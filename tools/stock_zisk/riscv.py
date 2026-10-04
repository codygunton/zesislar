"""Decode RV64IM transfer fields from bytes, independently of objdump comments."""


def signed(value, bits):
    return value-(1 << bits) if value & (1 << (bits-1)) else value


def decode(pc, data):
    half = int.from_bytes(data[:2], 'little')
    if half & 3 != 3:
        return {'pc': pc, 'size': 2, 'word': half, 'kind': 'unsupported', 'extension': 'RVC'}
    if len(data) < 4 or half & 0x1f == 0x1f:
        raise ValueError(f'Unsupported instruction length at {pc:#x}')
    word = int.from_bytes(data[:4], 'little')
    op, rd, f3, r1, r2, f7 = word & 127, word >> 7 & 31, word >> 12 & 7, word >> 15 & 31, word >> 20 & 31, word >> 25
    row = {'pc': pc, 'size': 4, 'word': word, 'rd': rd, 'rs1': r1, 'rs2': r2,
           'funct3': f3, 'kind': 'plain', 'mnemonic': '', 'imm': signed(word >> 20, 12)}
    if op in {0x17, 0x37}:
        row.update(mnemonic='auipc' if op == 0x17 else 'lui', imm=signed(word & 0xfffff000, 32))
    elif op == 0x6f:
        imm = ((word >> 31) << 20 | (word >> 12 & 255) << 12 |
               (word >> 20 & 1) << 11 | (word >> 21 & 1023) << 1)
        row.update(kind='call' if rd else 'jump', mnemonic='jal', target=pc+signed(imm, 21))
    elif op == 0x67 and f3 == 0:
        row.update(kind='return' if rd == 0 and r1 == 1 and row['imm'] == 0 else 'indirect', mnemonic='jalr')
    elif op == 0x63 and f3 in {0, 1, 4, 5, 6, 7}:
        imm = ((word >> 31) << 12 | (word >> 7 & 1) << 11 |
               (word >> 25 & 63) << 5 | (word >> 8 & 15) << 1)
        row.update(kind='branch', mnemonic={0:'beq', 1:'bne', 4:'blt', 5:'bge', 6:'bltu', 7:'bgeu'}[f3],
                   target=pc+signed(imm, 13))
    elif op == 3 and f3 < 7:
        row.update(kind='load', mnemonic=['lb','lh','lw','ld','lbu','lhu','lwu'][f3], width=1 << (f3 & 3))
    elif op == 0x23 and f3 < 4:
        row.update(kind='store', mnemonic=['sb','sh','sw','sd'][f3], width=1 << f3,
                   imm=signed((word >> 25) << 5 | (word >> 7 & 31), 12))
    elif op == 0x13:
        if f3 not in {1, 5}:
            row['mnemonic'] = {0:'addi',2:'slti',3:'sltiu',4:'xori',6:'ori',7:'andi'}[f3]
        elif f3 == 1 and word >> 26 == 0:
            row.update(mnemonic='slli', imm=word >> 20 & 63)
        elif f3 == 5 and word >> 26 in {0, 16}:
            row.update(mnemonic='srli' if word >> 26 == 0 else 'srai', imm=word >> 20 & 63)
    elif op == 0x1b:
        if f3 == 0: row['mnemonic'] = 'addiw'
        elif f3 == 1 and f7 == 0: row.update(mnemonic='slliw', imm=r2)
        elif f3 == 5 and f7 in {0, 32}: row.update(mnemonic='srliw' if f7 == 0 else 'sraiw', imm=r2)
    elif op in {0x33, 0x3b}:
        suffix = 'w' if op == 0x3b else ''
        if f7 == 0 and (op == 0x33 or f3 in {0,1,5}):
            row['mnemonic'] = ['add','sll','slt','sltu','xor','srl','or','and'][f3]+suffix
        elif f7 == 32 and f3 in {0,5}:
            row['mnemonic'] = ('sub' if f3 == 0 else 'sra')+suffix
        elif f7 == 1 and (op == 0x33 or f3 in {0,4,5,6,7}):
            row['mnemonic'] = ['mul','mulh','mulhsu','mulhu','div','divu','rem','remu'][f3]+suffix
    elif op == 0x0f and f3 == 0 and rd == 0 and r1 == 0:
        row['mnemonic'] = 'fence'
    elif op == 0x73 and word == 0x8135a073:
        row.update(mnemonic='csrrs', kind='runtime', csr=0x813)
    if not row['mnemonic']:
        extension = ('A' if op == 0x2f else 'FP' if op in {7,0x27,0x43,0x47,0x4b,0x4f,0x53}
                     else 'ecall' if word == 0x73 else 'CSR/system' if op == 0x73
                     else 'Zb-or-other-extension')
        row.update(kind='unsupported', extension=extension)
    return row


def decode_range(start, data):
    rows, offset = [], 0
    while offset < len(data):
        row = decode(start+offset, data[offset:offset+4])
        rows.append(row)
        offset += row['size']
    if offset != len(data):
        raise ValueError(f'Truncated range at {start+offset:#x}')
    return rows


def simple_transfers(rows):
    """Resolve PC-relative pairs. Refuse guesses about register-loaded targets."""
    constants = {0: 0}
    boundaries = {row['target'] for row in rows if row['kind'] in {'branch','jump'}}
    for row in rows:
        pc, kind = row['pc'], row['kind']
        if pc in boundaries: constants = {0: 0}
        if kind == 'unsupported': continue
        rd, r1, imm, op = row['rd'], row['rs1'], row['imm'], row['mnemonic']
        value = None
        if op == 'auipc': value = pc+imm
        elif op == 'lui': value = imm
        elif op == 'addi' and r1 in constants: value = constants[r1]+imm
        elif kind == 'indirect' and r1 in constants:
            row.update(target=(constants[r1]+imm) & ~1, kind='call' if rd else 'jump')
        if kind not in {'store','branch'} and rd:
            constants.pop(rd, None)
            if value is not None: constants[rd] = value
        if row['kind'] in {'branch','jump','call','return','indirect'}:
            constants = {0: 0}
    return rows
