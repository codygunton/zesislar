"""Build a conservative decoded CFG under explicit allocator and dispatch inputs."""
import argparse
from collections import deque
import json
from pathlib import Path

from elftools.elf.elffile import ELFFile

import manifest
from inventory import cfg_loops, INSN
from dwarf import inline_ranges
from riscv import decode_range, simple_transfers

ROOTS = ['rlp.decodeItem', 'rlp_decode.nextUint64', 'rlp_decode.decodeParentHeader',
         'rlp_decode.decodeTxFields', 'rlp_decode.txAccessList',
         'array_list.Aligned([32]u8,null).ensureTotalCapacity',
         'array_list.Aligned([32]u8,null).toOwnedSlice',
         'array_list.Aligned(input.AccessListEntry,null).toOwnedSlice',
         'alt_fl_alloc.alloc', 'alt_fl_alloc.remap', 'alt_fl_alloc.free', 'memcpy']
CALLER_SAVED = {1,5,6,7,10,11,12,13,14,15,16,17,28,29,30,31}


class Image:
    def __init__(self, elf):
        self.elf = elf
        self.symbols = {s.name: s for s in elf.get_section_by_name('.symtab').iter_symbols()}
        self.functions = {s.name: s for s in self.symbols.values()
                          if s['st_info']['type'] == 'STT_FUNC' and s['st_size']}
        self.sections = [(s, s.data()) for s in elf.iter_sections() if s['sh_type'] != 'SHT_NOBITS' and s['sh_flags'] & 2]

    def read(self, address, size):
        for section, data in self.sections:
            offset = address-section['sh_addr']
            if 0 <= offset and offset+size <= len(data): return data[offset:offset+size]
        raise ValueError(f'Unmapped ELF bytes: {address:#x}+{size}')

    def rows(self, name):
        symbol = self.functions[name]
        return simple_transfers(decode_range(symbol['st_value'], self.read(symbol['st_value'], symbol['st_size'])))


def plus(value, offset):
    if isinstance(value, int): return (value+offset) % (1 << 64)
    if isinstance(value, tuple): return (value[0], value[1]+offset)
    return None


def switch_targets(image, rows):
    """Check the complete mask/scale/base/load/jump sequence, then read five entries."""
    candidates = [i for i, r in enumerate(rows[:40]) if r['kind'] == 'indirect' and r['rd'] == 0]
    if len(candidates) != 1: raise ValueError('Expected one decodeTxFields dispatch')
    index = candidates[0]
    jump = rows[index]
    load_index = next(i for i in range(index-1, -1, -1) if rows[i]['rd'] == jump['rs1'] and rows[i]['kind'] != 'store')
    mask, upper, shift, lower, add, load = rows[load_index-5:load_index+1]
    if not (mask['mnemonic'] == 'andi' and mask['rs1'] == 12 and mask['imm'] == 255
            and upper['mnemonic'] == 'auipc'
            and shift['mnemonic'] == 'slli' and shift['imm'] == 3 and shift['rs1'] == mask['rd']
            and lower['mnemonic'] == 'addi' and lower['rs1'] == upper['rd']
            and add['mnemonic'] == 'add' and add['rs1'] == lower['rd'] and add['rs2'] == shift['rd']
            and load['mnemonic'] == 'ld' and load['rs1'] == add['rd'] and load['imm'] == 0
            and load['rd'] == jump['rs1'] and jump['imm'] == 0):
        raise ValueError('Unsupported dispatch instruction pattern')
    base = upper['pc']+upper['imm']+lower['imm']
    table = image.read(base, 5*8)
    targets = [int.from_bytes(table[i:i+8], 'little') for i in range(0, 40, 8)]
    boundaries = {row['pc'] for row in rows}
    if any(target not in boundaries for target in targets):
        raise ValueError('A dispatch target is not a function instruction boundary')
    return {'pc': jump['pc'], 'table_address': base, 'table_bytes': table.hex(),
            'index_register': 12, 'index_mask': 255, 'index_bounds': [0,4],
            'bound_status': 'Required entry condition. This scan does not prove the caller obligation.',
            'targets': targets, 'evidence_instructions': [row['pc'] for row in rows[load_index-5:index+1]]}


def initial_state(name):
    state = {0:0, 2:('stack',0)}
    if name in {'rlp_decode.decodeTxFields','rlp_decode.txAccessList',
                'array_list.Aligned([32]u8,null).ensureTotalCapacity'}:
        state[11] = ('allocator',0)
    elif '.toOwnedSlice' in name:
        state[12] = ('allocator',0)
    return state


def execute(row, before, image, vtable):
    state = dict(before)
    kind, op, rd, r1, r2, imm = row['kind'], row['mnemonic'], row['rd'], row['rs1'], row['rs2'], row['imm']
    left, right, value = state.get(r1), state.get(r2), None
    if kind == 'load':
        address = plus(left, imm)
        if address == ('allocator',8) and row['width'] == 8: value = vtable
        elif address == ('allocator',0) and row['width'] == 8: value = ('allocator_state',0)
        elif isinstance(address, tuple): value = state.get(('memory',address,row['width']))
        elif isinstance(address, int) and vtable <= address < vtable+32 and row['width'] == 8:
            value = int.from_bytes(image.read(address, 8), 'little')
    elif kind == 'store':
        address = plus(left,imm)
        if isinstance(address, tuple) and address[0] == 'stack':
            for key in list(state):
                if isinstance(key, tuple) and key[0] == 'memory' and key[1][0] == 'stack':
                    if max(address[1],key[1][1]) < min(address[1]+row['width'],key[1][1]+key[2]): state.pop(key)
            if right is not None: state[('memory',address,row['width'])] = right
    elif op == 'auipc': value = row['pc']+imm
    elif op == 'lui': value = imm % (1 << 64)
    elif op == 'addi': value = plus(left,imm)
    elif op in {'add','sub'}:
        if isinstance(right,int): value = plus(left, right if op == 'add' else -right)
        elif op == 'add' and isinstance(left,int): value = plus(right,left)
    elif isinstance(left,int):
        if op == 'slli': value = left << imm & ((1 << 64)-1)
        elif op == 'srli': value = left >> imm
        elif op == 'andi': value = left & imm
        elif op == 'ori': value = left | imm
    if kind not in {'store','branch'} and rd:
        state.pop(rd,None)
        if value is not None: state[rd] = value
    if kind == 'call' or kind == 'indirect' and rd:
        for register in CALLER_SAVED: state.pop(register,None)
    return state


def analyze(image, name):
    rows = image.rows(name)
    unsupported = [row for row in rows if row['kind'] == 'unsupported']
    if unsupported:
        return {'name':name,'unsupported':unsupported,'unresolved':[],'rows':rows}
    table = switch_targets(image,rows) if name == 'rlp_decode.decodeTxFields' else None
    vtable = image.symbols['alt_fl_alloc.vtable']['st_value']
    at = {r['pc']:r for r in rows}
    states = {rows[0]['pc']:initial_state(name)}
    queue = deque(states)
    while queue:
        pc = queue.popleft()
        row, before = at[pc], states[pc]
        kind = row['kind']
        target = row.get('target')
        if kind == 'indirect':
            value = plus(before.get(row['rs1']), row['imm'])
            target = value & ~1 if isinstance(value,int) else None
        edges = ([row['target'],pc+4] if kind == 'branch' else
                 [target] if kind == 'jump' or kind == 'indirect' and row['rd'] == 0 else
                 [] if kind == 'return' else [pc+row['size']])
        if table and pc == table['pc']: edges = table['targets']
        after = execute(row,before,image,vtable)
        for edge in edges:
            if edge not in at: continue
            merged = after if edge not in states else {k:v for k,v in states[edge].items() if after.get(k) == v}
            if edge not in states or merged != states[edge]:
                states[edge] = merged
                queue.append(edge)
    unresolved, calls = [], []
    for row in rows:
        pc, kind = row['pc'], row['kind']
        target = row.get('target')
        if kind == 'indirect' and (not table or pc != table['pc']):
            value = plus(states.get(pc,{}).get(row['rs1']),row['imm'])
            if isinstance(value,int):
                target = value & ~1
                row.update(target=target,kind='call' if row['rd'] else 'jump',resolution='selected allocator vtable under the stated entry condition')
                kind = row['kind']
            else:
                unresolved.append({'pc':pc,'register':row['rs1'],'reason':'No unique target in the conservative register analysis'})
        edges = ([row['target'],pc+4] if kind == 'branch' else
                 [target] if kind == 'jump' else [] if kind in {'return','indirect'} else [pc+row['size']])
        if table and pc == table['pc']:
            edges = table['targets']
            row['resolution'] = 'five checked table entries under the stated index bound'
        row['successors'] = [edge for edge in edges if edge is not None]
        if row['kind'] in {'load','store'}:
            address = plus(states.get(pc,{}).get(row['rs1']),row['imm'])
            row['address_analysis'] = address
        if kind == 'call' or kind == 'jump' and target not in at:
            calls.append({'pc':pc,'target':target,'kind':'tail' if kind == 'jump' else 'call'})
    starts = {rows[0]['pc']}
    for row in rows:
        if row['kind'] in {'branch','jump','call','return','indirect'}:
            starts.update(edge for edge in row['successors'] if edge in at)
            if row['pc']+row['size'] in at: starts.add(row['pc']+row['size'])
    ordered = sorted(starts)
    end = rows[-1]['pc']+rows[-1]['size']
    blocks = []
    for i,start in enumerate(ordered):
        stop = ordered[i+1] if i+1 < len(ordered) else end
        last = at[stop-4]
        blocks.append({'start':start,'end':stop,'successors':last['successors']})
    return {'name':name,'entry':rows[0]['pc'],'end':end,'rows':rows,'blocks':blocks,
            'instruction_count':len(rows),'block_count':len(blocks),
            'branch_count':sum(row['kind']=='branch' for row in rows),'call_count':len(calls),
            'calls':calls,'returns':[row['pc'] for row in rows if row['kind']=='return'],
            'loops':cfg_loops(rows),'loop_count':len(cfg_loops(rows)),
            'runtime_operations':[{'pc':r['pc'],'csr':r['csr']} for r in rows if r['kind']=='runtime'],
            'unresolved':unresolved,'unsupported':unsupported,'dispatch':table,
            'allocator_argument_register':next((key for key,value in initial_state(name).items() if value == ('allocator',0)),None)}


def region(name, function, starts):
    blocks = [b for b in function['blocks'] if b['start'] in starts]
    pcs = {pc for b in blocks for pc in range(b['start'],b['end'],4)}
    rows = [r for r in function['rows'] if r['pc'] in pcs]
    incoming = [{'from':r['pc'],'to':edge} for r in function['rows'] if r['pc'] not in pcs
                for edge in r['successors'] if edge in pcs]
    outgoing = [{'from':r['pc'],'to':edge} for r in rows for edge in r['successors'] if edge not in pcs]
    return {'name':name,'blocks':sorted(starts),'instruction_count':len(rows),'block_count':len(blocks),
            'branch_count':sum(r['kind']=='branch' for r in rows),
            'call_count':sum(c['pc'] in pcs for c in function['calls']),
            'loop_count':len(cfg_loops(rows)),'entry_edges':incoming,'exit_edges':outgoing,
            'returns':[r['pc'] for r in rows if r['kind']=='return'],
            'status':'Complete-block proposal. No Level 1 boundary approval or resource proof is implied.'}


def transaction_regions(function):
    blocks = {b['start']:b for b in function['blocks']}
    table = function['dispatch']
    reaches = []
    for target in table['targets']:
        seen, queue = set(), [target]
        while queue:
            node = queue.pop()
            if node not in blocks or node in seen: continue
            seen.add(node)
            queue.extend(blocks[node]['successors'])
        reaches.append(seen)
    shared = {node for node in blocks if sum(node in group for group in reaches)>1}
    arms = [region(f'type_{i}',function,group-shared) for i,group in enumerate(reaches)]
    tail = region('shared_tail',function,shared)
    dispatch = region('dispatch',function,set(blocks)-set().union(*reaches))
    return [dispatch,*arms,tail]


def inline_region(image, obj):
    instances, evidence = inline_ranges(obj,image.elf,['decodeSingleTx'])
    if len(instances['decodeSingleTx']) != 1:
        raise ValueError('Expected one emitted decodeSingleTx instance')
    ranges = instances['decodeSingleTx'][0]['ranges']
    owners = [s for s in image.functions.values()
              if all(s['st_value'] <= r['start'] < r['end'] <= s['st_value']+s['st_size'] for r in ranges)]
    if len(owners) != 1: raise ValueError('The inline decoder lacks one enclosing symbol')
    owner = analyze(image,owners[0].name)
    if owner['unsupported']: raise ValueError('Unsupported instruction in the enclosing function')
    boundaries = {r['pc'] for r in owner['rows']} | {owner['end']}
    if any(r['start'] not in boundaries or r['end'] not in boundaries for r in ranges):
        raise ValueError('An inline range splits an instruction')
    selected = {b['start'] for b in owner['blocks']
                if any(max(b['start'],r['start']) < min(b['end'],r['end']) for r in ranges)}
    result = region('decodeSingleTx',owner,selected)
    blocks = [b for b in owner['blocks'] if b['start'] in selected]
    pcs = {pc for b in blocks for pc in range(b['start'],b['end'],4)}
    result.update(parent_symbol=owners[0].name,dwarf=instances['decodeSingleTx'][0],
                  dwarf_relocation=evidence,block_ranges=blocks,
                  added_instruction_count=len(pcs)-sum((r['end']-r['start'])//4 for r in ranges),
                  calls=[c for c in owner['calls'] if c['pc'] in pcs],
                  unresolved=[r for r in owner['unresolved'] if r['pc'] in pcs])
    guards = []
    for i,row in enumerate(owner['rows']):
        if row['pc'] not in pcs or row['mnemonic'] != 'addi' or row['imm'] != -5: continue
        following = owner['rows'][i+1:i+5]
        if not following or following[0]['mnemonic'] != 'andi' or following[0]['imm'] != 255:
            continue
        mask = following[0]
        if mask['rs1'] != row['rd'] or mask['rd'] != row['rd']: continue
        for j,limit in enumerate(following):
            if limit['mnemonic'] != 'addi' or limit['rs1'] != 0 or limit['imm'] != 252: continue
            branch = following[j+1] if j+1 < len(following) else None
            if branch and branch['mnemonic'] == 'bltu' and branch['rs1'] == mask['rd'] and branch['rs2'] == limit['rd']:
                guards.append({'input_register':row['rs1'],'subtract_pc':row['pc'],'mask_pc':mask['pc'],
                    'branch_pc':branch['pc'],'reject_target':branch['target'],
                    'accepted_byte_values':[value for value in range(256) if not ((value-5)&255)<252],
                    'status':'Decoded guard arithmetic. A caller-contract proof must connect this register to the dispatch argument.'})
    result['type_guard_evidence'] = guards
    return result


def publish(out, recipe, record):
    """Publish one checked inventory and bind each derived output to the recipe."""
    functions = record['functions']
    identity = record['artifact_identity']
    files = {
        'inventory.json': (2,record),
        'cfg.json': (1,{'schema':1,'artifact_identity':identity,'functions':[
            {key:f[key] for key in ['name','entry','end','rows','blocks','calls','returns','loops']}
            for f in functions]}),
        'regions.json': (1,{'schema':1,'artifact_identity':identity,
            'transaction_regions':record['transaction_regions'],'inline_decodeSingleTx':record['inline_decodeSingleTx']}),
        'dump-ranges.json': (1,{'schema':1,'artifact_identity':identity,
            'functions':[{'name':f['name'],'start':f['entry'],'end':f['end']} for f in functions],
            'inline_decodeSingleTx':record['inline_decodeSingleTx']['block_ranges']}),
        'verification.json': (2,{'schema':2,'artifact_identity':identity,
            'static_closure':'passed under the inventory conditions',
            'unsupported_instructions':[],'unresolved_transfers':[],'missing_callees':[],
            'expected_unmodeled_operations':[{'function':f['name'],**r} for f in functions for r in f['runtime_operations']],
            'trace_generation':'blocked: the exact target platform model needs review',
            'entry_block_smoke':'not run','return_site_chain':'not run','proof_status':'not proved'})}
    for name,(_,payload) in files.items():
        (out/name).write_text(json.dumps(payload,indent=2)+'\n')
    decoder = next(f for f in functions if f['name']=='rlp.decodeItem')
    # The raw dump intentionally has no selected Isla configuration.
    # A reviewed platform must supply the configuration and access constraints.
    lines = ['// Raw selected-ELF bytes. Trace generation requires a reviewed platform.',
             '// Artifact identity: '+identity]
    assembly = {}
    for line in (out/'disassembly.objdump').read_text().splitlines():
        match = INSN.match(line)
        if match: assembly[int(match[1],16)] = (int(match[2],16),line)
    for row in decoder['rows']:
        word,line = assembly[row['pc']]
        if word != row['word']: raise ValueError('The raw dump differs from the selected ELF')
        lines.append(line)
    (out/'decodeItem.raw.dump').write_text('\n'.join(lines)+'\n')
    files['decodeItem.raw.dump'] = (1,None)
    lines = ['# Selected stock decoder inventory','',record['claim'],'',
        '| Function or proposed region | Instructions | Blocks | Branches | Loops | Calls |',
        '|---|---:|---:|---:|---:|---:|']
    for f in [*functions,*record['transaction_regions'],record['inline_decodeSingleTx']]:
        counts = [str(f[key]) for key in ['instruction_count','block_count','branch_count','loop_count','call_count']]
        lines.append('| '+f['name']+' | '+' | '.join(counts)+' |')
    lines += ['', 'Branches count conditional branches. Loops count cyclic strongly connected components.',
        'Calls include direct calls, resolved allocator calls, and external tail transfers.',
        'Blocks end at calls and control transfers. Region proposals contain complete blocks.',
        'The five dispatch entries come from table bytes after a checked mask and scale sequence.',
        'The dispatch index requires the entry bound 0 through 4.',
        'The inline caller contains two decoded guards that accept byte values 1 through 4.',
        'Caller proofs must connect those guards and the legacy zero argument to the dispatch contract.',
        'The allocator calls use the selected vtable under the recorded entry condition.',
        'The inventory reads allocator targets from the actual vtable bytes.',
        'The scan found no missing callee and no unresolved transfer inside the selected regions.',
        'The only expected unmodeled operation is memcpy CSR 0x813.',
        'The ELF symbol gives memcpy three instructions. Its following padding instruction lies outside that symbol.',
        'The decodeSingleTx proposal adds five instructions to obtain complete blocks around its DWARF ranges.',
        'The region proposals do not establish approved Level 1 boundaries.',
        'Trace generation waits for the exact platform model. The entry smoke and return chains did not run.', '']
    (out/'INVENTORY.md').write_text('\n'.join(lines))
    files['INVENTORY.md'] = (1,None)
    for name,(version,_) in files.items():
        recipe.setdefault('derived',{})[name] = {'artifact_identity':identity,'schema_version':version}
    recipe['invalidated_derived'] = [name for name in recipe.get('invalidated_derived',[]) if name not in files]
    recipe.pop('historical_reports',None)
    recipe['historical_comparison'] = 'comparison-generic-script/ remains historical pilot evidence from c9165ca4.'
    manifest.refresh(out,recipe)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--elf', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--object', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--publish', action='store_true')
    args = parser.parse_args()
    with args.elf.open('rb') as stream:
        image = Image(ELFFile(stream))
        results = [analyze(image,name) for name in ROOTS]
        if any(r['unsupported'] for r in results):
            args.out.write_text(json.dumps({'schema':2,'status':'refused unsupported instructions','functions':results},indent=2)+'\n')
            for result in results:
                for instruction in result['unsupported']:
                    print(f"UNSUPPORTED {result['name']} {instruction['pc']:#x}: {instruction['extension']}")
            raise SystemExit(1)
        known = {r.get('entry') for r in results}
        missing = [{'caller':r['name'],**call} for r in results for call in r.get('calls',[]) if call['target'] not in known]
        with args.object.open('rb') as source:
            inline = inline_region(image,ELFFile(source))
        missing += [{'caller':'decodeSingleTx',**c} for c in inline['calls'] if c['target'] not in known]
        vtable = image.symbols['alt_fl_alloc.vtable']['st_value']
        fields = [int.from_bytes(image.read(vtable+i,8),'little') for i in range(0,32,8)]
        record = {'elf_sha256':manifest.digest(args.elf),'schema':2,'functions':results,
            'inline_decodeSingleTx':inline,'missing_callees':missing,
            'transaction_regions':transaction_regions(next(r for r in results if r['name']=='rlp_decode.decodeTxFields')),
            'allocator_vtable':{'address':vtable,'state_address':image.symbols['alt_fl_alloc.state']['st_value'],
                'free_lists_address':image.symbols['alt_fl_alloc.free_lists']['st_value'],'bytes':image.read(vtable,32).hex(),
                'slots':dict(zip(['alloc','resize','remap','free'],fields))},
            'conditions':['The allocator argument points to a two-word allocator containing the selected state and vtable.',
                'Calls preserve caller spills and callee-saved registers under their eventual contracts.',
                'The decodeTxFields index is between 0 and 4. Caller resource and bound proofs remain separate.'],
            'claim':'Conditional static inventory. This report is not a machine-code proof.'}
        if args.manifest:
            recipe = json.loads(args.manifest.read_text())
            manifest.require_equal(record['elf_sha256'],recipe['elf_sha256'],'Selected ELF')
            manifest.require_equal(manifest.digest(args.object),recipe['stock_object_sha256'],'Selected object')
            record['artifact_identity'] = recipe['artifact_identity']
    args.out.write_text(json.dumps(record,indent=2)+'\n')
    for result in results:
        print(result['name'],result.get('instruction_count'), 'unresolved',result['unresolved'], 'unsupported',len(result['unsupported']))
    print('decodeSingleTx',inline['instruction_count'],'instructions',inline['block_count'],'complete blocks',len(inline['unresolved']),'unresolved')
    if missing or inline['unresolved'] or any(r['unresolved'] or r['unsupported'] for r in results): raise SystemExit(1)
    if args.publish:
        if not args.manifest or args.manifest.resolve().parent != args.out.resolve().parent:
            parser.error('--publish requires the manifest and output in the same directory')
        publish(args.out.parent,recipe,record)


if __name__ == '__main__': main()
