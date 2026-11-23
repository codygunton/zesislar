#!/usr/bin/env python3
"""Build the hint pack of one function from the pre-link object's DWARF.

Hints are untrusted. A hint never enters a statement unchecked.

`build` writes `<run dir>/hints/`:
  SOURCE.md       numbered source of the function and of each function inlined into it
  TYPES.json      structure, union and enumeration layouts reachable from its variables
  LOCATIONS.json  pc range -> variable -> register, frame slot or value; line and inline tables
  BLOCKS.md       per CFG block: disassembly, source lines, inline stack, live-in registers,
                  variables in scope
`slice --pcs ...` cuts the part of a hint pack that concerns some pcs.
`counts` prints the DWARF sanity counts of the object.

The linked ELF has only a symbol table, so DWARF comes from the object named by
`inputs.object` of the build recipe, read with `relocate_dwarf_sections=False` and
relocated by `code_dwarf` (tools/stock_zisk/dwarf.py). Markdown files name pcs only as
offsets from the function's symbol (`+0xOFFSET`) or as `SYMBOL+0xOFFSET`; the JSON files
also carry the absolute address of each pc (generated data).
"""
import argparse
import bisect
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(REPO / 'tools' / 'stock_zisk'))
from inventory import die_attribute, die_ranges, function_body  # noqa: E402

RECIPE = Path('build/stock-zisk/build-recipe.json')
ELF = Path('build/stock-zisk/zesu-zisk.elf')
CFG = Path('build/stock-zisk/cfg.json')
ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1',
       'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
       's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
ARGS = list(range(10, 18))
CALLER_SAVED = [1, 5, 6, 7, *ARGS, 28, 29, 30, 31]
CALLEE_SAVED = [2, 8, 9, *range(18, 28)]
ZESU_MARK = '/p0c-zesu-source/'
STD_MARK = '/std/'
ARRAY_LIST = 'std/array_list.zig'
VAR_TAGS = {'DW_TAG_formal_parameter', 'DW_TAG_variable'}
AGGREGATES = {'DW_TAG_structure_type', 'DW_TAG_union_type', 'DW_TAG_enumeration_type'}


# ---------------------------------------------------------------- paths and inputs

def shared_root():
    """The main checkout: `_build/` is shared by every worktree."""
    try:
        common = subprocess.check_output(
            ['git', '-C', str(REPO), 'rev-parse', '--path-format=absolute', '--git-common-dir'],
            text=True, stderr=subprocess.DEVNULL).strip()
        return Path(common).parent
    except (OSError, subprocess.CalledProcessError):
        return REPO


def resolve(path):
    """Resolve a repository-relative path in this worktree, then in the main checkout."""
    path = Path(path)
    if path.is_absolute():
        return path
    for root in (REPO, shared_root()):
        if (root / path).exists():
            return root / path
    return shared_root() / path


def sha256(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b''):
            digest.update(chunk)
    return digest.hexdigest()


def source_key(path):
    """Host-independent key: `src/...` for zesu, `std/...` for the Zig library."""
    if ZESU_MARK in path:
        return path.split(ZESU_MARK, 1)[1]
    if STD_MARK in path:
        return 'std/' + path.rsplit(STD_MARK, 1)[1]
    return path


class Sources:
    """Source text by key; records which commit and which library files were read."""

    def __init__(self, zesu_dir, zig_lib=None):
        self.zesu_dir, self.zig_lib = Path(zesu_dir), Path(zig_lib) if zig_lib else None
        self.cache, self.record = {}, {}

    def path(self, key):
        if key.startswith('src/'):
            return self.zesu_dir / key
        if key.startswith('std/') and self.zig_lib:
            for candidate in (self.zig_lib / 'lib' / key, self.zig_lib / key):
                if candidate.exists():
                    return candidate
        return None

    def lines(self, key):
        if key not in self.cache:
            path = self.path(key)
            if path is None or not path.exists():
                self.cache[key] = None
                self.record[key] = {'available': False}
            else:
                text = path.read_text(errors='replace')
                self.cache[key] = text
                self.record[key] = {'available': True, 'sha256': sha256(path)}
        text = self.cache[key]
        return None if text is None else text.split('\n')

    def text(self, key):
        self.lines(key)
        return self.cache[key]

    def zig_lib_record(self):
        if not self.zig_lib:
            return None
        path = self.path(ARRAY_LIST)
        return {'array_list': 'lib/' + ARRAY_LIST,
                'sha256': sha256(path) if path else None}


def check_source_commit(zesu_dir, recipe):
    expected = recipe['sources']['zesu']['commit']
    actual = subprocess.check_output(['git', '-C', str(zesu_dir), 'rev-parse', 'HEAD'],
                                     text=True).strip()
    if actual != expected:
        raise SystemExit(f'zesu source at {actual}, recipe names {expected}')
    dirty = subprocess.check_output(['git', '-C', str(zesu_dir), 'status', '--porcelain',
                                     '--untracked-files=no'], text=True).strip()
    if dirty:
        raise SystemExit('zesu source checkout has tracked changes')
    return actual


# ---------------------------------------------------------------- ELF and DWARF

def open_elf(path):
    from elftools.elf.elffile import ELFFile
    return ELFFile(open(path, 'rb'))


def load_dwarf(object_path, elf_path):
    from dwarf import code_dwarf
    obj, final = open_elf(object_path), open_elf(elf_path)
    dwarf, evidence = code_dwarf(obj, final)
    return dwarf, evidence, final


class Symbols:
    def __init__(self, elf):
        rows = sorted((s['st_value'], s['st_size'], s.name)
                      for s in elf.get_section_by_name('.symtab').iter_symbols()
                      if s['st_info']['type'] == 'STT_FUNC' and s['st_size'])
        self.starts = [row[0] for row in rows]
        self.rows = rows
        self.by_name = {name: (start, size) for start, size, name in rows}

    def name(self, address):
        index = bisect.bisect_right(self.starts, address) - 1
        if index >= 0:
            start, size, name = self.rows[index]
            if address < start + size:
                return name if address == start else f'{name}+{address - start:#x}'
        return None


def counts(dwarf):
    """Sanity counts: structure types, members, DIEs with DW_AT_location."""
    result = defaultdict(int)
    for unit in dwarf.iter_CUs():
        for die in unit.iter_DIEs():
            if die.tag == 'DW_TAG_structure_type':
                result['structure_types'] += 1
            elif die.tag == 'DW_TAG_member':
                result['members'] += 1
            if 'DW_AT_location' in die.attributes:
                result['location_entries'] += 1
    return dict(result)


def text_attr(die, key):
    attribute = die_attribute(die, key)
    if attribute is None:
        return None
    value = attribute.value
    return value.decode(errors='replace') if isinstance(value, bytes) else value


def die_name(die):
    name = text_attr(die, 'DW_AT_name')
    return name.split('__anon_')[0] if name else None


def qualified_name(die):
    return text_attr(die, 'DW_AT_linkage_name') or die_name(die)


def cu_file(dwarf, cu, index):
    program = dwarf.line_program_for_CU(cu)
    if program is None or not index:
        return ''
    header = program.header
    version = header['version']
    entry = header.file_entry[index if version >= 5 else index - 1]
    if entry.dir_index or version >= 5:
        directory = header.include_directory[entry.dir_index if version >= 5 else entry.dir_index - 1]
    else:
        directory = cu.get_top_DIE().attributes['DW_AT_comp_dir'].value
    return str(Path(directory.decode(errors='replace')) / entry.name.decode(errors='replace'))


def type_die(die):
    """The DIE named by DW_AT_type, following abstract origins."""
    while 'DW_AT_type' not in die.attributes:
        for reference in ('DW_AT_abstract_origin', 'DW_AT_specification'):
            if reference in die.attributes:
                die = die.get_DIE_from_attribute(reference)
                break
        else:
            return None
    return die.get_DIE_from_attribute('DW_AT_type')


def array_dims(die):
    dims = []
    for child in die.iter_children():
        if child.tag != 'DW_TAG_subrange_type':
            continue
        if 'DW_AT_count' in child.attributes:
            dims.append(child.attributes['DW_AT_count'].value)
        elif 'DW_AT_upper_bound' in child.attributes:
            dims.append(child.attributes['DW_AT_upper_bound'].value + 1)
        else:
            dims.append(None)
    return dims


def type_name(die):
    if die is None:
        return 'void'
    tag = die.tag
    if tag == 'DW_TAG_pointer_type':
        return '*' + type_name(type_die(die))
    if tag in ('DW_TAG_const_type', 'DW_TAG_volatile_type'):
        return type_name(type_die(die))
    if tag == 'DW_TAG_array_type':
        prefix = ''.join(f'[{n if n is not None else "?"}]' for n in array_dims(die))
        return prefix + type_name(type_die(die))
    if tag == 'DW_TAG_subroutine_type':
        return 'fn'
    name = text_attr(die, 'DW_AT_name')
    if name:
        return name
    return f'<anonymous {tag[7:].replace("_type", "")} {die.offset:#x}>'


def type_size(die):
    while die is not None:
        if 'DW_AT_byte_size' in die.attributes:
            return die.attributes['DW_AT_byte_size'].value
        if die.tag == 'DW_TAG_pointer_type':
            return die.cu.header['address_size']
        if die.tag == 'DW_TAG_array_type':
            dims, element = array_dims(die), type_size(type_die(die))
            total = element
            for dim in dims:
                total = None if total is None or dim is None else total * dim
            return total
        if die.tag not in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type'):
            return None
        die = type_die(die)
    return None


def collect_types(roots, pointer_depth):
    """Aggregates reachable from `roots`; at most `pointer_depth` pointer hops."""
    types, seen, work = {}, set(), [(die, 0) for die in roots if die is not None]
    while work:
        die, hops = work.pop()
        if die is None or (die.offset, hops) in seen:
            continue
        seen.add((die.offset, hops))
        tag = die.tag
        if tag == 'DW_TAG_pointer_type':
            if hops < pointer_depth:
                work.append((type_die(die), hops + 1))
            continue
        if tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type',
                   'DW_TAG_array_type'):
            work.append((type_die(die), hops))
            continue
        if tag not in AGGREGATES:
            continue
        name = type_name(die)
        if name in types:
            continue
        entry = {'kind': tag[7:-5], 'byte_size': type_size(die)}
        if tag == 'DW_TAG_enumeration_type':
            entry['values'] = {text_attr(child, 'DW_AT_name'): child.attributes['DW_AT_const_value'].value
                               for child in die.iter_children()
                               if child.tag == 'DW_TAG_enumerator'
                               and 'DW_AT_const_value' in child.attributes}
        else:
            members = []
            for child in die.iter_children():
                if child.tag != 'DW_TAG_member':
                    continue
                member_type = type_die(child)
                location = child.attributes.get('DW_AT_data_member_location')
                members.append({'name': text_attr(child, 'DW_AT_name'),
                                'offset': location.value if location is not None
                                and isinstance(location.value, int) else 0 if tag == 'DW_TAG_union_type' else None,
                                'size': type_size(member_type), 'type': type_name(member_type)})
                work.append((member_type, hops))
            entry['members'] = members
        types[name] = entry
    return dict(sorted(types.items()))


# ---------------------------------------------------------------- locations

def reg_name(number):
    return ABI[number] if number < 32 else f'f{number - 32}' if number < 64 else f'r{number}'


def signed_hex(value):
    return f'-{-value:#x}' if value < 0 else f'+{value:#x}'


def op_text(op):
    return ' '.join([op.op_name[6:], *(str(arg) for arg in op.args)])


def simple_location(ops, frame_base):
    if not ops:
        return {'kind': 'optimized_out'}
    names = [op.op_name for op in ops]
    stack_value = names[-1] == 'DW_OP_stack_value'
    body = ops[:-1] if stack_value else ops
    if len(body) == 1:
        op = body[0]
        name = op.op_name
        base = offset = None
        if re.fullmatch(r'DW_OP_breg\d+', name):
            base, offset = reg_name(int(name[10:])), op.args[0]
        elif name == 'DW_OP_bregx':
            base, offset = reg_name(op.args[0]), op.args[1]
        elif name == 'DW_OP_fbreg' and frame_base:
            base, offset = frame_base, op.args[0]
        if base is not None:
            text = f'{base}{signed_hex(offset)}'
            if stack_value:
                return {'kind': 'value', 'text': text}
            return {'kind': 'frame' if base in ('sp', 's0') else 'memory',
                    'base': base, 'offset': offset, 'text': f'[{text}]'}
        if not stack_value and re.fullmatch(r'DW_OP_reg\d+', name):
            return {'kind': 'register', 'register': reg_name(int(name[9:]))}
        if not stack_value and name == 'DW_OP_regx':
            return {'kind': 'register', 'register': reg_name(op.args[0])}
        if stack_value and re.fullmatch(r'DW_OP_lit\d+', name):
            return {'kind': 'constant', 'value': int(name[9:])}
        if stack_value and re.fullmatch(r'DW_OP_const\w+', name):
            return {'kind': 'constant', 'value': op.args[0]}
    return {'kind': 'expr', 'text': '; '.join(op_text(op) for op in ops)}


def decode_location(ops, frame_base):
    pieces, current = [], []
    for op in ops:
        if op.op_name == 'DW_OP_piece':
            pieces.append((op.args[0], current))
            current = []
        else:
            current.append(op)
    if not pieces:
        return simple_location(current, frame_base)
    if current:
        pieces.append((None, current))
    return {'kind': 'pieces',
            'pieces': [{'size': size, **simple_location(part, frame_base)} for size, part in pieces]}


def location_text(location):
    kind = location['kind']
    if kind == 'register':
        return location['register']
    if kind in ('frame', 'memory', 'value', 'expr'):
        return location['text']
    if kind == 'constant':
        return f'= {location["value"]}'
    if kind == 'pieces':
        return '{' + ', '.join(f'{piece["size"]}B: {location_text(piece)}' for piece in location['pieces']) + '}'
    return kind


# ---------------------------------------------------------------- scopes

def clip(ranges, lo, hi):
    return [(max(a, lo), min(b, hi)) for a, b in ranges if a < hi and b > lo]


class Function:
    """DWARF facts about one linked function."""

    def __init__(self, dwarf, symbol, entry, end):
        from elftools.dwarf.dwarf_expr import DWARFExprParser
        self.dwarf, self.symbol, self.entry, self.end = dwarf, symbol, entry, end
        self.parser = DWARFExprParser(dwarf.structs)
        self.loclists = dwarf.location_lists()
        self.variables, self.inlines, self.unlocated, self.type_roots = [], [], [], []
        self.die = self.find()
        if self.die is None:
            raise SystemExit(f'No DWARF subprogram starts at {symbol}')
        fb = self.die.attributes.get('DW_AT_frame_base')
        self.frame_base = None
        if fb is not None and fb.form == 'DW_FORM_exprloc':
            location = decode_location(self.parser.parse_expr(fb.value), None)
            self.frame_base = location.get('register')
        self.root = {'name': qualified_name(self.die), 'source': self.source_of(self.die),
                     'line': text_attr(self.die, 'DW_AT_decl_line')}
        self.walk(self.die, [], [(entry, end)])
        self.lines = self.line_table()

    def find(self):
        for unit in self.dwarf.iter_CUs():
            for die in unit.iter_DIEs():
                if die.tag == 'DW_TAG_subprogram' and 'DW_AT_low_pc' in die.attributes \
                        and any(start == self.entry for start, _ in die_ranges(self.dwarf, die)):
                    return die
        return None

    def source_of(self, die):
        attribute = die_attribute(die, 'DW_AT_decl_file')
        if attribute is None:
            return None
        holder = die
        while 'DW_AT_decl_file' not in holder.attributes:
            holder = holder.get_DIE_from_attribute(
                'DW_AT_abstract_origin' if 'DW_AT_abstract_origin' in holder.attributes
                else 'DW_AT_specification')
        return source_key(cu_file(self.dwarf, holder.cu, attribute.value))

    def walk(self, die, scope, ranges):
        for child in die.iter_children():
            tag = child.tag
            if tag in VAR_TAGS:
                self.variable(child, scope, ranges)
            elif tag == 'DW_TAG_inlined_subroutine':
                inner = clip(die_ranges(self.dwarf, child), self.entry, self.end)
                if not inner:
                    continue
                call_file = child.attributes.get('DW_AT_call_file')
                call_line = child.attributes.get('DW_AT_call_line')
                frame = {'name': qualified_name(child), 'source': self.source_of(child),
                         'line': text_attr(child, 'DW_AT_decl_line'),
                         'call': (f'{source_key(cu_file(self.dwarf, child.cu, call_file.value))}:'
                                  f'{call_line.value if call_line else "?"}') if call_file else None}
                self.inlines.append({**frame, 'depth': len(scope) + 1,
                                     'scope': [f['name'] for f in scope] + [frame['name']],
                                     'ranges': inner})
                self.walk(child, scope + [frame], inner)
            elif tag == 'DW_TAG_lexical_block':
                inner = clip(die_ranges(self.dwarf, child), self.entry, self.end) or ranges
                self.walk(child, scope, inner)

    def variable(self, die, scope, ranges):
        name = die_name(die) or '<anonymous>'
        kind = 'param' if die.tag == 'DW_TAG_formal_parameter' else 'var'
        tdie = type_die(die)
        self.type_roots.append(tdie)
        row = {'name': name, 'kind': kind,
               'scope': [self.root['name']] + [frame['name'] for frame in scope],
               'type': type_name(tdie), 'size': type_size(tdie),
               'decl': f'{self.source_of(die)}:{text_attr(die, "DW_AT_decl_line")}'}
        attribute = die.attributes.get('DW_AT_location')
        pieces = []
        if attribute is None:
            pass
        elif attribute.form == 'DW_FORM_exprloc':
            location = decode_location(self.parser.parse_expr(attribute.value), self.frame_base)
            pieces = [(lo, hi, location) for lo, hi in ranges]
        else:
            base = die.cu.get_top_DIE().attributes.get('DW_AT_low_pc')
            base = base.value if base else 0
            for entry in self.loclists.get_location_list_at_offset(attribute.value, die):
                if hasattr(entry, 'base_address'):
                    base = entry.base_address
                    continue
                offset = 0 if entry.is_absolute else base
                location = decode_location(self.parser.parse_expr(entry.loc_expr), self.frame_base)
                for lo, hi in clip([(offset + entry.begin_offset, offset + entry.end_offset)],
                                   self.entry, self.end):
                    pieces.append((lo, hi, location))
        if not pieces:
            self.unlocated.append({key: row[key] for key in ('name', 'kind', 'scope', 'type')})
            return
        row['ranges'] = [{'start': self.rel(lo), 'end': self.rel(hi),
                          'start_address': lo, 'end_address': hi, 'location': location}
                         for lo, hi, location in sorted(pieces, key=lambda p: p[:2])]
        self.variables.append(row)

    def rel(self, pc):
        return f'+{pc - self.entry:#x}'

    def line_table(self):
        """Sorted (lo, hi, file key, line) rows that overlap the function."""
        rows = []
        for unit in self.dwarf.iter_CUs():
            program = self.dwarf.line_program_for_CU(unit)
            if program is None:
                continue
            previous = None
            for entry in program.get_entries():
                state = entry.state
                if state is None:
                    continue
                if previous is not None and previous.address < state.address:
                    lo, hi = max(previous.address, self.entry), min(state.address, self.end)
                    if lo < hi:
                        rows.append((lo, hi, previous.file, previous.line))
                previous = None if state.end_sequence else state
            files = {}
            resolved = []
            for lo, hi, index, line in rows:
                if index not in files:
                    files[index] = source_key(cu_file(self.dwarf, unit, index))
                resolved.append((lo, hi, files[index], line))
            rows = resolved
        rows.sort()
        return rows

    def line_at(self, pc):
        index = bisect.bisect_right(self.lines, (pc, float('inf'))) - 1
        if index >= 0:
            lo, hi, key, line = self.lines[index]
            if lo <= pc < hi:
                return key, line
        return None

    def inline_stack(self, pc):
        frames = [frame for frame in self.inlines
                  if any(lo <= pc < hi for lo, hi in frame['ranges'])]
        return [frame['name'] for frame in sorted(frames, key=lambda f: f['depth'])]

    def in_scope(self, pc):
        result = []
        for variable in self.variables:
            for piece in variable['ranges']:
                if piece['start_address'] <= pc < piece['end_address']:
                    result.append((variable, piece['location']))
                    break
        return result


# ---------------------------------------------------------------- machine code

def code_bytes(elf, start, end):
    for section in elf.iter_sections():
        base = section['sh_addr']
        if section['sh_flags'] & 4 and base <= start and end <= base + section['sh_size']:
            return section.data()[start - base:end - base]
    raise SystemExit(f'No code section holds {start:#x}..{end:#x}')


def disassemble(data, start):
    import capstone
    engine = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    return {ins.address: (ins.mnemonic, ins.op_str) for ins in engine.disasm(data, start)}


def uses_defs(row, call):
    """Registers read and written by one decoded row; ABI-conservative at calls and returns."""
    word = row['word']
    op = word & 127
    rd, rs1, rs2 = row['rd'], row['rs1'], row['rs2']
    uses, defs = set(), set()
    if op in (0x37, 0x17, 0x6f):
        defs = {rd}
    elif op in (0x13, 0x1b, 0x03, 0x67, 0x73):
        uses, defs = {rs1}, {rd}
    elif op in (0x23, 0x63):
        uses = {rs1, rs2}
    elif op in (0x33, 0x3b):
        uses, defs = {rs1, rs2}, {rd}
    if call:
        uses |= set(ARGS)
        defs |= set(CALLER_SAVED)
    if row['kind'] == 'return':
        uses |= {10, 11, *CALLEE_SAVED}
    uses.discard(0)
    defs.discard(0)
    return uses, defs


def liveness(function_row):
    """Live-in registers per block. Unknown successors keep every register live."""
    calls = {call['pc'] for call in function_row['calls']}
    rows = {row['pc']: row for row in function_row['rows']}
    blocks = {block['start']: block for block in function_row['blocks']}
    everything = set(range(1, 32))
    outside = set(ARGS) | set(CALLEE_SAVED) | {1}
    summary = {}
    for start, block in blocks.items():
        uses, defs = set(), set()
        pc = start
        while pc < block['end']:
            row = rows[pc]
            u, d = uses_defs(row, pc in calls)
            uses |= u - defs
            defs |= d
            pc += row['size']
        last = rows[block['end'] - 4]
        tail = everything if last['kind'] == 'indirect' and pc not in calls else set()
        summary[start] = (uses, defs, tail)
    live = {start: set() for start in blocks}
    changed = True
    while changed:
        changed = False
        for start in sorted(blocks, reverse=True):
            uses, defs, tail = summary[start]
            out = set(tail)
            for successor in blocks[start]['successors']:
                out |= live[successor] if successor in blocks else outside
            new = uses | (out - defs)
            if new != live[start]:
                live[start], changed = new, True
    return {start: sorted(regs) for start, regs in live.items()}


# ---------------------------------------------------------------- rendering

FN = r'\bfn\s+{name}\s*\('


def function_extent(text, name, decl_line):
    """First and last line of the function declared at `decl_line`."""
    if text is None or not name or not decl_line:
        return None
    offsets = [0]
    for line in text.split('\n'):
        offsets.append(offsets[-1] + len(line) + 1)
    if decl_line >= len(offsets):
        return None
    short = name.rsplit('.', 1)[-1]
    match = re.compile(FN.format(name=re.escape(short))).search(text, offsets[decl_line - 1])
    if match is None or match.start() >= offsets[min(decl_line + 2, len(offsets) - 1)]:
        return None
    try:
        body = function_body(text, match)
    except (IndexError, ValueError):
        return None
    end = text.index(body, match.start()) + len(body)
    return decl_line, text.count('\n', 0, end) + 1


def render_source(fn, sources, header):
    out = [f'# Source of `{fn.symbol}`', '', *header, '',
           'Lines marked `*` have code in this function per the DWARF line table.', '']
    code_lines = defaultdict(set)
    for lo, hi, key, line in fn.lines:
        if line:
            code_lines[key].add(line)
    units, seen = [], set()
    for frame in [fn.root, *sorted(fn.inlines, key=lambda f: (f['depth'], f['name']))]:
        key = (frame['name'], frame['source'], frame['line'])
        if key in seen:
            continue
        seen.add(key)
        units.append(frame)
    for frame in units:
        key, decl = frame['source'], frame['line']
        title = 'function' if frame is fn.root else 'inlined'
        lines = sources.lines(key) if key else None
        extent = function_extent(sources.text(key) if key else None, frame['name'], decl)
        out.append(f'## {title} `{frame["name"]}` — {key}:{decl}'
                   + (f'-{extent[1]}' if extent else ''))
        out.append('')
        if lines is None:
            used = sorted(code_lines.get(key, ()))
            out.append(f'Source text absent on this host. Lines with code: '
                       f'{", ".join(map(str, used)) or "none"}.')
            out.append('')
            continue
        first, last = extent if extent else (decl, decl)
        if not extent:
            out.append('Function extent not found; declaration line only.')
        out.append('```zig')
        width = len(str(last))
        for number in range(first, last + 1):
            mark = '*' if number in code_lines[key] else ' '
            out.append(f'{mark}{number:>{width}}  {lines[number - 1]}')
        out.append('```')
        out.append('')
    return '\n'.join(out)


def operand_text(row, op_str, fn, symbols, calls):
    target = row.get('target')
    if row['pc'] in calls:
        callee = calls[row['pc']]
        note = symbols.name(callee) or 'unknown callee'
        return op_str, f'call {note}'
    if target is None:
        if row['kind'] == 'indirect' and row.get('successors'):
            where = ', '.join(fn.rel(s) if fn.entry <= s < fn.end else (symbols.name(s) or 'outside')
                              for s in row['successors'])
            return op_str, f'indirect jump; CFG targets: {where}'
        return op_str, None
    where = fn.rel(target) if fn.entry <= target < fn.end else (symbols.name(target) or 'outside')
    parts = op_str.rsplit(', ', 1)
    return (parts[0] + ', ' + where) if len(parts) == 2 else where, None


def render_blocks(fn, function_row, elf, symbols, sources, header):
    data = code_bytes(elf, fn.entry, fn.end)
    text = disassemble(data, fn.entry)
    rows = {row['pc']: row for row in function_row['rows']}
    calls = {call['pc']: call['target'] for call in function_row['calls']}
    live = liveness(function_row)
    out = [f'# Blocks of `{fn.symbol}`', '', *header, '',
           'Live-in registers come from a register dataflow over the CFG that treats every call',
           'as reading a0-a7 and writing the caller-saved registers. Variables come from DWARF',
           'locations at the block start. All of it is an untrusted hint.', '']
    for block in function_row['blocks']:
        start, end = block['start'], block['end']
        successors = ', '.join(fn.rel(s) if fn.entry <= s < fn.end else (symbols.name(s) or 'outside')
                               for s in block['successors']) or 'none'
        out.append(f'## block {fn.rel(start)}..{fn.rel(end)}')
        out.append('')
        out.append(f'- successors: {successors}')
        stack = [fn.root['name'], *fn.inline_stack(start)]
        out.append(f'- inline stack: {" > ".join(stack)}')
        out.append(f'- live-in: {" ".join(reg_name(r) for r in live[start]) or "none"}')
        scope = fn.in_scope(start)
        if scope:
            out.append('- variables:')
            for variable, location in scope:
                owner = variable['scope'][-1]
                out.append(f'  - `{variable["name"]}` ({variable["kind"]} of {owner}, '
                           f'{variable["type"]}): {location_text(location)}')
        else:
            out.append('- variables: none located')
        out.append('')
        out.append('```')
        last_source, last_stack = None, stack
        pc = start
        while pc < end:
            row = rows[pc]
            here = [fn.root['name'], *fn.inline_stack(pc)]
            if here != last_stack:
                out.append(f'        ; inline: {" > ".join(here)}')
                last_stack = here
            source = fn.line_at(pc)
            if source and source != last_source and source[1]:
                lines = sources.lines(source[0])
                snippet = lines[source[1] - 1].strip() if lines and source[1] <= len(lines) else ''
                out.append(f'        // {source[0]}:{source[1]}  {snippet}'.rstrip())
                last_source = source
            mnemonic, op_str = text.get(pc, (row.get('mnemonic') or '?', ''))
            operands, note = operand_text(row, op_str, fn, symbols, calls)
            line = f'{fn.rel(pc):>8}  {mnemonic:<7} {operands}'.rstrip()
            out.append(line + (f'   ; {note}' if note else ''))
            pc += row['size']
        out.append('```')
        out.append('')
    return '\n'.join(out)


def compress_lines(fn):
    result = []
    for lo, hi, key, line in fn.lines:
        if result and result[-1]['end_address'] == lo and result[-1]['file'] == key \
                and result[-1]['line'] == line:
            result[-1]['end_address'] = hi
            result[-1]['end'] = fn.rel(hi)
            continue
        result.append({'start': fn.rel(lo), 'end': fn.rel(hi), 'start_address': lo,
                       'end_address': hi, 'file': key, 'line': line})
    return result


def function_row_for(cfg, name, symbol):
    rows = cfg['functions']
    if symbol:
        matches = [row for row in rows if row['name'] == symbol]
    else:
        matches = [row for row in rows if row['name'] == name or row['name'].endswith('.' + name)]
    if len(matches) != 1:
        raise SystemExit(f'{len(matches)} CFG functions match {symbol or name}; pass --symbol')
    return matches[0]


def build(args):
    recipe = json.loads(resolve(RECIPE).read_text())
    object_path = resolve(args.object or recipe['inputs']['object']['path'])
    if not object_path.exists():
        raise SystemExit(f'{object_path} is absent; run tools/stock_zisk/fetch_inputs.py')
    object_sha = sha256(object_path)
    if object_sha != recipe['inputs']['object']['sha256']:
        raise SystemExit(f'{object_path} has sha256 {object_sha}; the recipe names another')
    zesu_dir = resolve(args.source_dir or recipe['sources']['zesu']['path'])
    commit = check_source_commit(zesu_dir, recipe)
    elf_path = resolve(args.elf)
    cfg = json.loads(resolve(args.cfg).read_text())
    function_row = function_row_for(cfg, args.function, args.symbol)
    symbol = function_row['name']
    run = Path(args.run) if args.run else shared_root() / '_build' / 'agents' / 'aa' / args.function
    out = run / 'hints'
    out.mkdir(parents=True, exist_ok=True)

    dwarf, evidence, elf = load_dwarf(object_path, elf_path)
    symbols = Symbols(elf)
    if symbols.by_name.get(symbol, (None,))[0] != function_row['entry']:
        raise SystemExit(f'ELF symbol {symbol} does not start the CFG function')
    fn = Function(dwarf, symbol, function_row['entry'], function_row['end'])
    sources = Sources(zesu_dir, args.zig_lib)
    zig = sources.zig_lib_record()
    header = [f'- function: `{symbol}` ({len(function_row["blocks"])} blocks, '
              f'{len(function_row["rows"])} instructions)',
              f'- zesu source: commit `{commit}` (recipe `sources.zesu`)',
              f'- object: sha256 `{object_sha}`',
              ('- Zig standard library: ' + (f'`{zig["array_list"]}` sha256 `{zig["sha256"]}`'
                                              if zig else 'absent; std functions get DWARF-only hints'))]

    source_md = render_source(fn, sources, header)
    blocks_md = render_blocks(fn, function_row, elf, symbols, sources, header)
    identity = {'function': symbol, 'entry': function_row['entry'], 'end': function_row['end'],
                'zesu_commit': commit, 'object_sha256': object_sha,
                'elf_sha256': sha256(elf_path), 'zig_lib': zig}
    locations = {'schema': 'zesu.hints.locations.v1', **identity,
                 'frame_base': fn.frame_base, 'dwarf_relocation': evidence,
                 'variables': fn.variables, 'unlocated': fn.unlocated,
                 'inline': [{**{k: v for k, v in frame.items() if k != 'ranges'},
                             'ranges': [{'start': fn.rel(lo), 'end': fn.rel(hi),
                                         'start_address': lo, 'end_address': hi}
                                        for lo, hi in frame['ranges']]}
                            for frame in fn.inlines],
                 'lines': compress_lines(fn), 'sources': sources.record}
    types = {'schema': 'zesu.hints.types.v1', **identity, 'pointer_depth': args.pointer_depth,
             'types': collect_types(fn.type_roots, args.pointer_depth)}
    files = {'SOURCE.md': source_md + '\n', 'BLOCKS.md': blocks_md + '\n',
             'LOCATIONS.json': json.dumps(locations, indent=1) + '\n',
             'TYPES.json': json.dumps(types, indent=1) + '\n'}
    for name, content in files.items():
        (out / name).write_text(content)
    for name in files:
        print(f'{out / name}: {(out / name).stat().st_size} bytes')
    print(f'{len(fn.variables)} located variables, {len(fn.unlocated)} unlocated, '
          f'{len(fn.inlines)} inline ranges, {len(types["types"])} types')


# ---------------------------------------------------------------- slice

BLOCK_HEAD = re.compile(r'^## block \+(0x[0-9a-f]+)\.\.\+(0x[0-9a-f]+)$', re.M)


def parse_pc(text, locations):
    text = text.strip()
    entry, symbol = locations['entry'], locations['function']
    if text.startswith('+'):
        return entry + int(text[1:], 16)
    if '+0x' in text:
        name, offset = text.rsplit('+', 1)
        if name != symbol:
            raise SystemExit(f'{text}: names another symbol than {symbol}')
        return entry + int(offset, 16)
    if text == symbol:
        return entry
    return int(text, 0)


def base_names(type_text):
    """The type itself, then each type left after removing one leading `*` or `[n]`."""
    names = [type_text]
    while True:
        stripped = re.sub(r'^(?:\*|\[[^\]]*\])', '', names[-1])
        if stripped == names[-1]:
            return names
        names.append(stripped)


def type_closure(names, types):
    result, work = {}, list(names)
    while work:
        name = work.pop()
        for base in base_names(name):
            if base in types and base not in result:
                result[base] = types[base]
                work.extend(member['type'] for member in types[base].get('members', ()))
    return result


def slice_pack(hints_dir, pcs):
    hints_dir = Path(hints_dir)
    locations = json.loads((hints_dir / 'LOCATIONS.json').read_text())
    types = json.loads((hints_dir / 'TYPES.json').read_text())['types']
    blocks_md = (hints_dir / 'BLOCKS.md').read_text()
    entry = locations['entry']
    wanted = sorted({parse_pc(pc, locations) for pc in pcs})
    heads = list(BLOCK_HEAD.finditer(blocks_md))
    out = [f'# Hint slice of `{locations["function"]}` at '
           + ', '.join(f'+{pc - entry:#x}' for pc in wanted), '']
    chosen = []
    for index, head in enumerate(heads):
        lo, hi = entry + int(head.group(1), 16), entry + int(head.group(2), 16)
        if any(lo <= pc < hi for pc in wanted):
            stop = heads[index + 1].start() if index + 1 < len(heads) else len(blocks_md)
            chosen.append(blocks_md[head.start():stop].rstrip())
    missing = [pc for pc in wanted
               if not any(entry + int(h.group(1), 16) <= pc < entry + int(h.group(2), 16) for h in heads)]
    if missing:
        raise SystemExit('pcs outside every block: ' + ', '.join(f'+{pc - entry:#x}' for pc in missing))
    out.extend(chosen)
    out.append('')
    out.append('## variables at these pcs')
    out.append('')
    type_names = set()
    for pc in wanted:
        out.append(f'- +{pc - entry:#x}:')
        for variable in locations['variables']:
            for piece in variable['ranges']:
                if piece['start_address'] <= pc < piece['end_address']:
                    out.append(f'  - `{variable["name"]}` ({variable["kind"]} of {variable["scope"][-1]}, '
                               f'{variable["type"]}, declared {variable["decl"]}): '
                               f'{location_text(piece["location"])} for {piece["start"]}..{piece["end"]}')
                    type_names.add(variable['type'])
                    break
    closure = type_closure(type_names, types)
    if closure:
        out.append('')
        out.append('## types')
        out.append('')
        for name, entry_type in sorted(closure.items()):
            out.append(f'- `{name}` ({entry_type["kind"]}, {entry_type["byte_size"]} bytes)')
            for member in entry_type.get('members', ()):
                out.append(f'  - {member["offset"]}: `{member["name"]}` {member["type"]} '
                           f'({member["size"]} bytes)')
            if 'values' in entry_type:
                out.append('  - values: ' + ', '.join(f'{k}={v}' for k, v in entry_type['values'].items()))
    return '\n'.join(out) + '\n'


def cmd_slice(args):
    text = slice_pack(args.hints, [pc for group in args.pcs for pc in group.split(',') if pc])
    if args.max_bytes and len(text.encode()) > args.max_bytes:
        raise SystemExit(f'slice has {len(text.encode())} bytes, above --max-bytes {args.max_bytes}')
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)


def cmd_counts(args):
    recipe = json.loads(resolve(RECIPE).read_text())
    object_path = resolve(args.object or recipe['inputs']['object']['path'])
    obj = open_elf(object_path)
    print(json.dumps(counts(obj.get_dwarf_info(relocate_dwarf_sections=False)), sort_keys=True))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    commands = parser.add_subparsers(dest='command', required=True)
    make = commands.add_parser('build', help='write <run dir>/hints/')
    make.add_argument('--function', required=True, help='region name; names the run dir')
    make.add_argument('--symbol', help='CFG function name; default: the unique one ending in .FUNCTION')
    make.add_argument('--run', help='run dir; default _build/agents/aa/FUNCTION of the main checkout')
    make.add_argument('--object', help='pre-link object; default inputs.object of the recipe')
    make.add_argument('--elf', default=str(ELF))
    make.add_argument('--cfg', default=str(CFG))
    make.add_argument('--source-dir', help='zesu source; default sources.zesu.path of the recipe')
    make.add_argument('--zig-lib', help='Zig 0.16.0 tree holding lib/std; std hints are DWARF-only without it')
    make.add_argument('--pointer-depth', type=int, default=1,
                      help='pointer hops followed when collecting types')
    make.set_defaults(run_command=build)
    cut = commands.add_parser('slice', help='print the hint part for some pcs')
    cut.add_argument('--hints', required=True, help='a hints/ directory written by build')
    cut.add_argument('--pcs', required=True, action='append',
                     help='comma-separated +0xOFFSET or SYMBOL+0xOFFSET')
    cut.add_argument('--out')
    cut.add_argument('--max-bytes', type=int, help='fail when the slice is larger')
    cut.set_defaults(run_command=cmd_slice)
    count = commands.add_parser('counts', help='DWARF sanity counts of the object')
    count.add_argument('--object')
    count.set_defaults(run_command=cmd_counts)
    args = parser.parse_args(argv)
    args.run_command(args)


if __name__ == '__main__':
    main()
