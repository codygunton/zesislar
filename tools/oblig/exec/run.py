#!/usr/bin/env python3
"""Machine runs of one region of the pinned ELF under Unicorn (RV64), with state snapshots.

Test evidence only: machine runs filter proposed assertions (`annotations.py test`); no statement or
proof cites them. The region entry, the allocator entries, `memcpy` and every symbol the run names
come from the `.symtab` of `build/stock-zisk/zesu-zisk.elf`; this file names no code address.

    run.py --function F --inputs FILE [--at +0xOFF,...] [--alloc-fail N] [--remap top|never]
           [--input ID ...] --run RUN

Regions (`F`): see `PROFILES`. Inputs: `inputs/<F>.json`, schema `oblig-exec-inputs/1`:
`{"schema", "function", "inputs": [{"id", ...function fields..., "expect": {...}}]}`.
Function fields: `hex` (encoded bytes) for the decoders; `len`, `capacity` and, for
`keysEnsureCapacity`, `new_capacity` for the array-list regions. `expect` lists outcome keys
and their expected values; `expect_ok` in the result compares them. When `--alloc-fail N` makes
an allocation fail, the expectation is the profile's out-of-memory outcome instead.

Hooks replace `memcpy` (the ZisK CSR stub; the copied length is written to the ZisK scratch word,
as ZiskRuntime.v states) and the allocator entries `alloc`, `resize`, `remap`, `free` (reached by
`jalr` through `alt_fl_alloc.vtable`) by a bump allocator in RAM. `resize`/`remap` succeed in place
for a shrink or for the most recent live block (`--remap top`, the default), and always fail with
`--remap never`, so the caller allocates, copies and frees. `--alloc-fail N`: the N-th call of
`alloc` (1-based, counted per input) returns null.

Output (schemas `oblig-exec-snapshot/1`, `oblig-exec-result/1`, `oblig-exec-run/1`):

- `<RUN>/exec/<dir>/STATE-<oooo>.json`, one file per requested offset that control reached, `<oooo>`
  the 4-hex offset from the function symbol, `<dir>` the input id with `.alloc-fail-<N>` and
  `.remap-never` appended when those options are given:
  `{"schema", "function", "symbol", "elf_sha256", "input", "alloc_fail", "remap", "offset": "+0x00c4",
    "visits": [{"visit": k, "insn": n, "regs": {"pc", "ra", "sp", ..., "t6"}, "memory":
    [{"name", "base", "size", "hex"}]}]}`.
  One visit row per time control reaches the offset, taken before that instruction executes.
  `regs`: the 31 integer registers by ABI name plus `pc`, unsigned 64-bit integers.
  `memory`: the ranges the run's contract owns at the visit:
  `frame` (the region's own frame, `[entry sp - N, entry sp)`, `N` from the prologue `addi sp, sp, -N`),
  `zisk-scratch` (8 bytes), `heap#<k>` (each live bump-allocator block, `k` its allocation order),
  and the profile's argument ranges: `input`, `result` (decoders); `rest`, `allocator`, `vtable`
  (`txAccessList`); `list`, `allocator`, `vtable`, `result` (array-list regions; no `result` for
  `keysEnsureCapacity`).
- `<RUN>/exec/<dir>/RESULT.json`: `{"schema", "function", "input", "alloc_fail", "remap", "stop",
  "outcome", "expect", "expect_ok", "calls": [{"callee", "site", "a0", "a1", "a2"}], "allocator":
  [{"op", "site", ...}], "alloc_failed", "heap_live", "oob_reads", "oob_first", "writes_oob",
  "unmapped", "sp_restored", "callee_saved_ok", "insns", "visits": {"+0xOFF": count}}`.
  `oob_reads` counts data reads outside the owned ranges (including `memcpy` source bytes outside
  owned ranges, live heap blocks and `.rodata`).
- `<RUN>/exec/RUN.json`: one row per input: id, dir, stop, outcome kind, expect_ok, snapshot counts.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import struct
import sys
from pathlib import Path

from elftools.elf.elffile import ELFFile
from unicorn import (UC_ARCH_RISCV, UC_HOOK_BLOCK, UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_UNMAPPED,
                     UC_HOOK_MEM_WRITE, UC_MEM_FETCH_UNMAPPED, UC_MEM_READ_UNMAPPED, UC_MEM_WRITE_UNMAPPED,
                     UC_MODE_RISCV64, UC_PROT_ALL, Uc, UcError)
from unicorn import riscv_const as R

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_ELF = ROOT / 'build' / 'stock-zisk' / 'zesu-zisk.elf'

# ZisK platform constants (ZesuSsz/Contracts/ZiskRuntime.v, ParentHeaderContract.v); no code addresses.
INPUT_WINDOW = (1 << 30, 1 << 31)  # ZisK input window
INPUT_MAPPED = 0x400000          # first 4 MiB of the input window, zero filled
INPUT_PTR = 0x40000008           # ZisK places input data after an 8-byte length header
RAM = (0xa0000000, 0xc0000000)
ROM_END = 0x88000000
ZISK_SCRATCH = 0xa0400f00        # ziskExtraParamsAddress
DATA_PTR = 0xa0500000            # encoded bytes for decoders whose contract reads RAM
CELLS = 0xa0600000               # argument cells: slices, lists, allocator
RESULT_PTR = 0xa0700000
SP0 = 0xa0800000
HEAP = (0xb0000000, 0xbf000000)
STACK_WINDOW = 0x4000            # owned stack below the entry sp: own frame and callee frames
SENTINEL = 0x1000                # unmapped, 4-aligned return address
PAGE = 0x1000
CALLEE_SAVED = [R.UC_RISCV_REG_X8, R.UC_RISCV_REG_X9] + [getattr(R, f'UC_RISCV_REG_X{i}') for i in range(18, 28)]
ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6',
       'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
XREG = [getattr(R, f'UC_RISCV_REG_X{i}') for i in range(32)]
A = XREG[10:18]
ALLOCATOR = {'alloc': 'alt_fl_alloc.alloc', 'resize': 'alt_fl_alloc.resize',
             'remap': 'alt_fl_alloc.remap', 'free': 'alt_fl_alloc.free'}


class Elf:
    """Segments, symbols and sections of the pinned ELF."""

    def __init__(self, path: Path):
        data = path.read_bytes()
        self.path, self.sha256 = path, hashlib.sha256(data).hexdigest()
        elf = ELFFile(io.BytesIO(data))
        self.segments = [(s['p_vaddr'], s['p_memsz'], s.data()) for s in elf.iter_segments()
                         if s['p_type'] == 'PT_LOAD' and s['p_memsz']]
        self.sections = [(s.name, s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in elf.iter_sections()
                         if s['sh_addr'] and s['sh_size']]
        self.symbols: dict[str, tuple[int, int]] = {}
        self.funcs: dict[int, str] = {}
        self.objects: list[tuple[int, int, str]] = []
        symtab = elf.get_section_by_name('.symtab')
        if symtab is None:
            raise SystemExit(f'{path}: no .symtab')
        for s in symtab.iter_symbols():
            kind, addr, size = s['st_info']['type'], s['st_value'], s['st_size']
            if not s.name or kind not in ('STT_FUNC', 'STT_OBJECT'):
                continue
            self.symbols.setdefault(s.name, (addr, size))
            if kind == 'STT_FUNC' and size:
                self.funcs.setdefault(addr, s.name)
            elif kind == 'STT_OBJECT' and size:
                self.objects.append((addr, size, s.name))
        self.objects.sort()

    def sym(self, name: str) -> int:
        if name not in self.symbols:
            raise SystemExit(f'symbol {name!r} not in {self.path}')
        return self.symbols[name][0]

    def section(self, addr: int) -> str | None:
        return next((n for n, lo, hi in self.sections if lo <= addr < hi), None)

    def describe(self, addr: int) -> str:
        """`symbol+0xOFF` for an address inside a function or object, else its section."""
        for base, name in self.funcs.items():
            if base <= addr < base + self.symbols[name][1]:
                return f'{name}+{addr - base:#x}'
        for base, size, name in self.objects:
            if base <= addr < base + size:
                return f'{name}+{addr - base:#x}'
        return self.section(addr) or 'unmapped'

    def word(self, addr: int) -> int:
        for base, _, data in self.segments:
            if base <= addr and addr + 4 <= base + len(data):
                return struct.unpack_from('<I', data, addr - base)[0]
        raise SystemExit(f'{addr:#x} is not file-backed')


def frame_size(elf: Elf, entry: int) -> int:
    """N of a prologue `addi sp, sp, -N` at the entry, else 0."""
    w = elf.word(entry)
    if w & 0x7f == 0x13 and (w >> 7) & 0x1f == 2 and (w >> 12) & 7 == 0 and (w >> 15) & 0x1f == 2:
        imm = w >> 20
        imm -= (imm & 0x800) << 1
        return -imm if imm < 0 else 0
    return 0


class Heap:
    """Bump allocator; `blocks` keeps every block in allocation order."""

    def __init__(self, remap: str):
        self.top, self.blocks, self.remap = HEAP[0], [], remap

    def alloc(self, n: int, align: int) -> int:
        base = (self.top + align - 1) & -align
        if base + n > HEAP[1]:
            return 0
        self.blocks.append({'k': len(self.blocks), 'base': base, 'size': n, 'live': True})
        self.top = base + n
        return base

    def live(self, ptr: int):
        return next((b for b in self.blocks if b['live'] and b['base'] == ptr), None)

    def grow(self, ptr: int, old: int, new: int) -> tuple[bool, str | None]:
        b = self.live(ptr)
        if b is None:
            return False, 'not a live block'
        note = None if b['size'] == old else f'length {old} != block size {b["size"]}'
        if self.remap == 'never':
            return False, note
        if new <= b['size']:
            b['size'] = new
            return True, note
        if b['base'] + b['size'] == self.top and b['base'] + new <= HEAP[1]:
            b['size'] = new
            self.top = b['base'] + new
            return True, note
        return False, note

    def free(self, ptr: int, n: int) -> str | None:
        b = self.live(ptr)
        if b is None:
            return 'not a live block'
        b['live'] = False
        return None if b['size'] == n else f'length {n} != block size {b["size"]}'


class Machine:
    """One run of a region on one input."""

    def __init__(self, elf: Elf, profile: 'Profile', row: dict, at: list[int], alloc_fail: int | None,
                 remap: str, max_insns: int):
        self.elf, self.profile, self.row = elf, profile, row
        self.entry = elf.sym(profile.symbol)
        self.size = elf.symbols[profile.symbol][1]
        self.frame = frame_size(elf, self.entry)
        self.at = {self.entry + off: off for off in at}
        self.alloc_fail, self.max_insns = alloc_fail, max_insns
        self.heap = Heap(remap)
        self.ranges: list[tuple[str, int, int, bool]] = []   # name, base, size, writable
        self.visits: dict[int, list[dict]] = {off: [] for off in at}
        self.insns, self.alloc_calls, self.alloc_failed = 0, 0, False
        self.calls, self.alloc_log, self.oob, self.writes_oob, self.unmapped = [], [], [], [], []
        self.blocks, self.memcpy = [], []
        self.stop = None
        uc = self.uc = Uc(UC_ARCH_RISCV, UC_MODE_RISCV64)
        self._map()
        self.stubs = {elf.sym('memcpy'): self._memcpy}
        for op, name in ALLOCATOR.items():
            self.stubs[elf.sym(name)] = getattr(self, '_' + op)
        uc.mem_write(ZISK_SCRATCH, b'\x5a' * 8)
        for r, v in ((R.UC_RISCV_REG_PC, self.entry), (R.UC_RISCV_REG_RA, SENTINEL), (R.UC_RISCV_REG_SP, SP0)):
            uc.reg_write(r, v)
        for i, r in enumerate(CALLEE_SAVED):
            uc.reg_write(r, 0x5000 + i)
        for r, v in zip(A, profile.setup(self, row)):
            uc.reg_write(r, v)

    # -- memory -------------------------------------------------------------------------------
    def _map(self):
        uc, mapped = self.uc, []
        for vaddr, memsz, data in self.elf.segments:
            lo, hi = vaddr & ~(PAGE - 1), (vaddr + memsz + PAGE - 1) & ~(PAGE - 1)
            for mlo, mhi in mapped:
                if mlo <= lo < mhi:
                    lo = mhi
            if hi > lo:
                uc.mem_map(lo, hi - lo, UC_PROT_ALL)
                mapped.append((lo, hi))
            uc.mem_write(vaddr, data)
        uc.mem_map(INPUT_WINDOW[0], INPUT_MAPPED, UC_PROT_ALL)
        cursor = RAM[0]
        for mlo, mhi in sorted(m for m in mapped if RAM[0] <= m[0] < RAM[1]) + [(RAM[1], RAM[1])]:
            if mlo > cursor:
                uc.mem_map(cursor, mlo - cursor, UC_PROT_ALL)
            cursor = max(cursor, mhi)

    def own(self, name: str, base: int, size: int, writable: bool, data: bytes | None = None):
        self.ranges.append((name, base, size, writable))
        if data is not None:
            self.uc.mem_write(base, data)

    def read(self, addr: int, n: int) -> bytes:
        return bytes(self.uc.mem_read(addr, n))

    def u64(self, addr: int) -> int:
        return struct.unpack('<Q', self.read(addr, 8))[0]

    def reg(self, r: int) -> int:
        return self.uc.reg_read(r)

    def _inside(self, addr: int, n: int, write: bool) -> bool:
        if SP0 - STACK_WINDOW <= addr and addr + n <= SP0:
            return True
        if ZISK_SCRATCH <= addr and addr + n <= ZISK_SCRATCH + 8:
            return True
        if any(base <= addr and addr + n <= base + size and (w or not write)
               for _, base, size, w in self.ranges):
            return True
        return any(b['live'] and b['base'] <= addr and addr + n <= b['base'] + b['size'] for b in self.heap.blocks)

    def _class(self, addr: int) -> str:
        if any(b['base'] <= addr < b['base'] + max(b['size'], 1) for b in self.heap.blocks):
            return 'heap(freed)'
        if INPUT_WINDOW[0] <= addr < INPUT_WINDOW[1]:
            return 'input-window'
        if RAM[0] <= addr < RAM[1]:
            return 'ram'
        if self.elf.section(addr) is not None or addr < ROM_END and addr >= self.elf.sections[0][1]:
            return f'{self.elf.section(addr) or "rom"}:{self.elf.describe(addr)}'
        return 'unmapped-on-ZisK'

    def site(self, pc: int) -> str:
        if self.entry <= pc < self.entry + self.size:
            return f'+{pc - self.entry:#06x}'
        return self.elf.describe(pc)

    # -- hooks --------------------------------------------------------------------------------
    def _return(self, value: int | None):
        if value is not None:
            self.uc.reg_write(A[0], value)
        self.uc.reg_write(R.UC_RISCV_REG_PC, self.reg(R.UC_RISCV_REG_RA))

    def _caller(self) -> str:
        return self.site(self.reg(R.UC_RISCV_REG_RA) - 4)

    def _memcpy(self):
        dst, src, n = (self.reg(r) for r in A[:3])
        for a in range(src, src + n):
            if not (self._inside(a, 1, False) or (self.elf.section(a) or '').startswith('.rodata')):
                self.oob.append((self._caller(), a, 1, self._class(a)))
        if not self._inside(dst, n, True) and n:
            self.writes_oob.append((self._caller(), dst, n))
        self.uc.mem_write(dst, self.read(src, n))
        self.uc.mem_write(ZISK_SCRATCH, struct.pack('<Q', n))
        self.memcpy.append({'site': self._caller(), 'dst': dst, 'src': src, 'len': n})
        self._return(None)

    def _alloc(self):
        n, align = self.reg(A[1]), 1 << self.reg(A[2])
        self.alloc_calls += 1
        if self.alloc_fail == self.alloc_calls:
            ptr, self.alloc_failed = 0, True
        else:
            ptr = self.heap.alloc(n, align)
        self.alloc_log.append({'op': 'alloc', 'site': self._caller(), 'len': n, 'align': align, 'ptr': ptr})
        self._return(ptr)

    def _grow(self, op: str):
        ptr, old, align, new = (self.reg(r) for r in A[1:5])
        ok, note = self.heap.grow(ptr, old, new)
        self.alloc_log.append({'op': op, 'site': self._caller(), 'ptr': ptr, 'len': old, 'align': 1 << align,
                               'new_len': new, 'ok': ok, **({'note': note} if note else {})})
        self._return((ptr if ok else 0) if op == 'remap' else int(ok))

    def _resize(self):
        self._grow('resize')

    def _remap(self):
        self._grow('remap')

    def _free(self):
        ptr, n, align = (self.reg(r) for r in A[1:4])
        note = self.heap.free(ptr, n)
        self.alloc_log.append({'op': 'free', 'site': self._caller(), 'ptr': ptr, 'len': n, 'align': 1 << align,
                               **({'note': note} if note else {})})
        self._return(None)

    def snapshot(self, off: int):
        regs = {'pc': self.reg(R.UC_RISCV_REG_PC)}
        regs.update((ABI[i], self.reg(XREG[i])) for i in range(1, 32))
        memory = [(n, b, s) for n, b, s, _ in self.ranges]
        memory += [('frame', SP0 - self.frame, self.frame), ('zisk-scratch', ZISK_SCRATCH, 8)]
        memory += [(f'heap#{b["k"]}', b['base'], b['size']) for b in self.heap.blocks if b['live']]
        self.visits[off].append({'visit': len(self.visits[off]), 'insn': self.insns, 'regs': regs, 'memory': [
            {'name': n, 'base': b, 'size': s, 'hex': self.read(b, s).hex()} for n, b, s in memory]})

    def run(self) -> 'Machine':
        uc, end = self.uc, self.entry + self.size

        def on_code(uc, addr, size, _):
            self.insns += 1
            if self.insns > self.max_insns:
                self.stop = 'insn limit'
                uc.emu_stop()
                return
            if addr in self.at:
                self.snapshot(self.at[addr])
            if addr in self.elf.funcs and addr != self.entry:
                site = self.reg(R.UC_RISCV_REG_RA) - 4
                if self.entry <= site < end:
                    self.calls.append({'callee': self.elf.funcs[addr], 'site': self.site(site),
                                       **{ABI[10 + i]: self.reg(A[i]) for i in range(3)}})
            stub = self.stubs.get(addr)
            if stub:
                stub()

        def on_block(uc, addr, size, _):
            if self.entry <= addr < end:
                self.blocks.append(addr - self.entry)

        def on_read(uc, access, addr, size, value, _):
            if not self._inside(addr, size, False):
                self.oob.append((self.site(self.reg(R.UC_RISCV_REG_PC)), addr, size, self._class(addr)))

        def on_write(uc, access, addr, size, value, _):
            if not self._inside(addr, size, True):
                self.writes_oob.append((self.site(self.reg(R.UC_RISCV_REG_PC)), addr, size))

        def on_unmapped(uc, access, addr, size, value, _):
            kind = {UC_MEM_READ_UNMAPPED: 'read', UC_MEM_WRITE_UNMAPPED: 'write',
                    UC_MEM_FETCH_UNMAPPED: 'fetch'}.get(access, str(access))
            if kind == 'fetch' and addr == SENTINEL:
                return False
            self.unmapped.append((self.site(self.reg(R.UC_RISCV_REG_PC)), addr, size, kind))
            if kind == 'fetch' or len(self.unmapped) > 64:
                return False
            uc.mem_map(addr & ~(PAGE - 1), PAGE * 2 if (addr & (PAGE - 1)) + size > PAGE else PAGE, UC_PROT_ALL)
            return True

        uc.hook_add(UC_HOOK_CODE, on_code)
        uc.hook_add(UC_HOOK_BLOCK, on_block)
        uc.hook_add(UC_HOOK_MEM_READ, on_read)
        uc.hook_add(UC_HOOK_MEM_WRITE, on_write)
        uc.hook_add(UC_HOOK_MEM_UNMAPPED, on_unmapped)
        try:
            uc.emu_start(self.entry, SENTINEL, count=0)
        except UcError as e:
            if self.reg(R.UC_RISCV_REG_PC) != SENTINEL and self.stop is None:
                self.stop = f'UcError {e} at {self.site(self.reg(R.UC_RISCV_REG_PC))}'
        if self.stop is None:
            self.stop = 'returned' if self.reg(R.UC_RISCV_REG_PC) == SENTINEL else 'stopped'
        return self

    def result(self) -> dict:
        outcome = self.profile.outcome(self, self.row)
        expect = self.row.get('expect')
        if self.alloc_failed:
            expect = self.profile.oom_expect
        ok = None if expect is None else all(outcome.get(k) == v for k, v in expect.items())
        live = [b for b in self.heap.blocks if b['live']]
        return {
            'schema': 'oblig-exec-result/1', 'function': self.profile.name, 'input': self.row['id'],
            'alloc_fail': self.alloc_fail, 'remap': self.heap.remap, 'stop': self.stop, 'outcome': outcome,
            'expect': expect, 'expect_ok': ok, 'calls': self.calls, 'allocator': self.alloc_log,
            'memcpy': self.memcpy, 'alloc_failed': self.alloc_failed,
            'heap_live': {'blocks': len(live), 'bytes': sum(b['size'] for b in live)},
            'oob_reads': len(self.oob),
            'oob_first': [{'site': s, 'addr': a, 'size': n, 'class': c} for s, a, n, c in self.oob[:8]],
            'oob_classes': sorted({c for *_, c in self.oob}),
            'writes_oob': [{'site': s, 'addr': a, 'size': n} for s, a, n in self.writes_oob[:8]],
            'unmapped': [{'site': s, 'addr': a, 'size': n, 'kind': k} for s, a, n, k in self.unmapped[:8]],
            'sp_restored': self.reg(R.UC_RISCV_REG_SP) == SP0,
            'callee_saved_ok': all(self.reg(r) == 0x5000 + i for i, r in enumerate(CALLEE_SAVED)),
            'insns': self.insns, 'last_blocks': [f'+{b:#06x}' for b in self.blocks[-4:]],
            'visits': {f'+{off:#06x}': len(v) for off, v in self.visits.items()},
        }


# -- profiles ---------------------------------------------------------------------------------
class Profile:
    name = symbol = ''
    oom_expect: dict | None = None

    def setup(self, m: Machine, row: dict) -> list[int]:
        raise NotImplementedError

    def outcome(self, m: Machine, row: dict) -> dict:
        raise NotImplementedError


def allocator_cells(m: Machine, at: int) -> int:
    """A `std.mem.Allocator` `{ptr, vtable}` over `alt_fl_alloc`, and the vtable cells it reaches."""
    state, vtable = m.elf.sym('alt_fl_alloc.state'), m.elf.sym('alt_fl_alloc.vtable')
    m.own('allocator', at, 16, False, struct.pack('<QQ', state, vtable))
    m.own('vtable', vtable, 32, False)
    return at


class DecodeParentHeader(Profile):
    """a0 = result (80 bytes), a1 = input pointer (input window), a2 = input length."""
    name, symbol = 'decodeParentHeader', 'rlp_decode.decodeParentHeader'
    # Exit blocks, as offsets from the symbol (the labels of the recorded evidence).
    EPILOGUE, DIRECT_ERROR, NO_OPTIONALS, WITH_OPTIONALS, MEMCPY_TAIL = 0x274, (0x26c, 0x270), 0x3bc, 0x514, 0xe8

    def setup(self, m, row):
        data = bytes.fromhex(row['hex'])
        m.uc.mem_write(INPUT_PTR - 8, struct.pack('<Q', len(data)))
        m.own('input', INPUT_PTR, len(data), False, data)
        m.own('result', RESULT_PTR, 80, True, b'\xaa' * 80)
        return [RESULT_PTR, INPUT_PTR, len(data)]

    def exit(self, m):
        if m.memcpy:
            return f'memcpy tail +{self.MEMCPY_TAIL:#06x}'
        pre = [b for b in m.blocks if b != self.EPILOGUE][-1:]
        if pre and pre[0] in self.DIRECT_ERROR:
            return f'direct error (tag 3 at +{self.DIRECT_ERROR[1]:#06x})'
        if pre and pre[0] == self.NO_OPTIONALS:
            return f'success, no optionals (+{self.NO_OPTIONALS:#06x})'
        if pre and (pre[0] in (self.WITH_OPTIONALS - 4, self.WITH_OPTIONALS) or self.WITH_OPTIONALS <= pre[0] < m.size):
            return f'success with optionals (+{self.WITH_OPTIONALS:#06x})'
        return 'other: ' + ','.join(f'+{b:#06x}' for b in m.blocks[-4:])

    def outcome(self, m, row):
        r = m.read(RESULT_PTR, 80)
        w = lambda o: struct.unpack_from('<Q', r, o)[0]  # noqa: E731
        tag, out = r[72], {'result_hex': r.hex(), 'exit': self.exit(m)}
        if tag == 0 and r[73] == 0:
            opt = lambda v, t: w(v) if r[t] == 1 else (None if r[t] == 0 else f'badtag{r[t]}')  # noqa: E731
            out['result'] = dict(kind='Success', gasLimit=w(0), gasUsed=w(8), timestamp=w(16), baseFee=opt(24, 32),
                                 blobGasUsed=opt(40, 48), excessBlobGas=opt(56, 64))
        elif tag == 3 and r[73] == 0:
            out['result'] = dict(kind='Error')
        else:
            out['result'] = dict(kind=f'Other(tag={tag},b73={r[73]})')
        out['kind'] = out['result']['kind']
        return out


class DecodeItem(Profile):
    """a0 = result (40 bytes), a1 = input pointer, a2 = input length.

    Result: payload pointer at 0, payload length at 8, kind byte at 16 (0 string, 1 list), bytes consumed
    at 24, error code (u16) at 32: 0 on success; the error exit stores 4 there and zeroes the other words.
    """
    name, symbol = 'decodeItem', 'rlp.decodeItem'

    def setup(self, m, row):
        data = bytes.fromhex(row['hex'])
        m.own('input', DATA_PTR, len(data), False, data)
        m.own('result', RESULT_PTR, 40, True, b'\xaa' * 40)
        return [RESULT_PTR, DATA_PTR, len(data)]

    def outcome(self, m, row):
        r = m.read(RESULT_PTR, 40)
        w = lambda o: struct.unpack_from('<Q', r, o)[0]  # noqa: E731
        error = struct.unpack_from('<H', r, 32)[0]
        out = {'result_hex': r.hex()}
        if error == 0:
            out.update(kind='Success', item='list' if r[16] else 'string', payload_offset=w(0) - DATA_PTR,
                       payload_len=w(8), consumed=w(24))
        else:
            out.update(kind='Error', error=error)
        return out


class TxAccessList(Profile):
    """a0 = result `{ptr, len, err:u16}` (24 bytes), a1 = *Allocator, a2 = rest: *[]const u8.

    `AccessListEntry` is 40 bytes: `storage_keys` slice `{ptr, len}` at 0, `address` (20 bytes) at 16.
    Error code 3 is `error.InvalidBlock`; an allocation failure also ends in it (`catch return error.InvalidBlock`).
    """
    name, symbol = 'txAccessList', 'rlp_decode.txAccessList'
    oom_expect = {'kind': 'Error'}

    def setup(self, m, row):
        data = bytes.fromhex(row['hex'])
        m.own('input', DATA_PTR, len(data), False, data)
        m.own('rest', CELLS, 16, True, struct.pack('<QQ', DATA_PTR, len(data)))
        allocator = allocator_cells(m, CELLS + 0x20)
        m.own('result', RESULT_PTR, 24, True, b'\xaa' * 24)
        return [RESULT_PTR, allocator, CELLS]

    def outcome(self, m, row):
        ptr, n = m.u64(RESULT_PTR), m.u64(RESULT_PTR + 8)
        err = struct.unpack('<H', m.read(RESULT_PTR + 16, 2))[0]
        rest_ptr, rest_len = m.u64(CELLS), m.u64(CELLS + 8)
        out = {'err': err, 'consumed': rest_ptr - DATA_PTR, 'rest_len': rest_len}
        if err == 0:
            entries = []
            for i in range(n):
                e = ptr + 40 * i
                kp, kn = m.u64(e), m.u64(e + 8)
                entries.append({'address': m.read(e + 16, 20).hex(),
                                'keys': [m.read(kp + 32 * j, 32).hex() for j in range(kn)]})
            out.update(kind='Success', entries=entries, key_counts=[len(e['keys']) for e in entries])
        else:
            out['kind'] = 'Error' if err == 3 else f'Other(err={err})'
        return out


class ArrayList(Profile):
    """`std.ArrayListUnmanaged(T)` `{items.ptr, items.len, capacity}`; error code 2 is `error.OutOfMemory`."""
    elem = align = 0
    oom_expect = {'kind': 'OutOfMemory'}

    def pattern(self, i: int) -> bytes:
        return bytes((0x11 * (i % 15 + 1) + j) & 0xff for j in range(self.elem))

    def list_cells(self, m, row) -> int:
        n, cap = row['len'], row['capacity']
        if n > cap:
            raise SystemExit(f'{row["id"]}: len {n} > capacity {cap}')
        if cap:
            ptr = m.heap.alloc(cap * self.elem, self.align)
            m.uc.mem_write(ptr, b''.join(self.pattern(i) for i in range(n)) + b'\xdd' * ((cap - n) * self.elem))
        else:
            ptr = self.align          # Zig's empty-slice pointer is the alignment
        m.own('list', CELLS, 24, True, struct.pack('<QQQ', ptr, n, cap))
        return CELLS

    def items_ok(self, m, ptr: int, n: int) -> bool:
        return all(m.read(ptr + i * self.elem, self.elem) == self.pattern(i) for i in range(n))

    def list_after(self, m) -> dict:
        return dict(zip(('ptr', 'len', 'capacity'), struct.unpack('<QQQ', m.read(CELLS, 24))))


class ToOwnedSlice(ArrayList):
    """a0 = result `{ptr, len, err:u16}`, a1 = *list, a2 = *Allocator."""

    def setup(self, m, row):
        lst = self.list_cells(m, row)
        allocator = allocator_cells(m, CELLS + 0x20)
        m.own('result', RESULT_PTR, 24, True, b'\xaa' * 24)
        return [RESULT_PTR, lst, allocator]

    def outcome(self, m, row):
        ptr, n = m.u64(RESULT_PTR), m.u64(RESULT_PTR + 8)
        err = struct.unpack('<H', m.read(RESULT_PTR + 16, 2))[0]
        after = self.list_after(m)
        out = {'err': err, 'list_after': after}
        if err == 0:
            out.update(kind='Success', len=n, items_ok=self.items_ok(m, ptr, n),
                       list_reset=after['len'] == 0 and after['capacity'] == 0)
        else:
            out['kind'] = 'OutOfMemory' if err == 2 else f'Other(err={err})'
        return out


class KeysToOwnedSlice(ToOwnedSlice):
    name, symbol, elem, align = 'keysToOwnedSlice', 'array_list.Aligned([32]u8,null).toOwnedSlice', 32, 1


class EntriesToOwnedSlice(ToOwnedSlice):
    name, symbol, elem, align = ('entriesToOwnedSlice', 'array_list.Aligned(input.AccessListEntry,null).toOwnedSlice',
                                 40, 8)


class KeysEnsureCapacity(ArrayList):
    """a0 = *list, a1 = *Allocator, a2 = requested capacity; returns the error code in a0 (0 or 2)."""
    name, symbol, elem, align = 'keysEnsureCapacity', 'array_list.Aligned([32]u8,null).ensureTotalCapacity', 32, 1

    def setup(self, m, row):
        lst = self.list_cells(m, row)
        return [lst, allocator_cells(m, CELLS + 0x20), row['new_capacity']]

    def outcome(self, m, row):
        err = m.reg(A[0]) & 0xffff
        after = self.list_after(m)
        out = {'err': err, 'list_after': after}
        if err == 0:
            out.update(kind='Success', len=after['len'], capacity_ok=after['capacity'] >= row['new_capacity'],
                       items_ok=self.items_ok(m, after['ptr'], after['len']))
        else:
            out['kind'] = 'OutOfMemory' if err == 2 else f'Other(err={err})'
        return out


PROFILES = {p.name: p for p in (DecodeParentHeader(), DecodeItem(), TxAccessList(), KeysToOwnedSlice(),
                                EntriesToOwnedSlice(), KeysEnsureCapacity())}


# -- driver -----------------------------------------------------------------------------------
def parse_offsets(text: str | None, size: int) -> list[int]:
    out = []
    for part in filter(None, (text or '').split(',')):
        off = int(part.strip().lstrip('+'), 16)
        if not 0 <= off < size:
            raise SystemExit(f'offset {part} outside the function (size {size:#x})')
        out.append(off)
    return sorted(set(out))


def run_one(elf: Elf, function: str, row: dict, at: list[int] = (), alloc_fail: int | None = None,
            remap: str = 'top', max_insns: int = 2_000_000) -> Machine:
    return Machine(elf, PROFILES[function], row, list(at), alloc_fail, remap, max_insns).run()


def input_dir(row_id: str, alloc_fail: int | None, remap: str) -> str:
    return row_id + (f'.alloc-fail-{alloc_fail}' if alloc_fail else '') + ('.remap-never' if remap == 'never' else '')


def write_run(elf: Elf, function: str, rows: list[dict], run_dir: Path, at: list[int], alloc_fail: int | None,
              remap: str, max_insns: int) -> list[dict]:
    profile, summary = PROFILES[function], []
    for row in rows:
        m = run_one(elf, function, row, at, alloc_fail, remap, max_insns)
        d = run_dir / 'exec' / input_dir(row['id'], alloc_fail, remap)
        d.mkdir(parents=True, exist_ok=True)
        for stale in d.glob('STATE-*.json'):
            stale.unlink()
        for off, visits in m.visits.items():
            if visits:
                (d / f'STATE-{off:04x}.json').write_text(json.dumps({
                    'schema': 'oblig-exec-snapshot/1', 'function': function, 'symbol': profile.symbol,
                    'elf_sha256': elf.sha256, 'input': row['id'], 'alloc_fail': alloc_fail, 'remap': remap,
                    'offset': f'+{off:#06x}', 'visits': visits}) + '\n')
        res = m.result()
        (d / 'RESULT.json').write_text(json.dumps(res, indent=1) + '\n')
        summary.append({'id': row['id'], 'dir': d.name, 'stop': res['stop'], 'kind': res['outcome'].get('kind'),
                        'expect_ok': res['expect_ok'], 'alloc_failed': res['alloc_failed'],
                        'oob_reads': res['oob_reads'], 'visits': res['visits']})
    return summary


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--function', required=True, choices=sorted(PROFILES))
    ap.add_argument('--inputs', type=Path, help='inputs JSON (default: inputs/<function>.json beside this file)')
    ap.add_argument('--at', help='comma-separated offsets from the function symbol, e.g. +0xc4,+0x18c')
    ap.add_argument('--alloc-fail', type=int, help='the N-th alloc call (1-based) returns null')
    ap.add_argument('--remap', choices=('top', 'never'), default='top')
    ap.add_argument('--input', action='append', help='run only these input ids')
    ap.add_argument('--run', type=Path, required=True, help='run directory')
    ap.add_argument('--elf', type=Path, default=DEFAULT_ELF)
    ap.add_argument('--max-insns', type=int, default=2_000_000)
    args = ap.parse_args(argv)
    elf = Elf(args.elf)
    profile = PROFILES[args.function]
    spec = json.loads((args.inputs or Path(__file__).parent / 'inputs' / f'{args.function}.json').read_text())
    if spec.get('function') != args.function:
        raise SystemExit(f'inputs are for {spec.get("function")!r}, not {args.function!r}')
    rows = [r for r in spec['inputs'] if not args.input or r['id'] in args.input]
    at = parse_offsets(args.at, elf.symbols[profile.symbol][1])
    summary = write_run(elf, args.function, rows, args.run, at, args.alloc_fail, args.remap, args.max_insns)
    out = args.run / 'exec' / 'RUN.json'
    previous = json.loads(out.read_text()) if out.exists() else {}
    previous = previous.get('inputs', []) if previous.get('function') == args.function else []
    dirs = {s['dir'] for s in summary}
    out.write_text(json.dumps({'schema': 'oblig-exec-run/1', 'function': args.function, 'symbol': profile.symbol,
                               'elf_sha256': elf.sha256,
                               'inputs': [p for p in previous if p['dir'] not in dirs] + summary}, indent=1) + '\n')
    for s in summary:
        print(f"{s['dir']}\t{s['stop']}\t{s['kind']}\texpect_ok={s['expect_ok']}\toob={s['oob_reads']}\t"
              + ' '.join(f'{k}:{v}' for k, v in s['visits'].items()))
    return 0 if all(s['expect_ok'] is not False and s['stop'] == 'returned' for s in summary) else 1


if __name__ == '__main__':
    sys.exit(main())
