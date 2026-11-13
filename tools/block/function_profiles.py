"""Per-function inputs of the FP301 block renderers.

A profile names everything that differs between functions: the argument
type, the contract modules, the selected-code premise, the output module
directory, the domain fact, the block list, and the loop inputs. The
renderers keep their structure; they read these values from the profile.
A profile holds declarations data only. It never holds a proof script.
"""
from functools import lru_cache
import json
from pathlib import Path

PROFILE_DIRECTORY = Path(__file__).resolve().parent / 'functions'
DEFAULT_FUNCTION = 'decodeItem'
SYMBOL_TABLE = Path(__file__).resolve().parents[2] / 'build/stock-zisk/symbols.txt'

# Fields that hold a block of the function itself: a 4-digit suffix in the legacy form,
# an offset `+0x..` from the function symbol in the symbol form.
BLOCK_LISTS = ['blocks', 'loop_heads']
ADDRESS_FIELDS = ['call_site_pc', 'callee_pc', 'return_site_pc', 'return_instruction_pc']

REQUIRED = [
    'function', 'args_type', 'pc_prefix', 'generated_directory', 'callers_directory',
    'contract_requires', 'loop_contract_requires', 'selected_code', 'domain_component',
    'blocks', 'loop_heads',
]


class FunctionProfile:
    """Read-only view of one function's renderer inputs."""

    def __init__(self, data, path=None):
        missing = [key for key in REQUIRED if key not in data]
        if missing:
            raise ValueError('The function profile lacks: ' + ', '.join(missing))
        self.data = data
        self.path = path

    def __getitem__(self, key):
        return self.data[key]

    def get(self, key, default=None):
        return self.data.get(key, default)

    @property
    def name(self):
        return self.data['function']

    @property
    def args_type(self):
        return self.data['args_type']

    @property
    def generated_directory(self):
        return self.data['generated_directory']

    @property
    def generated_module(self):
        return '.'.join(Path(self.data['generated_directory']).parts)

    def pc(self, suffix):
        """Return the address string of a block suffix, for example 0x800d6960."""
        return self.data['pc_prefix'] + suffix

    def qualified(self, module, symbol=None):
        result = self.generated_module + '.' + module
        return result if symbol is None else result + '.' + symbol

    def telescope(self):
        return ' `{!islaG Sigma} `{!threadG} (args : ' + self.args_type + ') (returnAddress : Z)'

    def selected_import(self):
        return 'Require Import ' + self.data['selected_code']['module'] + '.\n'

    def selected_premise(self):
        return self.data['selected_code']['premise']


@lru_cache(maxsize=None)
def symbol_table(path=SYMBOL_TABLE):
    """The ELF symbol addresses from `readelf -Ws` output (tools/stock_zisk/build.py)."""
    result = {}
    for row in Path(path).read_text().splitlines():
        fields = row.split()
        if len(fields) >= 8 and fields[0].endswith(':') and fields[0][:-1].isdigit():
            result.setdefault(fields[7], int(fields[1], 16))
    return result


def resolve_symbol_keys(data, symbols):
    """Rewrite a table keyed by symbol and offset to the address form the renderers read.

    The table names its function's ELF `symbol`. A block is `+0xOFFSET` from that symbol;
    an address field (a call site, a callee, a return instruction) is `+0xOFFSET` or
    `SYMBOL+0xOFFSET`. Blocks become 4-digit suffixes under `pc_prefix`, as the generated
    names use them; address fields become absolute addresses. A relink then changes only
    the symbol table, not the design table."""
    if 'symbol' not in data:
        return data
    if data['symbol'] not in symbols:
        raise ValueError('The ELF has no symbol ' + data['symbol'])
    base = symbols[data['symbol']]

    def absolute(text):
        name, _, offset = text.partition('+')
        if not offset.startswith('0x'):
            raise ValueError('A symbol key needs a hex offset: ' + text)
        if name and name not in symbols:
            raise ValueError('The ELF has no symbol ' + name)
        return (symbols[name] if name else base) + int(offset, 16)

    first = absolute(data['blocks'][0])
    prefix = hex(first)[:-4]

    def suffix(text):
        if not text.startswith('+'):
            raise ValueError('A block of the function is an offset from its symbol: ' + text)
        address = hex(absolute(text))
        if not address.startswith(prefix):
            raise ValueError('A block lies outside the address prefix of the first block: ' + text)
        return address[len(prefix):]

    def walk(value, key=None):
        if isinstance(value, dict):
            return {(suffix(k) if isinstance(k, str) and k.startswith('+') else k): walk(v, k)
                    for k, v in value.items()}
        if isinstance(value, list):
            return [walk(item, key) for item in value]
        if isinstance(value, str) and key in ADDRESS_FIELDS:
            return hex(absolute(value))
        if isinstance(value, str) and key in BLOCK_LISTS:
            return suffix(value)
        if isinstance(value, str) and value.startswith('+0x'):
            return suffix(value)
        return value

    resolved = walk({key: value for key, value in data.items() if key != 'symbol'})
    resolved.update(symbol=data['symbol'], pc_prefix=prefix)
    return resolved


def load_profile(name=None):
    """Load a profile by function name or by path. No name means decodeItem."""
    if name is None:
        name = DEFAULT_FUNCTION
    path = Path(name)
    if not path.suffix:
        path = PROFILE_DIRECTORY / (name + '.json')
    data = json.loads(path.read_text())
    if 'symbol' in data:
        data = resolve_symbol_keys(data, symbol_table())
    if data.get('loop_heads') and 'loop_head_fixture' not in data:
        # The loop-head rows of a design-table loop live beside the other fixtures.
        data['loop_head_fixture'] = 'tools/block/fixtures/%s-loop-heads.json' % data['function'].lower()
    return FunctionProfile(data, path)


def function_returns(profile):
    """The function-return design rows: `function_returns` (a list), or the older single
    `function_return`. Each row names its `return_instruction_pc` and a `return_fact`;
    `True` (or JSON true) allows the exit resources only and adds no meaning."""
    rows = profile.get('function_returns') if profile else None
    if rows is None:
        row = profile.get('function_return') if profile else None
        rows = [row] if row else []
    return list(rows)


def return_sites(profile):
    """(suffix, design) per function-return design. One site keeps the plain names
    `fp_machineReturn` / `FunctionReturn*`; several sites suffix each name with the return
    instruction's address digits after the profile prefix."""
    designs = function_returns(profile)
    if len(designs) <= 1:
        return [('', design) for design in designs]
    prefix = profile['pc_prefix']
    sites = []
    for design in designs:
        pc = hex(int(design['return_instruction_pc'], 0))
        if not pc.startswith(prefix):
            raise ValueError('A return instruction lies outside the profile address prefix: ' + pc)
        sites.append((pc[len(prefix):], design))
    return sites


def return_alignment_fact(profile):
    """The pure conjunct of a `return_address` design row: the register's value at the function
    entry is aligned, stated on bv_unsigned of that value (F44). None without a row."""
    row = profile.get('return_address') if profile else None
    if not row:
        return None
    # An equation, not (n | x): an introduced divisibility hypothesis becomes x = c * n, and the
    # same goal at a successor then has no proof.
    return '\u231c(bv_unsigned %s mod %d = 0)%%Z\u231d' % (row['value'], row['alignment'])


def add_return_alignment(public, profile):
    """Give the function-entry seed the return-address conjunct, before its terminal True. The
    forward pass carries it to every entry; loop-head classes get it beside the domain."""
    fact = return_alignment_fact(profile)
    components = public['assertion_tree']['components']
    if fact is None or any(component.get('id') == 'return_address_alignment' for component in components):
        return public
    row = profile.get('return_address')
    register, = [component for component in components
                 if component.get('kind') == 'register' and component.get('register') == row['register']]
    if register['value_coq'] != row['value']:
        raise ValueError('The return-address row names %s; the entry seed gives %s %s'
                         % (row['value'], row['register'], register['value_coq']))
    terminal = next(index for index, component in enumerate(components) if component.get('coq') == 'True')
    components.insert(terminal, {'kind': 'opaque', 'id': 'return_address_alignment',
                                 'original_component': fact, 'coq': fact})
    return public


def _lines(rows):
    return ''.join(row + '\n' for row in rows)


def pilot_header(profile):
    """Header of the forward-pass entry declarations."""
    return ('(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)\n'
            'Require ZesuSsz.Automation.Hooks.\n'
            'Require Import isla.riscv64.riscv64.\n'
            'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
            'Require Import stdpp.bitvector.definitions.\n'
            + _lines(profile['contract_requires'])
            + 'Require Import ZesuSsz.Contracts.Level1.\n'
            'Local Open Scope Z_scope.\n')


def return_header(profile):
    """Header of the function-return package declarations."""
    return ('(* Generated from the authenticated function-return resource package. *)\n'
            'Require Import isla.riscv64.riscv64.\n'
            'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
            + _lines(profile['contract_requires'])
            + 'Require ZesuSsz.Automation.Hooks.\n'
            'Local Open Scope Z_scope.\n')


def loop_header(profile):
    """Header of the loop-derived successor and exit declarations."""
    return ('(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)\n'
            'Require Import ZesuSsz.Automation2.All.\n'
            'Require Import isla.riscv64.riscv64.\n'
            'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
            'Require Import stdpp.bitvector.definitions.\n'
            + _lines(profile['loop_contract_requires'])
            + 'Require Import ZesuSsz.Contracts.Level1.\n'
            'Require Import ZesuSsz.Automation2.ByteWindowFold.\n'
            'Local Open Scope Z_scope.\n')
