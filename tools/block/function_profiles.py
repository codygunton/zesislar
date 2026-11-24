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
BLOCK_LISTS = ['blocks', 'loop_heads', 'unreachable_entries', 'unreachable_reached']
ADDRESS_FIELDS = ['call_site_pc', 'callee_pc', 'return_site_pc', 'return_instruction_pc']

REQUIRED = [
    'function', 'args_type', 'generated_directory', 'callers_directory',
    'contract_requires', 'loop_contract_requires', 'selected_code', 'domain_component',
    'blocks', 'loop_heads',
]


class FunctionProfile:
    """Read-only view of one function's renderer inputs."""

    def __init__(self, data, path=None):
        missing = [key for key in REQUIRED if key not in data]
        if 'pc_base' not in data and 'pc_prefix' not in data:
            missing.append('pc_prefix')
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

    def pc(self, key):
        """Return the address string of a block key, for example 0x800d6960.

        A symbol-keyed table names a block by its offset from the function symbol
        (4 hex digits, `0014`); a legacy table by the address digits after `pc_prefix`."""
        if 'pc_base' in self.data:
            return hex(int(self.data['pc_base'], 16) + int(key, 16))
        return self.data['pc_prefix'] + key

    def key(self, pc):
        """Return the block key of an address inside the function (the inverse of `pc`)."""
        pc = hex(int(pc, 16)) if isinstance(pc, str) else hex(pc)
        if 'pc_base' in self.data:
            offset = int(pc, 16) - int(self.data['pc_base'], 16)
            if not 0 <= offset < 0x10000:
                raise ValueError('An address lies outside the function: ' + pc)
            return format(offset, '04x')
        if not pc.startswith(self.data['pc_prefix']):
            raise ValueError('An address lies outside the function: ' + pc)
        return pc[len(self.data['pc_prefix']):]

    def qualified(self, module, symbol=None):
        result = self.generated_module + '.' + module
        return result if symbol is None else result + '.' + symbol

    def telescope(self):
        return ' `{!islaG Sigma} `{!threadG} (args : ' + self.args_type + ') (returnAddress : Z)'

    @property
    def charged(self):
        """Profile `charged: true`: the code is charged and every entry owns its step budget."""
        return self.data.get('charged') is True

    def code(self):
        """The selected code premise row: `charged_code` of a charged profile, else `selected_code`."""
        return self.data['charged_code' if self.charged else 'selected_code']

    def selected_import(self):
        return 'Require Import ' + self.code()['module'] + '.\n'

    def selected_premise(self):
        return self.code()['premise']


STEP_BUDGET_MODULE = 'ZesuSsz.Automation2.StepBudget'


def budget_import(profile):
    """The step-budget library import of a charged profile's declarations; empty otherwise."""
    return 'Require Import ' + STEP_BUDGET_MODULE + '.\n' if profile.get('charged') is True else ''


def call_premise(profile, call):
    """The callee spec premise of a call row, `instr_pre CALLEE (SPEC)%I`, and its modules.

    A charged profile hands the callee its budget: the row's `charged_spec` (in `charged_spec_module`),
    a spec that states the budget itself, or `step_budget (K) ∗ SPEC` with K the callee's registry
    budget (tools/block/budgets.py); a K over the call's arguments needs a `charged_spec`."""
    if profile.get('charged') is not True:
        return ('instr_pre ' + call['callee_pc'] + ' (' + call['spec_module'] + '.' + call['spec'] + ')%I',
                [call['spec_module']])
    if call.get('charged_spec'):
        return ('instr_pre ' + call['callee_pc'] + ' (' + call['charged_spec_module'] + '.'
                + call['charged_spec'] + ')%I', [call['charged_spec_module'], STEP_BUDGET_MODULE])
    from budgets import callee_budget
    budget = callee_budget(int(call['callee_pc'], 16))
    if '{argv:' in budget.text():
        raise ValueError('The budget of the callee at %s reads its arguments: the call row needs a '
                         'charged_spec' % call['callee_pc'])
    return ('instr_pre ' + call['callee_pc'] + ' (step_budget (' + budget.text() + ') ∗ '
            + call['spec_module'] + '.' + call['spec'] + ')%I', [call['spec_module'], STEP_BUDGET_MODULE])


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
    """Rewrite a table keyed by symbol and offset to the form the renderers read.

    The table names its function's ELF `symbol`. A block is `+0xOFFSET` from that symbol;
    an address field (a call site, a callee, a return instruction) is `+0xOFFSET` or
    `SYMBOL+0xOFFSET`. Blocks become 4-digit offset keys (`0014`), which the generated
    names use; `pc_base` is the symbol's address; address fields become absolute
    addresses. A relink then changes only the symbol table: neither the design table
    nor any generated name."""
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

    def offset_key(text):
        if not text.startswith('+'):
            raise ValueError('A block of the function is an offset from its symbol: ' + text)
        offset = absolute(text) - base
        if not 0 <= offset < 0x10000:
            raise ValueError('A block offset needs at most 4 hex digits: ' + text)
        return format(offset, '04x')

    def walk(value, key=None):
        if isinstance(value, dict):
            return {(offset_key(k) if isinstance(k, str) and k.startswith('+') else k): walk(v, k)
                    for k, v in value.items()}
        if isinstance(value, list):
            return [walk(item, key) for item in value]
        if isinstance(value, str) and key in ADDRESS_FIELDS:
            return hex(absolute(value))
        if isinstance(value, str) and key in BLOCK_LISTS:
            return offset_key(value)
        if isinstance(value, str) and value.startswith('+0x'):
            return offset_key(value)
        return value

    resolved = walk({key: value for key, value in data.items() if key != 'symbol'})
    resolved.update(symbol=data['symbol'], pc_base=hex(base))
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
    """(key, design) per function-return design. One site keeps the plain names
    `fp_machineReturn` / `FunctionReturn*`; several sites suffix each name with the return
    instruction's block key."""
    designs = function_returns(profile)
    if len(designs) <= 1:
        return [('', design) for design in designs]
    return [(profile.key(design['return_instruction_pc']), design) for design in designs]


RETURN_CASE = 'function_return'


def return_case(package):
    """The case name (RESULT.json `pc`) of a return package: `function_return` for the one
    return site, `function_return_<package>` for a return site's block key or a tail call's
    `Tail<key>` (render_function_callers.exit_package)."""
    return RETURN_CASE + ('_' + package if package else '')


def return_site(sites, start, end):
    """The suffix of the return site inside [start, end); None if none lies there."""
    if len(sites) <= 1:
        return sites[0][0] if sites else ''   # One package serves every return block.
    inside = [suffix for suffix, design in sites
              if end is not None and start <= int(design['return_instruction_pc'], 0) < end]
    return inside[0] if len(inside) == 1 else None


def tail_callees(profile, start, end):
    """The callee addresses of the `tail_calls` rows whose call site lies in [start, end). A
    block whose successors are all among them exits as a return block does (exit_package)."""
    return {int(call['callee_pc'], 16) for call in profile.get('tail_calls', [])
            if start <= int(call['call_site_pc'], 16) < end}


def exit_package(profile, sites, start, end):
    """The return package suffix of a block without successors: its tail call's
    `Tail<key>` package, else its function-return site (return_site). Its case is
    return_case of that suffix."""
    tails = [call for call in profile.get('tail_calls', []) if start <= int(call['call_site_pc'], 16) < end]
    if tails:
        return 'Tail' + profile.key(tails[0]['call_site_pc'])
    return return_site(sites, start, end)


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
            + budget_import(profile)
            + 'Local Open Scope Z_scope.\n')


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
            + budget_import(profile)
            + 'Local Open Scope Z_scope.\n')
