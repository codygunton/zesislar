#!/usr/bin/env python3
"""Evaluate raw Isla events without proof execution or target-specific knowledge.

The result is untrusted input for later block proofs. Conditions remain explicit.
Captured proof states never supply input bindings.
"""
from dataclasses import dataclass, field
import hashlib
import json
import re


@dataclass(frozen=True)
class Expr:
    op: str
    args: tuple = ()
    width: int | None = None
    value: int | str | bool | None = None

    def to_dict(self):
        result = {'op': self.op}
        if self.width is not None:
            result['width'] = self.width
        if self.value is not None:
            result['value'] = self.value
        if self.args:
            result['args'] = [arg.to_dict() for arg in self.args]
        return result

    @classmethod
    def from_dict(cls, value):
        return cls(value['op'], tuple(cls.from_dict(a) for a in value.get('args', [])),
                   value.get('width'), value.get('value'))

    def coq(self):
        """Render supported terms. Reject unknown inputs and unresolved reads."""
        if self.op == 'input':
            text = str(self.value)
            if re.fullmatch(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*|_", text):
                return text
            return '(' + text + ')'
        if self.op == 'bits':
            return f'(BV {self.width}%N {self.value}%Z)'
        if self.op == 'bool':
            return 'true' if self.value else 'false'
        rendered = [arg.coq() for arg in self.args]
        binary = {'bvadd': 'bv_add', 'bvsub': 'bv_sub', 'bvmul': 'bv_mul',
                  'bvand': 'bv_and', 'bvor': 'bv_or', 'bvxor': 'bv_xor',
                  'bvshl': 'bv_shiftl', 'bvlshr': 'bv_shiftr', 'bvashr': 'bv_ashiftr',
                  'bvnot': 'bv_not', 'bvneg': 'bv_opp'}
        if self.op in binary:
            return f'({binary[self.op]} {" ".join(rendered)})'
        if self.op == 'concat':
            return f'(bv_concat {self.width}%N {" ".join(rendered)})'
        if self.op == 'extract':
            return f'(bv_extract {self.value}%N {self.width}%N {rendered[0]})'
        if self.op in ('zero_extend', 'sign_extend'):
            name = 'bv_zero_extend' if self.op == 'zero_extend' else 'bv_sign_extend'
            return f'({name} {self.width}%N {rendered[0]})'
        if self.op == '=':
            return f'(bool_decide ({rendered[0]} = {rendered[1]}))'
        if self.op == 'not':
            return f'(negb {rendered[0]})'
        if self.op in ('and', 'or'):
            name = 'andb' if self.op == 'and' else 'orb'
            result = rendered[-1]
            for term in reversed(rendered[:-1]):
                result = f'({name} {term} {result})'
            return result
        if self.op == 'ite':
            return f'(if {rendered[0]} then {rendered[1]} else {rendered[2]})'
        if self.op in ('bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge'):
            interpretation = 'bv_signed' if self.op.startswith('bvs') else 'bv_unsigned'
            relation = {'lt': '<', 'le': '<=', 'gt': '>', 'ge': '>='}[self.op[-2:]]
            return f'(bool_decide (({interpretation} {rendered[0]} {relation} {interpretation} {rendered[1]})%Z))'
        if self.op == 'array_byte':
            return f'(List.nth {self.value}%nat {rendered[0]} (BV 8%N 0%Z))'
        raise ValueError('The expression cannot render as Coq: ' + self.op)


def input_expr(coq_text, width=64):
    return Expr('input', width=width, value=coq_text)


def bits(value, width):
    if width <= 0:
        raise ValueError('A bitvector width must be positive')
    return Expr('bits', width=width, value=int(value) % (1 << width))


def boolean(value):
    return Expr('bool', value=bool(value))


def _signed(value, width):
    return value - (1 << width) if value >= (1 << (width - 1)) else value


def operation(op, *args, width=None, value=None):
    """Fold concrete operations and basic identities without a solver."""
    bit_binary = {'bvadd', 'bvsub', 'bvmul', 'bvand', 'bvor', 'bvxor', 'bvshl',
                  'bvlshr', 'bvashr', 'bvult', 'bvule', 'bvugt', 'bvuge',
                  'bvslt', 'bvsle', 'bvsgt', 'bvsge'}
    if op in bit_binary and (args[0].width is None or args[0].width != args[1].width):
        raise UnsupportedEvent('expression-width:' + op)
    if op == 'extract' and (args[0].width is None or width is None or width <= 0 or value < 0 or value+width > args[0].width):
        raise UnsupportedEvent('expression-width:extract')
    if op in ('zero_extend', 'sign_extend') and (args[0].width is None or width < args[0].width):
        raise UnsupportedEvent('expression-width:' + op)
    if op == 'not':
        if args[0].op == 'bool':
            return boolean(not args[0].value)
        if args[0].op == 'not':
            return args[0].args[0]
    if op == '=' and args[0] == args[1]:
        return boolean(True)
    if op == '=' and all(a.op in ('bits', 'bool', 'enum') for a in args):
        return boolean(args[0] == args[1])
    if op in ('and', 'or'):
        decisive = op == 'or'
        if any(a == boolean(decisive) for a in args):
            return boolean(decisive)
        args = tuple(a for a in args if a != boolean(not decisive))
        if not args:
            return boolean(not decisive)
        if len(args) == 1:
            return args[0]
    if op == 'ite':
        if args[0].op == 'bool':
            return args[1] if args[0].value else args[2]
        if args[1] == args[2]:
            return args[1]
    if op in ('bvadd', 'bvsub', 'bvor', 'bvxor', 'bvshl', 'bvlshr', 'bvashr') and args[1].op == 'bits' and args[1].value == 0:
        return args[0]
    if op == 'bvadd' and args[0].op == 'bits' and args[0].value == 0:
        return args[1]
    if op == 'bvand' and args[1].op == 'bits':
        if args[1].value == (1 << args[1].width) - 1:
            return args[0]
        if args[1].value == 0:
            return args[1]
    if op == 'extract' and value == 0 and width == args[0].width:
        return args[0]
    if op in ('zero_extend', 'sign_extend') and width == args[0].width:
        return args[0]
    if op == 'extract' and args[0].op == 'extract':
        return operation('extract', args[0].args[0], width=width, value=value + args[0].value)
    if all(a.op == 'bits' for a in args):
        values = [a.value for a in args]
        x = values[0]
        y = values[1] if len(values) > 1 else None
        w = args[0].width
        target = width or w
        if op in ('bvadd', 'bvsub', 'bvmul', 'bvand', 'bvor', 'bvxor'):
            result = {'bvadd': lambda: x+y, 'bvsub': lambda: x-y, 'bvmul': lambda: x*y,
                      'bvand': lambda: x&y, 'bvor': lambda: x|y, 'bvxor': lambda: x^y}[op]()
            return bits(result, target)
        if op in ('bvshl', 'bvlshr', 'bvashr'):
            if y >= w:
                return bits(-1 if op == 'bvashr' and _signed(x, w) < 0 else 0, target)
            return bits((x << y) if op == 'bvshl' else ((_signed(x, w) if op == 'bvashr' else x) >> y), target)
        if op == 'bvnot':
            return bits(~x, target)
        if op == 'bvneg':
            return bits(-x, target)
        if op == 'extract':
            return bits(x >> value, target)
        if op in ('zero_extend', 'sign_extend'):
            return bits(_signed(x, w) if op == 'sign_extend' else x, target)
        if op == 'concat':
            return bits((x << args[1].width) | y, w + args[1].width)
        if op in ('bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge'):
            if op.startswith('bvs'):
                x, y = _signed(x, w), _signed(y, w)
            result = {'lt': lambda: x<y, 'le': lambda: x<=y, 'gt': lambda: x>y, 'ge': lambda: x>=y}[op[-2:]]()
            return boolean(result)
    if op == 'concat':
        width = sum(arg.width for arg in args)
        chunks = []
        def flatten(expr):
            if expr.op == 'concat':
                for arg in expr.args:
                    flatten(arg)
            else:
                chunks.append(expr)
        for arg in args:
            flatten(arg)
        if all(a.op == 'extract' for a in chunks):
            source = chunks[0].args[0]
            offset = 0
            for chunk in reversed(chunks):
                if chunk.args[0] != source or chunk.value != offset:
                    break
                offset += chunk.width
            else:
                if offset == source.width:
                    return source
    if width is None and op not in ('=', 'not', 'and', 'or', 'bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge'):
        width = args[1].width if op == 'ite' else args[0].width
    return Expr(op, tuple(args), width, value)


@dataclass(frozen=True)
class MemoryRegion:
    base: Expr
    bytes: tuple = ()
    byte_array: Expr | None = None
    length: Expr | int | None = None
    uninitialized: bool = False
    ownership_id: str | None = None
    minimum_length: int = 0

    def to_dict(self):
        result = {'base': self.base.to_dict(), 'bytes': [b.to_dict() for b in self.bytes]}
        if self.byte_array is not None:
            result['byte_array'] = self.byte_array.to_dict()
        if self.length is not None:
            result['length'] = self.length.to_dict() if isinstance(self.length, Expr) else self.length
        if self.uninitialized:
            result['uninitialized'] = True
        if self.ownership_id is not None:
            result['ownership_id'] = self.ownership_id
        if self.minimum_length:
            result['minimum_length'] = self.minimum_length
        return result


@dataclass(frozen=True)
class MemoryWrite:
    address: Expr
    value: Expr
    size: int
    mapped: bool = False
    result: Expr | None = None
    event_id: str | None = None
    provenance: dict | None = None
    ownership_id: str | None = None

    def to_dict(self):
        record = {'address': self.address.to_dict(), 'value': self.value.to_dict(),
                  'size': self.size, 'mapped': self.mapped}
        if self.result is not None:
            record['result'] = self.result.to_dict()
        if self.event_id is not None:
            record['event_id'] = self.event_id
        if self.provenance is not None:
            record['provenance'] = self.provenance
        if self.ownership_id is not None:
            record['ownership_id'] = self.ownership_id
        return record


@dataclass
class SymbolicState:
    registers: dict = field(default_factory=dict)
    memory: list = field(default_factory=list)
    conditions: list = field(default_factory=list)
    reports: list = field(default_factory=list)
    writes: list = field(default_factory=list)
    endianness: str = 'little'
    trace_count: int = 0
    retained_registers: dict = field(default_factory=dict)
    memory_disjoint: list = field(default_factory=list)
    register_writes: list | None = None

    def copy(self):
        return SymbolicState(dict(self.registers), list(self.memory), list(self.conditions),
                             list(self.reports), list(self.writes), self.endianness, self.trace_count,
                             dict(self.retained_registers), list(self.memory_disjoint),
                             list(self.register_writes) if self.register_writes is not None else None)

    def to_dict(self):
        result = {'schema': 1, 'registers': {k: v.to_dict() for k, v in sorted(self.registers.items())},
                'memory': [r.to_dict() for r in self.memory], 'writes': [w.to_dict() for w in self.writes],
                'conditions': [e.to_dict() for e in self.conditions], 'reports': self.reports,
                'endianness': self.endianness, 'trace_count': self.trace_count}
        if self.retained_registers:
            result['retained_registers'] = {k: v.to_dict() for k, v in sorted(self.retained_registers.items())}
        if self.memory_disjoint:
            result['memory_disjoint'] = [list(pair) for pair in self.memory_disjoint]
        if self.register_writes is not None:
            result['register_writes'] = [dict(write) for write in self.register_writes]
        return result


@dataclass
class TraceResult:
    state: SymbolicState
    status: str = 'complete'
    unsupported_event: str | None = None
    event_index: int | None = None
    path: tuple = ()

    def to_dict(self):
        result = {'state': self.state.to_dict(), 'status': self.status, 'path': list(self.path)}
        if self.unsupported_event is not None:
            result['unsupported_event'] = self.unsupported_event
        if self.event_index is not None:
            result['event_index'] = self.event_index
        return result


class UnsupportedEvent(ValueError):
    pass


@dataclass
class _PathBudget:
    limit: int
    paths: int = 1


TOKEN = re.compile(r'\s+|;[^\n]*|\(|\)|\|[^|]*\||"(?:\\.|[^"\\])*"|[^\s()]+')


def parse_trace(source):
    """Parse one raw Isla trace. Comments and strings cannot create events."""
    stack, roots = [], []
    for match in TOKEN.finditer(source):
        token = match.group()
        if token.isspace() or token.startswith(';'):
            continue
        if token == '(':
            child = []
            (stack[-1] if stack else roots).append(child)
            stack.append(child)
        elif token == ')':
            if not stack:
                raise ValueError('The trace has an unmatched closing parenthesis')
            stack.pop()
        else:
            (stack[-1] if stack else roots).append(token)
    if stack or len(roots) != 1 or not isinstance(roots[0], list) or not roots[0] or roots[0][0] != 'trace':
        raise ValueError('The source must contain one complete Isla trace')
    return roots[0]


def _name(value):
    if not isinstance(value, str):
        raise UnsupportedEvent('nonliteral-name')
    return value[1:-1] if value.startswith('|') and value.endswith('|') else value


def _fields(accessors):
    if accessors == 'nil':
        return []
    if not isinstance(accessors, list):
        raise UnsupportedEvent('register-accessor')
    result = []
    for accessor in accessors:
        if not isinstance(accessor, list) or len(accessor) != 3 or accessor[:2] != ['_', 'field']:
            raise UnsupportedEvent('register-accessor')
        result.append(_name(accessor[2]))
    return result


def _offset(address, base):
    def split(expr):
        if expr.op == 'bits':
            return None, expr.value
        if expr.op in ('bvadd', 'bvsub') and expr.args[1].op == 'bits':
            root, offset = split(expr.args[0])
            return root, offset + (expr.args[1].value if expr.op == 'bvadd' else -expr.args[1].value)
        return expr, 0
    a, x = split(address)
    b, y = split(base)
    if a != b or address.width != base.width:
        return None
    return (x-y) % (1 << address.width)


class _Evaluator:
    def __init__(self, state, path=(), instruction_index=0, trace_sha256=None):
        self.state, self.path = state, path
        self.env, self.types = {}, {}
        self.instruction_index = instruction_index
        self.event_index = 0
        self.status, self.unsupported = 'complete', None
        self.trace_sha256 = trace_sha256

    def clone(self, branch):
        result = _Evaluator(self.state.copy(), self.path + (branch,), self.instruction_index, self.trace_sha256)
        result.env, result.types = dict(self.env), dict(self.types)
        result.event_index = self.event_index
        return result

    def report(self, kind, **details):
        self.state.reports.append({'kind': kind, 'instruction_index': self.instruction_index,
                                   'event_index': self.event_index, 'path': list(self.path), **details})

    def register(self, key, width=64):
        if key not in self.state.registers:
            self.state.registers[key] = Expr('unknown_input', width=width, value='register:' + key)
            self.report('missing_register', register=key)
        return self.state.registers[key]

    def expression(self, raw):
        if isinstance(raw, str):
            if raw in self.env:
                return self.env[raw]
            if raw.startswith('#x'):
                return bits(int(raw[2:], 16), 4*(len(raw)-2))
            if raw.startswith('#b'):
                return bits(int(raw[2:], 2), len(raw)-2)
            if raw in ('true', 'false'):
                return boolean(raw == 'true')
            if raw.startswith('|'):
                return Expr('enum', value=_name(raw))
            raise UnsupportedEvent('expression:' + raw)
        if not raw:
            raise UnsupportedEvent('empty-expression')
        operator = raw[0]
        if isinstance(operator, list):
            if operator[:2] == ['_', 'extract'] and len(operator) == 4:
                high, low = map(int, operator[2:])
                return operation('extract', self.expression(raw[1]), width=high-low+1, value=low)
            if operator[:2] in (['_', 'zero_extend'], ['_', 'sign_extend']) and len(operator) == 3:
                arg = self.expression(raw[1])
                return operation(operator[1], arg, width=arg.width+int(operator[2]))
            raise UnsupportedEvent('indexed-expression:' + json.dumps(operator))
        if isinstance(operator, str) and operator.startswith('|') and len(raw) == 2:
            return self.register('.'.join([_name(operator), *_fields(raw[1])]))
        supported = {'=', 'not', 'and', 'or', 'ite', 'bvadd', 'bvsub', 'bvmul', 'bvand', 'bvor',
                     'bvxor', 'bvnot', 'bvneg', 'bvshl', 'bvlshr', 'bvashr', 'concat',
                     'bvult', 'bvule', 'bvugt', 'bvuge', 'bvslt', 'bvsle', 'bvsgt', 'bvsge'}
        if operator not in supported:
            raise UnsupportedEvent('expression:' + str(operator))
        args = [self.expression(arg) for arg in raw[1:]]
        expected = (1,) if operator in ('not', 'bvnot', 'bvneg') else ((3,) if operator == 'ite' else (2,))
        if operator not in ('and', 'or') and len(args) not in expected:
            raise UnsupportedEvent('expression-arity:' + operator)
        return operation(operator, *args)

    def condition(self, expression):
        if expression == boolean(False) or operation('not', expression) in self.state.conditions:
            self.status = 'infeasible'
        elif expression != boolean(True) and expression not in self.state.conditions:
            self.state.conditions.append(expression)

    def bind(self, raw, value):
        if isinstance(raw, str) and raw in self.types:
            old = self.env[raw]
            if old.op == 'local':
                self.substitute(old, value)
            else:
                self.condition(operation('=', old, value))
            self.env[raw] = value
        else:
            self.condition(operation('=', self.expression(raw), value))

    def substitute(self, old, value):
        """Resolve a trace declaration when a later read supplies its value."""
        def visit(expr):
            if expr == old:
                return value
            if not expr.args:
                return expr
            args = tuple(visit(arg) for arg in expr.args)
            return operation(expr.op, *args, width=expr.width, value=expr.value)
        self.env = {key: visit(expr) for key, expr in self.env.items()}
        self.state.registers = {key: visit(expr) for key, expr in self.state.registers.items()}
        self.state.retained_registers = {key: visit(expr) for key, expr in self.state.retained_registers.items()}
        self.state.writes = [MemoryWrite(visit(w.address), visit(w.value), w.size, w.mapped,
                                        visit(w.result) if w.result is not None else None,
                                        w.event_id, w.provenance, w.ownership_id) for w in self.state.writes]
        conditions, self.state.conditions = self.state.conditions, []
        for condition in conditions:
            self.condition(visit(condition))

    def register_event(self, kind, name, accessors, raw):
        key = '.'.join([_name(name), *_fields(accessors)])
        if kind == 'write-reg':
            def assignments(value, target):
                if isinstance(value, list) and value[:2] == ['_', 'struct']:
                    return [assignment for field_name, child in value[2:]
                            for assignment in assignments(child, target + '.' + _name(field_name))]
                return [(target, self.expression(value))]
            updates = assignments(raw, key)
            if self.state.register_writes is not None:
                self.state.register_writes.append({'key': key,
                    'event_id': f'{self.state.trace_count}:{self.instruction_index}:{self.event_index}',
                    'provenance': {'trace_sha256': self.trace_sha256,
                        'instruction_index': self.instruction_index, 'event_index': self.event_index,
                        'path': list(self.path)}})
            self.state.registers = {name: value for name, value in self.state.registers.items()
                                    if name != key and not name.startswith(key + '.')}
            self.state.registers.update(updates)
            if self.state.retained_registers:
                self.state.retained_registers = {name: value for name, value in self.state.retained_registers.items()
                                                if name != key and not name.startswith(key + '.')}
                self.state.retained_registers.update(updates)
            return
        if isinstance(raw, list) and raw[:2] == ['_', 'struct']:
            for field_name, field_value in raw[2:]:
                fields = [['_', 'field', name] for name in _fields(accessors)]
                self.register_event(kind, name, [*fields, ['_', 'field', field_name]], field_value)
            return
        if kind == 'read-reg':
            width = self.types[raw] if isinstance(raw, str) and raw in self.types else self.expression(raw).width
            self.bind(raw, self.register(key, width))
        else:
            value = self.expression(raw)
            self.condition(operation('=', self.register(key, value.width), value))

    def memory_byte(self, address):
        owners = []
        for region in self.state.memory:
            offset = _offset(address, region.base)
            length = region.length.value if isinstance(region.length, Expr) and region.length.op == 'bits' else region.length
            if offset is not None and region.ownership_id is not None and (offset < len(region.bytes) or
                    (isinstance(length, int) and offset < length) or offset < region.minimum_length):
                owners.append(region.ownership_id)
        for write in reversed(self.state.writes):
            offset = _offset(address, write.address)
            if offset is None:
                if owners and write.ownership_id is not None and all(
                        any(set(pair) == {owner, write.ownership_id} for pair in self.state.memory_disjoint)
                        for owner in owners):
                    continue
                self.report('ambiguous_memory_alias', address=address.to_dict(), write_address=write.address.to_dict())
                return Expr('unknown_read', (address,), 8)
            if 0 <= offset < write.size:
                if not write.mapped:
                    self.report('unknown_memory_mapping', address=address.to_dict(), write_address=write.address.to_dict())
                    return Expr('unknown_read', (address,), 8)
                position = offset if self.state.endianness == 'little' else write.size-offset-1
                return operation('extract', write.value, width=8, value=8*position)
        candidates, ambiguous_regions = [], []
        for region in self.state.memory:
            offset = _offset(address, region.base)
            if offset is None:
                ambiguous_regions.append(region)
                continue
            if offset < 0:
                continue
            length = region.length
            length = length.value if isinstance(length, Expr) and length.op == 'bits' else length
            if offset < len(region.bytes):
                candidates.append((region.bytes[offset], region.ownership_id))
            elif region.byte_array is not None and ((isinstance(length, int) and offset < length) or offset < region.minimum_length):
                candidates.append((Expr('array_byte', (region.byte_array,), 8, offset), region.ownership_id))
            elif region.byte_array is not None and isinstance(length, Expr):
                self.report('unknown_memory_bound', address=address.to_dict(), length=length.to_dict())
                return Expr('unknown_read', (address, region.byte_array, length), 8)
        def separated(region):
            return candidates and all(owner is not None and region.ownership_id is not None and
                                      any(set(pair) == {owner, region.ownership_id} for pair in self.state.memory_disjoint)
                                      for _, owner in candidates)
        ambiguous_regions = [region for region in ambiguous_regions if not separated(region)]
        if ambiguous_regions:
            self.report('ambiguous_memory_alias', address=address.to_dict(),
                        region_bases=[region.base.to_dict() for region in ambiguous_regions])
            return Expr('unknown_read', (address,), 8)
        if candidates and all(value == candidates[0][0] for value, _ in candidates):
            return candidates[0][0]
        self.report('ambiguous_memory_alias' if candidates else 'unknown_memory_read', address=address.to_dict())
        return Expr('unknown_read', (address,), 8)

    def mapped_byte(self, address):
        """A store cannot allocate initial memory or establish a missing bound."""
        for region in self.state.memory:
            offset = _offset(address, region.base)
            if offset is None:
                continue
            length = region.length
            length = length.value if isinstance(length, Expr) and length.op == 'bits' else length
            if 0 <= offset < len(region.bytes) or ((region.byte_array is not None or region.uninitialized)
                                                  and (isinstance(length, int) and 0 <= offset < length or 0 <= offset < region.minimum_length)):
                return True
        return False

    def memory_read(self, address, size):
        chunks = [self.memory_byte(operation('bvadd', address, bits(index, address.width))) for index in range(size)]
        if self.state.endianness == 'little':
            chunks.reverse()
        result = chunks[0]
        for chunk in chunks[1:]:
            result = operation('concat', result, chunk)
        return result

    def run(self, events, budget=None):
        current = [self]
        for event in events:
            following = []
            for evaluator in current:
                if evaluator.status != 'complete':
                    following.append(evaluator)
                    continue
                evaluator.event_index += 1
                try:
                    if not isinstance(event, list) or not event:
                        raise UnsupportedEvent('malformed-event')
                    kind, *args = event
                    if kind == 'cases':
                        if len(args) < 2:
                            raise UnsupportedEvent('cases-arity')
                        traces = args[1:]
                        allowed = len(traces)
                        if budget is not None:
                            allowed = min(allowed, budget.limit-budget.paths+1)
                            budget.paths += allowed-1
                        for index, trace in enumerate(traces[:allowed]):
                            if not isinstance(trace, list) or not trace or trace[0] != 'trace':
                                raise UnsupportedEvent('cases-child')
                            following.extend(evaluator.clone(index).run(trace[1:], budget))
                        if allowed < len(traces):
                            limited = evaluator.clone(allowed)
                            limited.status = 'path_limit'
                            limited.report('path_limit', max_paths=budget.limit,
                                           discarded_alternatives=len(traces)-allowed)
                            following.append(limited)
                        continue
                    evaluator.event(kind, args)
                except (UnsupportedEvent, ValueError, TypeError, IndexError) as error:
                    evaluator.status, evaluator.unsupported = 'unsupported', str(error)
                    evaluator.report('unsupported_event', event=event[0] if event else 'malformed-event', detail=str(error))
                following.append(evaluator)
            current = following
        return current

    def event(self, kind, args):
        if kind == 'declare-const':
            name, ty = args
            width = int(ty[2]) if isinstance(ty, list) and ty[:2] == ['_', 'BitVec'] else None
            if width is None and ty != 'Bool':
                raise UnsupportedEvent('declare-type:' + str(ty))
            self.types[name] = width
            self.env[name] = Expr('local', width=width, value=f'{self.state.trace_count}:{name}')
        elif kind == 'define-const':
            name, raw = args
            self.env[name] = self.expression(raw)
        elif kind in ('read-reg', 'write-reg', 'assume-reg'):
            self.register_event(kind, *args)
        elif kind in ('assert', 'assume'):
            self.condition(self.expression(args[0]))
        elif kind == 'read-mem':
            target, access, raw_address, raw_size = args
            if _name(access) != 'Read_plain':
                raise UnsupportedEvent('read-mem-kind:' + _name(access))
            self.bind(target, self.memory_read(self.expression(raw_address), _size(raw_size)))
        elif kind == 'write-mem':
            target, access, raw_address, raw_value, raw_size = args
            if _name(access) != 'Write_plain':
                raise UnsupportedEvent('write-mem-kind:' + _name(access))
            address, value, size = self.expression(raw_address), self.expression(raw_value), _size(raw_size)
            if value.width != size*8:
                raise UnsupportedEvent('write-mem-width')
            mapped = all(self.mapped_byte(operation('bvadd', address, bits(index, address.width))) for index in range(size))
            # Islaris seq_step imposes no constraint on the result of WriteMem.
            result = Expr('write_result', (address, value), value=f'{self.state.trace_count}:{self.event_index}')
            event_id = f'{self.state.trace_count}:{self.instruction_index}:{self.event_index}'
            provenance = {'trace_sha256': self.trace_sha256, 'instruction_index': self.instruction_index,
                          'event_index': self.event_index, 'path': list(self.path)}
            self.state.writes.append(MemoryWrite(address, value, size, mapped, result, event_id, provenance))
            self.bind(target, result)
        elif kind == 'branch-address':
            self.expression(args[0])
        elif kind in ('cycle', 'define-enum'):
            return
        else:
            raise UnsupportedEvent(kind)


def _size(raw):
    if not isinstance(raw, str) or not raw.isdigit() or int(raw) <= 0:
        raise UnsupportedEvent('memory-size:' + str(raw))
    return int(raw)


def evaluate_trace(source, state, *, live_registers=None, instruction_index=0, max_paths=None):
    """Return every trace path. Unsupported events stop only their own path."""
    if state.endianness not in ('little', 'big'):
        raise ValueError('The memory endianness must be little or big')
    if max_paths is not None and (isinstance(max_paths, bool) or not isinstance(max_paths, int) or max_paths < 1):
        raise ValueError('The path limit must be a positive integer')
    initial = state.copy()
    initial.trace_count += 1
    budget = _PathBudget(max_paths) if max_paths is not None else None
    trace_sha256 = hashlib.sha256(source.encode()).hexdigest()
    evaluators = _Evaluator(initial, instruction_index=instruction_index, trace_sha256=trace_sha256).run(parse_trace(source)[1:], budget)
    results = []
    for evaluator in evaluators:
        if live_registers is not None:
            live = set(live_registers)
            evaluator.state.registers = {k: v for k, v in evaluator.state.registers.items() if k in live}
        results.append(TraceResult(evaluator.state, evaluator.status, evaluator.unsupported,
                                   evaluator.event_index if evaluator.status in ('unsupported', 'path_limit') else None,
                                   evaluator.path))
    return results


def evaluate_block(traces, state, *, live_registers=None):
    """Compose traces. Prune registers only after the final instruction."""
    results = [TraceResult(state.copy())]
    for index, source in enumerate(traces):
        following = []
        for result in results:
            if result.status != 'complete':
                following.append(result)
                continue
            for successor in evaluate_trace(source, result.state, instruction_index=index):
                successor.path = result.path + successor.path
                following.append(successor)
        results = following
    if live_registers is not None:
        live = set(live_registers)
        for result in results:
            result.state.registers = {k: v for k, v in result.state.registers.items() if k in live}
    return results
