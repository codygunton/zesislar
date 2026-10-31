"""Bind installed import resolution to the pinned coqdep executable."""
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

from check_data_only_lemmas import rocq_commands


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require_imports(words, origin=None):
    """Preserve Require syntax and exclude its import-category modifier."""
    if words[:1] == ['Require']:
        index, prefix = 0, ''
    elif words[:1] == ['From'] and len(words) > 2 and words[2] == 'Require':
        index, prefix = 2, words[1]
    else:
        return None
    start = index + 1
    if start < len(words) and words[start] in {'Import', 'Export'}:
        start += 1
    # The pinned compiler validates the modifier itself.
    if start < len(words) and words[start] == '(':
        try:
            end = words.index(')', start + 1)
        except ValueError:
            raise ValueError('An import category modifier is incomplete.')
        if end == start + 1 or '(' in words[start + 1:end]:
            raise ValueError('An import category modifier is unsupported.')
        start = end + 1
    result = []
    for raw in words[start:]:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", raw):
            raise ValueError('An import uses unsupported library-name syntax at ' +
                             str(origin or '<source text>') + ': ' + repr(raw))
        module = prefix + '.' + raw if prefix else raw
        result.append({'module': module, 'statement': ' '.join(words[:start] + [raw]) + '.\n'})
    return result


class InstalledMappings:
    def __init__(self, flags, *, coqdep=None, receipt_dir=None):
        self.roots, self.entries, self.requests, self.resolutions = [], [], {}, {}
        self.receipt_dir = Path(receipt_dir) if receipt_dir is not None else None
        self.coqdep = Path(coqdep) if coqdep is not None else Path(os.environ['OPAM_SWITCH_PREFIX']) / 'bin/coqdep'
        if not self.coqdep.is_file():
            raise ValueError('The pinned coqdep executable is absent.')
        self.tool_sha256 = digest(self.coqdep)
        self.flags = ['-boot', '-dyndep', 'no']
        self.scanned_sources = False
        self.source_records = {}
        self.seed_snapshot = None
        index = 0
        while index < len(flags):
            flag = flags[index]
            if flag in {'-Q', '-R'}:
                if index + 2 >= len(flags):
                    raise ValueError('An actual compiler mapping is incomplete.')
                root = Path(flags[index + 1]).resolve()
                prefix = flags[index + 2]
                self.flags.extend([flag, str(root), prefix])
                row = {'flag': flag, 'root': str(root), 'prefix': prefix}
                if row not in self.roots:
                    self.roots.append(row)
                    if root.is_dir():
                        for obj in sorted(root.rglob('*.vo')):
                            relative = obj.relative_to(root).with_suffix('').parts
                            canonical = '.'.join(([prefix] if prefix else []) + list(relative))
                            self.entries.append({'mapping': row, 'canonical': canonical,
                                                 'source': obj.with_suffix('.v'), 'object': obj})
                index += 3
            elif flag in {'-I', '-coqlib'}:
                if index + 1 >= len(flags):
                    raise ValueError('An actual compiler path flag is incomplete.')
                self.flags.extend([flag, flags[index + 1]])
                index += 2
            else:
                index += 1

    def register_source(self, source, origin=None):
        identity = {'path': str(origin), 'sha256': digest(origin)} if origin is not None else {
            'text_sha256': hashlib.sha256(source.encode()).hexdigest()}
        if origin is not None and self.source_records.get(str(origin),{}).get('source')==identity:
            return
        source_requests=[]
        for command in rocq_commands(source):
            words = [word for word, _ in command]
            requests = require_imports(words, origin)
            if requests is None:
                continue
            for request in requests:
                module, statement = request['module'], request['statement']
                source_requests.append(request)
                self.register_request(module, statement, identity)

        if origin is not None:self.source_records[str(origin)]={'source':identity,'requests':source_requests}

    def register_request(self, module, statement, origin):
        rows = self.requests.setdefault(module, [])
        flags = self.dependency_flags(origin)
        if not any(row['statement'] == statement and self.dependency_flags(row['origin']) == flags for row in rows):
            rows.append({'statement': statement, 'origin': origin})
            self.resolutions.pop(module, None)

    def scan_sources(self):
        if not self.scanned_sources:
            self.scanned_sources = True
            for path in sorted({entry['source'] for entry in self.entries if entry['source'].is_file()}):
                self.register_source(path.read_text(), path)

    def _find_request(self, module):
        if module in self.requests:
            return self.requests[module]
        if any(row['canonical'] == module for row in self.entries):
            return [{'statement': 'Require Import ' + module + '.\n',
                     'origin': {'fully_qualified_graph_module': module}}]
        self.scan_sources()
        if module not in self.requests:
            raise ValueError('An import has no bound source syntax or canonical installed name: ' + module)
        return self.requests[module]

    def dependency_flags(self, origin):
        """Resolve Sail sibling imports in their bound source context only."""
        flags = list(self.flags)
        if not origin.get('path'):
            return flags
        source = Path(origin['path']).resolve()
        for row in self.roots:
            if row['prefix'] != 'SailStdpp' or row['flag'] != '-Q':
                continue
            if not source.is_relative_to(row['root']):
                continue
            if digest(source) != origin['sha256']:
                raise ValueError('The dependency request source changed.')
            for index in range(len(flags) - 2):
                if flags[index:index + 3] == ['-Q', row['root'], 'SailStdpp']:
                    flags[index] = '-R'
        return flags

    def _query(self, module, request):
        if digest(self.coqdep) != self.tool_sha256:
            raise ValueError('The pinned coqdep executable changed.')
        flags = self.dependency_flags(request['origin'])
        temporary = tempfile.TemporaryDirectory() if self.receipt_dir is None else None
        directory = Path(temporary.name) if temporary else self.receipt_dir
        directory.mkdir(parents=True, exist_ok=True)
        key = hashlib.sha256(json.dumps([module, request, flags], sort_keys=True).encode()).hexdigest()
        source = directory / ('resolve-' + key + '.v')
        source.write_text(request['statement'])
        argv = [str(self.coqdep), *flags, str(source)]
        environment = dict(os.environ, COQPATH='', LANG='C', LC_ALL='C', LC_CTYPE='C')
        for name in ['COQLIB', 'COQBIN', 'ROCQPATH', 'ROCQCORELIB', 'ROCQSTDLIB']:
            environment.pop(name, None)
        reply = subprocess.run(argv, cwd=directory, env=environment, capture_output=True, text=True)
        receipt = {'schema': 'compiled-library.coqdep-resolution.v1', 'module': module,
                   'request': request, 'tool': {'path': str(self.coqdep), 'sha256': self.tool_sha256},
                   'argv': argv, 'COQPATH': '', 'source_sha256': digest(source),
                   'returncode': reply.returncode, 'stdout': reply.stdout, 'stderr': reply.stderr}
        if self.receipt_dir is not None:
            (directory / ('resolve-' + key + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
        try:
            if reply.returncode or reply.stderr:
                if 'module-not-found' in reply.stderr:
                    raise ValueError('A compiled import has no actual installed mapping: ' + module)
                raise ValueError('Pinned coqdep reported an ambiguous or unsupported import: ' + module)
            choices = set()
            for line in reply.stdout.replace('\\\n', ' ').splitlines():
                if ':' not in line:
                    continue
                lhs, rhs = line.split(':', 1)
                if not any(word.endswith('.vo') for word in shlex.split(lhs)):
                    continue
                choices.update(Path(word).absolute() for word in shlex.split(rhs) if word.endswith('.vo'))
            if len(choices) != 1:
                raise ValueError('Pinned coqdep did not return one physical library: ' + module)
            obj = choices.pop()
            if not obj.is_file():
                raise ValueError('The compiler-resolved library object is absent: ' + module)
            entries = [entry for entry in self.entries if entry['object'].absolute() == obj]
            if not entries:
                raise ValueError('The compiler-resolved object is outside the indexed mappings: ' + module)
            return entries[0], request
        finally:
            if temporary is not None:
                temporary.cleanup()

    def resolve(self, module):
        if module in self.resolutions:
            return self.resolutions[module]['source']
        from mapping_snapshot import answer
        cached=answer(self,module)
        if cached is not None:
            self.resolutions[module]=cached
            return cached['source']
        answers = [self._query(module, request) for request in self._find_request(module)]
        objects = {entry['object'].resolve() for entry, _ in answers}
        if len(objects) != 1:
            raise ValueError('Source contexts resolve the same graph name ambiguously: ' + module)
        entry = answers[0][0]
        self.resolutions[module] = {'source': entry['source'], 'object': entry['object'],
            'canonical': entry['canonical'], 'requests': [request['statement'] for _, request in answers]}
        return entry['source']

    def inventory(self):
        return {'schema': 'compiled-library.tool-resolved-mappings.v1', 'roots': self.roots,
                'resolver': {'path': str(self.coqdep), 'sha256': self.tool_sha256},
                'modules': [{'logical_module': entry['canonical'], 'mapping': entry['mapping'],
                             'source': str(entry['source']), 'source_present': entry['source'].is_file(),
                             'object': str(entry['object'])} for entry in self.entries],
                'resolutions': [{'requested_module': name, 'canonical_module': row['canonical'],
                                 'source': str(row['source']), 'object': str(row['object']),
                                 'requests': row['requests']}
                                for name, row in sorted(self.resolutions.items())]}
