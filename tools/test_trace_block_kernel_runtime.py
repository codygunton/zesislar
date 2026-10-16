import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace
import ast, copy, hashlib, importlib.util, json, os, sys
from pathlib import Path
MODULES = Path(__file__).resolve().parent / 'block'
sys.path.insert(0, str(MODULES))
import trace_block_kernel_runtime as k
W = Path(__file__).resolve().parents[1]

def ref(path):
    return dict(path=str(path.resolve()), sha256=hashlib.sha256(path.read_bytes()).hexdigest(), bytes=path.stat().st_size)

class KernelRuntimeTests(unittest.TestCase):

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def _patch(self, target, name, value):
        patcher = mock.patch.object(target, name, value)
        patcher.start()
        self.addCleanup(patcher.stop)

    def _runtime_request(self):
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        workspace = tmp_path / 'workspace'
        workspace.mkdir()
        evidence = tmp_path / 'evidence'
        evidence.mkdir()
        refs = {}
        for name in ['plugin', 'bridge', 'reader', 'writer']:
            p = workspace / name
            p.write_text(name)
            p.chmod(448)
            refs[name] = ref(p)
        pinned = tmp_path / 'pinned'
        pinned.mkdir()
        for name in ['coqc', 'ocamlc', 'pet']:
            (pinned / name).write_text(name)
        original_path = Path
        monkeypatch.setattr(k, 'Path', lambda *args: pinned if args == ('/home/cody/islaris/_opam/bin',) else original_path(*args))
        inventory = list(refs.values()) + [ref(pinned / name) for name in ['coqc', 'ocamlc', 'pet']]
        toolchain = workspace / 'TOOLCHAIN.json'
        toolchain.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
        req = dict(workspace=str(workspace), chunk_writer={key: refs['writer'][key] for key in ['path', 'sha256']}, observer_runtime=dict(surface_policy=k.POLICY, plugin={key: refs['plugin'][key] for key in ['path', 'sha256']}, bridge={key: refs['bridge'][key] for key in ['path', 'sha256']}, kernel_reader=refs['reader'], kernel_toolchain=ref(toolchain)))
        return (req, evidence, inventory)

    def test_legacy(self):
        self.assertTrue(not k.bounded_kernel({}))
        self.assertTrue(k.prepare_kernel_environment({}, Path('/unused')) == ({}, None))
        self.assertTrue(k.snapshot_command({}) == '1: ltac2:(trace_block_snapshot "residual").')
        self.assertTrue(k.loaded_kernel_runtime(None, {}) is None)

    def test_policy(self):
        with self.assertRaises(ValueError):
            k.bounded_kernel(dict(observer_runtime=dict(surface_policy='unknown')))

    def test_bound_runtime(self):
        runtime_request = self._runtime_request()
        req, evidence, _ = runtime_request
        env, b = k.prepare_kernel_environment(req, evidence)
        manifest = json.loads(Path(env['ZESU_TRACE_KERNEL_MANIFEST']).read_text())
        self.assertTrue(set(manifest) == {'schema', 'reader', 'toolchain_ref'})
        for key in ['reader', 'toolchain_ref']:
            row = manifest[key]
            self.assertTrue(not Path(row['path']).is_absolute())
            self.assertTrue(hashlib.sha256((evidence / row['path']).read_bytes()).hexdigest() == row['sha256'])
        self.assertTrue(b['surface_policy'] == k.POLICY)
        self.assertTrue(k.snapshot_command(req) == '1: ltac2:(trace_bounded_snapshot "residual").')
        self.assertTrue(k.snapshot_command(req, 'all:') == 'all: ltac2:(trace_bounded_snapshot "residual").')

    def test_invalid_runtime_1(self):
        change = 'reader_hash'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_2(self):
        change = 'reader_size'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_3(self):
        change = 'reader_outside'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_4(self):
        change = 'missing_plugin'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_5(self):
        change = 'missing_pet'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_6(self):
        change = 'duplicate'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def test_invalid_runtime_7(self):
        change = 'self'
        tmp_path = self.root
        runtime_request = self._runtime_request()
        req, evidence, inventory = runtime_request
        if change == 'reader_hash':
            req['observer_runtime']['kernel_reader']['sha256'] = '0' * 64
        elif change == 'reader_size':
            req['observer_runtime']['kernel_reader']['bytes'] += 1
        elif change == 'reader_outside':
            p = tmp_path / 'outside'
            p.write_text('outside')
            req['observer_runtime']['kernel_reader'] = ref(p)
        else:
            p = Path(req['observer_runtime']['kernel_toolchain']['path'])
            if change == 'missing_plugin':
                inventory = inventory[1:]
            elif change == 'missing_pet':
                inventory = inventory[:-1]
            elif change == 'duplicate':
                inventory += inventory[:1]
            elif change == 'self':
                inventory += [ref(p)]
            p.write_text(json.dumps(dict(schema=1, artifacts=inventory)))
            req['observer_runtime']['kernel_toolchain'] = ref(p)
        with self.assertRaises(ValueError):
            k.prepare_kernel_environment(req, evidence)

    def _query(self):
        tmp_path = self.root
        p = tmp_path / 'query.json'
        status = dict(schema=1, complete=False, diagnostic_errors=63, unrecorded_errors=22, hand_trials=dict(started=8, accepted=6, refused=2, rolled_back=8), first_error=dict(phase='counter-envelope', error='injected'), first_unrecorded_error=dict(phase='capture-error-output', capture_error='first', logging_error='second'))
        raw = dict(accepted=True, feedback=[dict(level=3, message='- : string =\n"' + json.dumps(status) + '"')], retained_state_hash_unchanged=True, retained_state_check=dict(method='Pet.state_hash', before=5, after=5))
        p.write_text(json.dumps(raw))
        return (p, raw)

    def test_actual_status(self):
        query = self._query()
        p, _ = query
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        value = k.parse_observer_status(result)
        self.assertTrue(value['hand_trials'] == dict(started=8, accepted=6, refused=2, rolled_back=8))
        self.assertTrue(value['complete'] is False)
        self.assertTrue(k.status_command(False) == 'Abort. Ltac2 Eval trace_bounded_status ().')
        self.assertTrue(k.status_command(True) == 'Ltac2 Eval trace_bounded_status ().')

    def test_bad_status_1(self):
        change = 'refused'
        query = self._query()
        p, raw = query
        if change == 'refused':
            raw['accepted'] = False
        elif change == 'mismatch':
            raw['retained_state_check']['after'] += 1
        elif change == 'duplicate':
            raw['feedback'] += raw['feedback'][-1:]
        elif change == 'contradiction':
            prefix = '- : string =\n"'
            value = json.loads(raw['feedback'][-1]['message'][len(prefix):-1])
            value['complete'] = True
            raw['feedback'][-1]['message'] = prefix + json.dumps(value) + '"'
        p.write_text(json.dumps(raw))
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        if change == 'hash':
            result['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            k.parse_observer_status(result)

    def test_bad_status_2(self):
        change = 'hash'
        query = self._query()
        p, raw = query
        if change == 'refused':
            raw['accepted'] = False
        elif change == 'mismatch':
            raw['retained_state_check']['after'] += 1
        elif change == 'duplicate':
            raw['feedback'] += raw['feedback'][-1:]
        elif change == 'contradiction':
            prefix = '- : string =\n"'
            value = json.loads(raw['feedback'][-1]['message'][len(prefix):-1])
            value['complete'] = True
            raw['feedback'][-1]['message'] = prefix + json.dumps(value) + '"'
        p.write_text(json.dumps(raw))
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        if change == 'hash':
            result['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            k.parse_observer_status(result)

    def test_bad_status_3(self):
        change = 'mismatch'
        query = self._query()
        p, raw = query
        if change == 'refused':
            raw['accepted'] = False
        elif change == 'mismatch':
            raw['retained_state_check']['after'] += 1
        elif change == 'duplicate':
            raw['feedback'] += raw['feedback'][-1:]
        elif change == 'contradiction':
            prefix = '- : string =\n"'
            value = json.loads(raw['feedback'][-1]['message'][len(prefix):-1])
            value['complete'] = True
            raw['feedback'][-1]['message'] = prefix + json.dumps(value) + '"'
        p.write_text(json.dumps(raw))
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        if change == 'hash':
            result['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            k.parse_observer_status(result)

    def test_bad_status_4(self):
        change = 'duplicate'
        query = self._query()
        p, raw = query
        if change == 'refused':
            raw['accepted'] = False
        elif change == 'mismatch':
            raw['retained_state_check']['after'] += 1
        elif change == 'duplicate':
            raw['feedback'] += raw['feedback'][-1:]
        elif change == 'contradiction':
            prefix = '- : string =\n"'
            value = json.loads(raw['feedback'][-1]['message'][len(prefix):-1])
            value['complete'] = True
            raw['feedback'][-1]['message'] = prefix + json.dumps(value) + '"'
        p.write_text(json.dumps(raw))
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        if change == 'hash':
            result['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            k.parse_observer_status(result)

    def test_bad_status_5(self):
        change = 'contradiction'
        query = self._query()
        p, raw = query
        if change == 'refused':
            raw['accepted'] = False
        elif change == 'mismatch':
            raw['retained_state_check']['after'] += 1
        elif change == 'duplicate':
            raw['feedback'] += raw['feedback'][-1:]
        elif change == 'contradiction':
            prefix = '- : string =\n"'
            value = json.loads(raw['feedback'][-1]['message'][len(prefix):-1])
            value['complete'] = True
            raw['feedback'][-1]['message'] = prefix + json.dumps(value) + '"'
        p.write_text(json.dumps(raw))
        result = dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']})
        if change == 'hash':
            result['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            k.parse_observer_status(result)

    def test_sdk_error_boundary_1(self):
        binding = None
        is_error = True
        reject = False
        tmp_path = self.root
        import asyncio, datetime
        from types import SimpleNamespace
        tree = ast.parse((MODULES / 'trace_block_mcp.py').read_text())
        run = next((node for node in tree.body if isinstance(node, ast.AsyncFunctionDef) and node.name == '_run'))
        call = next((node for node in run.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'call'))

        class Response:
            isError = is_error
            structuredContent = {'success': True}

            def model_dump(self, **kwargs):
                return {}

        class Client:

            async def call_tool(self, *args):
                return Response()
        scope = dict(datetime=datetime, save_json=lambda *args: {'path': 'operation.json', 'sha256': '0' * 64}, evidence_dir=tmp_path, operations=[], kernel_binding=binding, range_recorder=None)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[call], type_ignores=[])), 'call', 'exec'), scope)
        if reject:
            with self.assertRaisesRegex(RuntimeError, 'SDK error'):
                asyncio.run(scope['call'](Client(), 'test', {}))
        else:
            self.assertTrue(asyncio.run(scope['call'](Client(), 'test', {})) == {'success': True})

    def test_sdk_error_boundary_2(self):
        binding = {}
        is_error = True
        reject = True
        tmp_path = self.root
        import asyncio, datetime
        from types import SimpleNamespace
        tree = ast.parse((MODULES / 'trace_block_mcp.py').read_text())
        run = next((node for node in tree.body if isinstance(node, ast.AsyncFunctionDef) and node.name == '_run'))
        call = next((node for node in run.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'call'))

        class Response:
            isError = is_error
            structuredContent = {'success': True}

            def model_dump(self, **kwargs):
                return {}

        class Client:

            async def call_tool(self, *args):
                return Response()
        scope = dict(datetime=datetime, save_json=lambda *args: {'path': 'operation.json', 'sha256': '0' * 64}, evidence_dir=tmp_path, operations=[], kernel_binding=binding, range_recorder=None)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[call], type_ignores=[])), 'call', 'exec'), scope)
        if reject:
            with self.assertRaisesRegex(RuntimeError, 'SDK error'):
                asyncio.run(scope['call'](Client(), 'test', {}))
        else:
            self.assertTrue(asyncio.run(scope['call'](Client(), 'test', {})) == {'success': True})

    def test_sdk_error_boundary_3(self):
        binding = {}
        is_error = False
        reject = False
        tmp_path = self.root
        import asyncio, datetime
        from types import SimpleNamespace
        tree = ast.parse((MODULES / 'trace_block_mcp.py').read_text())
        run = next((node for node in tree.body if isinstance(node, ast.AsyncFunctionDef) and node.name == '_run'))
        call = next((node for node in run.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'call'))

        class Response:
            isError = is_error
            structuredContent = {'success': True}

            def model_dump(self, **kwargs):
                return {}

        class Client:

            async def call_tool(self, *args):
                return Response()
        scope = dict(datetime=datetime, save_json=lambda *args: {'path': 'operation.json', 'sha256': '0' * 64}, evidence_dir=tmp_path, operations=[], kernel_binding=binding, range_recorder=None)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[call], type_ignores=[])), 'call', 'exec'), scope)
        if reject:
            with self.assertRaisesRegex(RuntimeError, 'SDK error'):
                asyncio.run(scope['call'](Client(), 'test', {}))
        else:
            self.assertTrue(asyncio.run(scope['call'](Client(), 'test', {})) == {'success': True})

    def test_loaded_inventory_1(self):
        mutation = 'none'
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        root = tmp_path / 'proc'
        process = root / '123'
        process.mkdir(parents=True)
        fields = ['S'] + ['0'] * 19
        fields[19] = '456'
        (process / 'stat').write_text('123 (pet) ' + ' '.join(fields))
        pet = tmp_path / 'pet'
        pet.write_text('pet')
        (process / 'exe').symlink_to(pet)
        plugin = tmp_path / 'actual.cmxs'
        plugin.write_text('plugin')
        stat = plugin.stat()
        inode = stat.st_ino + (1 if mutation == 'inode' else 0)
        (process / 'maps').write_text('0000-0001 r-xp 0000 %02x:%02x %d %s\n' % (os.major(stat.st_dev), os.minor(stat.st_dev), inode, plugin))
        artifacts = [ref(pet)] + ([] if mutation == 'unlisted' else [ref(plugin)])
        original = Path
        monkeypatch.setattr(k, 'Path', lambda *args: root if args == ('/proc',) else original(*args))
        identity = dict(pid=123, start_ticks=457 if mutation == 'ticks' else 456)
        if mutation == 'none':
            result = k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)
            self.assertTrue(result['availability'] == 'observed' and len(result['mappings']) == 1)
        else:
            with self.assertRaises(ValueError):
                k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)

    def test_loaded_inventory_2(self):
        mutation = 'unlisted'
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        root = tmp_path / 'proc'
        process = root / '123'
        process.mkdir(parents=True)
        fields = ['S'] + ['0'] * 19
        fields[19] = '456'
        (process / 'stat').write_text('123 (pet) ' + ' '.join(fields))
        pet = tmp_path / 'pet'
        pet.write_text('pet')
        (process / 'exe').symlink_to(pet)
        plugin = tmp_path / 'actual.cmxs'
        plugin.write_text('plugin')
        stat = plugin.stat()
        inode = stat.st_ino + (1 if mutation == 'inode' else 0)
        (process / 'maps').write_text('0000-0001 r-xp 0000 %02x:%02x %d %s\n' % (os.major(stat.st_dev), os.minor(stat.st_dev), inode, plugin))
        artifacts = [ref(pet)] + ([] if mutation == 'unlisted' else [ref(plugin)])
        original = Path
        monkeypatch.setattr(k, 'Path', lambda *args: root if args == ('/proc',) else original(*args))
        identity = dict(pid=123, start_ticks=457 if mutation == 'ticks' else 456)
        if mutation == 'none':
            result = k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)
            self.assertTrue(result['availability'] == 'observed' and len(result['mappings']) == 1)
        else:
            with self.assertRaises(ValueError):
                k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)

    def test_loaded_inventory_3(self):
        mutation = 'ticks'
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        root = tmp_path / 'proc'
        process = root / '123'
        process.mkdir(parents=True)
        fields = ['S'] + ['0'] * 19
        fields[19] = '456'
        (process / 'stat').write_text('123 (pet) ' + ' '.join(fields))
        pet = tmp_path / 'pet'
        pet.write_text('pet')
        (process / 'exe').symlink_to(pet)
        plugin = tmp_path / 'actual.cmxs'
        plugin.write_text('plugin')
        stat = plugin.stat()
        inode = stat.st_ino + (1 if mutation == 'inode' else 0)
        (process / 'maps').write_text('0000-0001 r-xp 0000 %02x:%02x %d %s\n' % (os.major(stat.st_dev), os.minor(stat.st_dev), inode, plugin))
        artifacts = [ref(pet)] + ([] if mutation == 'unlisted' else [ref(plugin)])
        original = Path
        monkeypatch.setattr(k, 'Path', lambda *args: root if args == ('/proc',) else original(*args))
        identity = dict(pid=123, start_ticks=457 if mutation == 'ticks' else 456)
        if mutation == 'none':
            result = k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)
            self.assertTrue(result['availability'] == 'observed' and len(result['mappings']) == 1)
        else:
            with self.assertRaises(ValueError):
                k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)

    def test_loaded_inventory_4(self):
        mutation = 'inode'
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        root = tmp_path / 'proc'
        process = root / '123'
        process.mkdir(parents=True)
        fields = ['S'] + ['0'] * 19
        fields[19] = '456'
        (process / 'stat').write_text('123 (pet) ' + ' '.join(fields))
        pet = tmp_path / 'pet'
        pet.write_text('pet')
        (process / 'exe').symlink_to(pet)
        plugin = tmp_path / 'actual.cmxs'
        plugin.write_text('plugin')
        stat = plugin.stat()
        inode = stat.st_ino + (1 if mutation == 'inode' else 0)
        (process / 'maps').write_text('0000-0001 r-xp 0000 %02x:%02x %d %s\n' % (os.major(stat.st_dev), os.minor(stat.st_dev), inode, plugin))
        artifacts = [ref(pet)] + ([] if mutation == 'unlisted' else [ref(plugin)])
        original = Path
        monkeypatch.setattr(k, 'Path', lambda *args: root if args == ('/proc',) else original(*args))
        identity = dict(pid=123, start_ticks=457 if mutation == 'ticks' else 456)
        if mutation == 'none':
            result = k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)
            self.assertTrue(result['availability'] == 'observed' and len(result['mappings']) == 1)
        else:
            with self.assertRaises(ValueError):
                k.loaded_kernel_runtime(dict(artifacts=artifacts), identity)

    def test_guard_bridge_selection_1(self):
        bounded = False
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        sys.path.insert(1, str(MODULES))
        import trace_block_prepare as preparation
        import trace_block_bounded_prepare as bp
        from trace_block_filtered import typed_guards
        tree = ast.parse((MODULES / 'trace_block_mcp.py').read_text())
        node = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'filtered_environment'))
        plugin = tmp_path / 'plugin'
        plugin.write_text('plugin')
        coqpath = tmp_path / 'coqpath'
        bridge = coqpath / ('P0Bounded' if bounded else 'P0Filtered') / 'TraceObserver.vo'
        bridge.parent.mkdir(parents=True)
        bridge.write_text('bridge')
        ordinary = typed_guards()['Hooks.zesu_conjunct_head_if_enabled']
        command = ordinary.replace('trace_block_ltac1_guard', 'trace_bounded_ltac1_guard')
        descriptors = {'Hooks.zesu_conjunct_head_if_enabled': {'rule': 'ConjunctMatch', 'typed_guard': dict(command=command, sha256=hashlib.sha256(command.encode()).hexdigest(), semantics='switch-independent-discarded')}}
        _, payload = bp.bounded_guard_manifest(descriptors)
        manifest = tmp_path / 'GUARDS.json'
        manifest.write_bytes(payload)
        runtime = dict(plugin={key: ref(plugin)[key] for key in ['path', 'sha256']}, bridge={key: ref(bridge)[key] for key in ['path', 'sha256']}, coqpath=str(coqpath))
        if bounded:
            runtime.update(surface_policy=k.POLICY, kernel_reader={}, kernel_toolchain={})
        request = dict(workspace=str(tmp_path), observer_runtime=runtime, entry_descriptors=descriptors, guard_manifest={key: ref(manifest)[key] for key in ['path', 'sha256']})
        observed = []

        def old(*args):
            observed.append('legacy')
            return {'old': 'yes'}
        monkeypatch.setattr(preparation, 'guard_manifest_environment', old)
        scope = dict(Path=Path, hashlib=hashlib, bounded_kernel=k.bounded_kernel)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[node], type_ignores=[])), 'filtered_environment', 'exec'), scope)
        env = scope['filtered_environment'](request)
        self.assertTrue(observed == ([] if bounded else ['legacy']))
        self.assertTrue(('ZESU_TRACE_GUARD_MANIFEST' in env) == bounded)

    def test_guard_bridge_selection_2(self):
        bounded = True
        tmp_path = self.root
        monkeypatch = SimpleNamespace(setattr=self._patch)
        sys.path.insert(1, str(MODULES))
        import trace_block_prepare as preparation
        import trace_block_bounded_prepare as bp
        from trace_block_filtered import typed_guards
        tree = ast.parse((MODULES / 'trace_block_mcp.py').read_text())
        node = next((n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'filtered_environment'))
        plugin = tmp_path / 'plugin'
        plugin.write_text('plugin')
        coqpath = tmp_path / 'coqpath'
        bridge = coqpath / ('P0Bounded' if bounded else 'P0Filtered') / 'TraceObserver.vo'
        bridge.parent.mkdir(parents=True)
        bridge.write_text('bridge')
        ordinary = typed_guards()['Hooks.zesu_conjunct_head_if_enabled']
        command = ordinary.replace('trace_block_ltac1_guard', 'trace_bounded_ltac1_guard')
        descriptors = {'Hooks.zesu_conjunct_head_if_enabled': {'rule': 'ConjunctMatch', 'typed_guard': dict(command=command, sha256=hashlib.sha256(command.encode()).hexdigest(), semantics='switch-independent-discarded')}}
        _, payload = bp.bounded_guard_manifest(descriptors)
        manifest = tmp_path / 'GUARDS.json'
        manifest.write_bytes(payload)
        runtime = dict(plugin={key: ref(plugin)[key] for key in ['path', 'sha256']}, bridge={key: ref(bridge)[key] for key in ['path', 'sha256']}, coqpath=str(coqpath))
        if bounded:
            runtime.update(surface_policy=k.POLICY, kernel_reader={}, kernel_toolchain={})
        request = dict(workspace=str(tmp_path), observer_runtime=runtime, entry_descriptors=descriptors, guard_manifest={key: ref(manifest)[key] for key in ['path', 'sha256']})
        observed = []

        def old(*args):
            observed.append('legacy')
            return {'old': 'yes'}
        monkeypatch.setattr(preparation, 'guard_manifest_environment', old)
        scope = dict(Path=Path, hashlib=hashlib, bounded_kernel=k.bounded_kernel)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[node], type_ignores=[])), 'filtered_environment', 'exec'), scope)
        env = scope['filtered_environment'](request)
        self.assertTrue(observed == ([] if bounded else ['legacy']))
        self.assertTrue(('ZESU_TRACE_GUARD_MANIFEST' in env) == bounded)

    def test_observation_completeness_1(self):
        mutation = 'none'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_2(self):
        mutation = 'binding'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_3(self):
        mutation = 'loaded'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_4(self):
        mutation = 'runtime-error'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_5(self):
        mutation = 'session-error'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_6(self):
        mutation = 'changed'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_7(self):
        mutation = 'status'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_8(self):
        mutation = 'false-status'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_9(self):
        mutation = 'status-error'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_10(self):
        mutation = 'transport'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_observation_completeness_11(self):
        mutation = 'pet'
        args = dict(binding={}, loaded={'availability': 'observed'}, error=None, unchanged=True, status={'status': {'complete': True}}, status_error=None, ownership={'transport_closed_normally': True, 'owned_pet_exited': True})
        if mutation == 'binding':
            args['binding'] = None
        elif mutation == 'loaded':
            args['loaded'] = None
        elif mutation == 'runtime-error':
            args['loaded']['availability'] = 'unavailable'
        elif mutation == 'session-error':
            args['error'] = {'type': 'runtime-binding-error'}
        elif mutation == 'changed':
            args['unchanged'] = False
        elif mutation == 'status':
            args['status'] = None
        elif mutation == 'false-status':
            args['status']['status']['complete'] = False
        elif mutation == 'status-error':
            args['status_error'] = {'type': 'query-failure'}
        elif mutation == 'transport':
            args['ownership']['transport_closed_normally'] = False
        elif mutation == 'pet':
            args['ownership']['owned_pet_exited'] = False
        self.assertTrue(k.observation_complete(**args) is (mutation == 'none'))

    def test_actual_single_line_status(self):
        query = self._query()
        p, raw = query
        prefix = '- : string =\n"'
        status = json.loads(raw['feedback'][0]['message'][len(prefix):-1])
        raw['feedback'][0]['message'] = '- : string = "' + json.dumps(status) + '"'
        p.write_text(json.dumps(raw))
        value = k.parse_observer_status(dict(accepted=True, **{key: ref(p)[key] for key in ['path', 'sha256']}))
        self.assertTrue(value == status)
if __name__ == '__main__':
    unittest.main()
