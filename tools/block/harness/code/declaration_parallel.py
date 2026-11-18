"""Connect DAG workers to the bound Dune, guard, and physical receipt route."""
import json
import asyncio
from pathlib import Path
import subprocess
import sys
import uuid

from entry_chain import binding, read_bound, save
from declaration_dag import execute, ModuleCompileFailure
from declaration_outputs import private_target, publish
from coqc_findlib import compiler_environment


class GuardedAdapter:
    def __init__(self, runtime, workspace, output, manager, environment, recheck,
                 protected_compile, *, runner=subprocess.run):
        self.runtime = runtime
        self.workspace = Path(workspace).resolve()
        self.output = Path(output).resolve()
        self.manager = manager
        self.environment = compiler_environment(self.workspace, environment)
        self.recheck = recheck
        self.protected_compile = protected_compile
        self.runner = runner
        from declaration_parallel_plan import validate
        validate(runtime,self.workspace)
        self.spec = runtime['declaration_dag']
        self.protected = set(self.spec['protected_modules'])
        self.wrapper = self.workspace / runtime['coqc_wrapper']
        self.wrapper_binding = binding(self.wrapper)
        self.dune = self.spec['dune']
        read_bound(self.spec['graph'])
        self.recheck()

    def compile_private(self, module):
        if module in self.protected:
            raise ValueError('A protected declaration cannot enter a private worker.')
        self.check_tools()
        source = self.workspace / self.runtime['module_files'][module]
        source_binding = binding(source)
        directory = self.workspace / '.declaration-private' / uuid.uuid4().hex
        directory.mkdir(parents=True, mode=0o700)
        target = private_target(self.runtime, source_binding,
                                directory / source.with_suffix('.vo').name, self.workspace)
        # Use the same recorded Dune environment as snapshot publication.
        # Running Dune per worker mutates its shared lock and ambient load paths.
        command = [str(self.wrapper), *self.runtime['expected_mcp_flags'],
                   '-o', str(target), str(source)]
        environment = dict(self.environment)
        # Each physical compiler must reserve its own slot inside the aggregate.
        for name in ['ZESU_COQC_SCOPE', 'ZESU_COQC_RESERVATION']:
            environment.pop(name, None)
        environment.update(ZESU_MODULE_CLAIM_BYTES=str(self.spec['weights'][module]),
                           ZESU_MODULE_LIMIT_GIB='64')
        save(directory / 'LAUNCH.json', {'module': module, 'source': source_binding,
             'argv': command, 'cwd': str(directory), 'wrapper': self.wrapper_binding,
             'dune': self.dune, 'weight_bytes': self.spec['weights'][module],
             'compiler_slot_reused': False,
             'environment': {name: value for name, value in environment.items()
                             if name != 'ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY'},
             'authentication_key_recorded': False})
        with (directory / 'stdout').open('xb') as stdout, (directory / 'stderr').open('xb') as stderr:
            result = self.runner(command, cwd=directory, env=environment,
                                 stdout=stdout, stderr=stderr, check=False)
        if result.returncode:
            self.recheck()
            evidence = self.failed_compilation(module, source_binding, target)
            if evidence is not None:
                raise ModuleCompileFailure('The physical declaration compiler failed: ' + module, evidence)
            raise RuntimeError('A private declaration compiler failed: ' + module +
                               ' (retained launch: ' + str(directory) + ')')
        self.check_tools()
        if binding(source) != source_binding:
            raise ValueError('A private declaration source changed during compilation.')
        candidates = []
        invocations = Path(self.runtime['job_output']) / 'compiler-invocations'
        for path in invocations.glob('*/PHYSICAL-RESULT.json'):
            physical = json.loads(path.read_text())
            inputs = read_bound(physical['input'])
            if (inputs.get('source') == source_binding and
                    inputs.get('physical_argv', [])[-3:] == ['-o', str(target), str(source)]):
                candidates.append(binding(path))
        if len(candidates) != 1:
            raise ValueError('A private declaration lacks one exact physical compiler result.')
        return {'module': module, 'source': source_binding, 'private_object': binding(target),
                'physical_result': candidates[0], 'launch': binding(directory / 'LAUNCH.json'),
                'stdout': binding(directory / 'stdout'), 'stderr': binding(directory / 'stderr')}

    def failed_compilation(self, module, source, target=None):
        # Only a recorded normal coqc error permits independent dispatch.
        # Guard refusals, signals, missing records, and identity errors halt it.
        from compiler_snapshot import failed_compilation
        self.check_tools()
        self.recheck()
        candidates = []
        invocations = Path(self.runtime['job_output']) / 'compiler-invocations'
        for path in invocations.glob('*/PHYSICAL-RESULT.json'):
            value = read_bound(binding(path))
            inputs = read_bound(value['input'])
            if inputs.get('source') == source and (target is None or
                    inputs.get('physical_argv', [])[-3:] == ['-o', str(target), source['path']]):
                candidates.append(binding(path))
        if len(candidates) != 1:
            return None
        return failed_compilation(candidates[0], self.manager.snapshot,
                                  self.manager.reference, source,
                                  self.runtime['physical_compiler'],
                                  self.runtime['physical_flags'], target)

    def compile_protected(self, module):
        try:
            return self.protected_compile(module)
        except Exception as error:
            value = getattr(error, 'result', None)
            normal_error = (isinstance(value, dict) and value.get('success') is False and
                            not value.get('pet_restarted') and not value.get('restarted') and
                            (value.get('reason') == 'compile_error' or
                             value.get('method') == 'stock-guarded-dependency-build' and value.get('returncode') == 1))
            if not normal_error:
                raise
            source = binding(self.workspace / self.runtime['module_files'][module])
            evidence = self.failed_compilation(module, source)
            if evidence is not None:
                raise ModuleCompileFailure('The protected physical compiler failed: ' + module, evidence)
            raise

    def check_tools(self):
        if compiler_environment(self.workspace, self.environment) != self.environment:
            raise ValueError('The recorded compiler environment changed before private dispatch.')
        if binding(self.wrapper) != self.wrapper_binding or binding(self.dune['path']) != self.dune:
            raise ValueError('A bound private declaration tool changed.')

    def publish(self, module, artifact):
        self.recheck()
        source = self.workspace / self.runtime['module_files'][module]
        if module in self.protected:
            reference = artifact['accepted_object_receipt']
            if reference not in self.manager.rows or read_bound(reference)['source'] != binding(source):
                raise ValueError('A protected declaration lacks its accepted provider receipt.')
            return reference
        if artifact.get('module') != module or artifact.get('source') != binding(source):
            raise ValueError('A private artifact names another declaration.')
        reference = publish(self.manager, module, source, artifact['physical_result'],
                            artifact['private_object']['path'],
                            {'success': True, 'method': 'guarded-dune-dependency-build'},
                            workspace=self.workspace)
        save(self.output / ('dependency-' + module + '.json'), {
             'source': str(source), 'source_sha256': binding(source)['sha256'],
             'object': str(source.with_suffix('.vo')),
             'object_sha256': binding(source.with_suffix('.vo'))['sha256'],
             'result': {'success': True, 'method': 'guarded-dune-dependency-build'},
             'accepted_object_receipt': reference, 'private_compilation': artifact})
        self.recheck()
        return reference

    def execute(self, available_bytes):
        graph = read_bound(self.spec['graph'])
        admission = self.runtime['canonical_admission']
        return execute(self.runtime['ordered_modules'], graph['import_edges'], self.spec['weights'],
                       completed=self.spec['completed_modules'], protected=self.protected,
                       claim_bytes=admission['minimum_claim_bytes'],
                       fence_bytes=admission['physical_fence_bytes'], available_bytes=available_bytes,
                       compile_private=self.compile_private, publish=self.publish,
                       compile_protected=self.compile_protected,
                       checkpoint=lambda value: save(self.output / 'DECLARATION-DAG-PROGRESS.json', value),
                       maximum_workers=self.spec['maximum_workers'],
                       keep_going=self.spec.get('keep_going', False))


async def run(runtime, workspace, output, manager, environment, recheck, protected_compile):
    if manager is None:
        raise ValueError('Parallel declarations require authenticated compiler output receipts.')
    loop=asyncio.get_running_loop()
    def protected(module):
        return asyncio.run_coroutine_threadsafe(protected_compile(module),loop).result()
    adapter=GuardedAdapter(runtime,workspace,output,manager,environment,recheck,protected)
    def available():
        return next(int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()
                    if line.startswith('MemAvailable:'))
    try:
        result=await asyncio.to_thread(adapter.execute,available)
    except RuntimeError as error:
        if hasattr(error,'result'):
            save(Path(output)/'DECLARATION-DAG-RESULT.json',error.result)
        raise
    save(Path(output)/'DECLARATION-DAG-RESULT.json',result)
    return result
