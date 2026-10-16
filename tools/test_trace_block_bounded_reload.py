"""Reject incomplete zero-display reload joins with synthetic artifact records."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_kernel_display import verify_kernel_capture_reload, RELOAD_CHECKS


class CaptureReloadTests(unittest.TestCase):
    def run_case(self, edit=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def save(name, value, raw=False):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                data = value if raw else (json.dumps(value, sort_keys=True) + '\n').encode()
                path.write_bytes(data)
                return {'path': name, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
            sidecar = save('complete.marshal', b'synthetic complete snapshot', True)
            reader = save('reader.exe', b'synthetic pinned reader', True)
            toolchain = save('toolchain.json', {'schema': 1})
            context = save('context.json', {'schema': 1})
            catalog = save('catalog.json', {'schema': 1})
            plan = {'schema': 1, 'complete_sidecar': sidecar, 'context_ref': context,
                    'evar_catalog_ref': catalog, 'toolchain_ref': toolchain, 'reader': reader,
                    'receipt_prefix': 'reload', 'markers': [], 'displays': []}
            receipt = {'schema': 1, 'kind': 'kernel-marshal-reload', 'sidecar': sidecar,
                       'context_ref': context, 'evar_catalog_ref': catalog, 'toolchain_ref': toolchain,
                       'reader': reader, 'accepted': True, 'checks': {key: True for key in RELOAD_CHECKS},
                       'kernel_typecheck': 'not-attempted', 'error': None, 'unique_kernel_nodes': 1}
            configuration = {'plan': plan, 'receipt': receipt, 'invocation': {}, 'result': {}}
            if edit:
                edit(configuration)
            plan_ref = save('PLAN.json', plan)
            receipt_ref = save('reload/reload.json', receipt)
            result = {'schema': 1, 'accepted': True, 'receipt': receipt_ref,
                      'membership_receipts': [], 'root_receipts': []}
            result.update(configuration['result'])
            stdout = save('stdout.json', {'result': save('reader-result.json', result)})
            stderr = save('stderr', b'', True)
            arguments = [str(root), str(root / 'PLAN.json'), toolchain['sha256'], '--result-ref']
            invocation = {'schema': 1, 'kind': 'kernel-reader-invocation', 'reader': reader,
                          'arguments': arguments, 'sidecar': sidecar, 'toolchain_ref': toolchain,
                          'marker_plan': plan_ref, 'exit_code': 0, 'receipt': receipt_ref,
                          'membership_receipts': [], 'root_receipts': [], 'stdout': stdout, 'stderr': stderr}
            invocation.update(configuration['invocation'])
            capture = {'displays': {}, 'complete_sidecar': sidecar, 'evar_catalog_ref': catalog,
                       'reload_evidence': {'receipt': receipt_ref,
                                           'invocation': save('invocation.json', invocation)}}
            return verify_kernel_capture_reload(root, capture, expected_reader=reader,
                expected_toolchain_ref=toolchain, expected_marker_plan=plan_ref,
                expected_arguments=arguments)

    def reject(self, edit):
        with self.assertRaises((ValueError, KeyError, FileNotFoundError)):
            self.run_case(edit)

    def test_complete_zero_display_reload(self):
        self.assertEqual(self.run_case()['displays'], [])

    def test_nonempty_display_plan_rejects(self):
        self.reject(lambda value: value['plan'].update(displays=[{}]))

    def test_nonempty_marker_plan_rejects(self):
        self.reject(lambda value: value['plan'].update(markers=[{}]))

    def test_foreign_reader_receipt_rejects(self):
        self.reject(lambda value: value['receipt'].update(reader={'path': 'foreign', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_foreign_catalog_receipt_rejects(self):
        self.reject(lambda value: value['receipt'].update(evar_catalog_ref={'path': 'foreign', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_foreign_context_receipt_rejects(self):
        self.reject(lambda value: value['receipt'].update(context_ref={'path': 'foreign', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_foreign_toolchain_receipt_rejects(self):
        self.reject(lambda value: value['receipt'].update(toolchain_ref={'path': 'foreign', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_refused_reload_rejects(self):
        self.reject(lambda value: value['receipt'].update(accepted=False))

    def test_failed_remarshal_check_rejects(self):
        self.reject(lambda value: value['receipt']['checks'].update(remarshal_bytes=False))

    def test_missing_reload_check_rejects(self):
        self.reject(lambda value: value['receipt']['checks'].pop('context'))

    def test_unknown_reload_field_rejects(self):
        self.reject(lambda value: value['receipt'].update(unknown=True))

    def test_failed_invocation_rejects(self):
        self.reject(lambda value: value['invocation'].update(exit_code=1))

    def test_boolean_exit_rejects(self):
        self.reject(lambda value: value['invocation'].update(exit_code=False))

    def test_changed_arguments_rejects(self):
        self.reject(lambda value: value['invocation'].update(arguments=['foreign']))

    def test_missing_invocation_receipt_rejects(self):
        self.reject(lambda value: value['invocation'].update(receipt={'path': 'missing', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_extra_root_receipt_rejects(self):
        self.reject(lambda value: value['invocation'].update(root_receipts=[{}]))

    def test_extra_membership_receipt_rejects(self):
        self.reject(lambda value: value['invocation'].update(membership_receipts=[{}]))

    def test_stdout_result_refusal_rejects(self):
        self.reject(lambda value: value['result'].update(accepted=False))

    def test_stdout_substituted_receipt_rejects(self):
        self.reject(lambda value: value['result'].update(receipt={'path': 'other', 'sha256': 'a' * 64, 'bytes': 1}))

    def test_stdout_missing_receipts_rejects(self):
        self.reject(lambda value: value['result'].update(root_receipts=None))

    def test_unsafe_receipt_prefix_rejects(self):
        self.reject(lambda value: value['plan'].update(receipt_prefix='../reload'))

    def test_changed_receipt_prefix_rejects(self):
        self.reject(lambda value: value['plan'].update(receipt_prefix='foreign'))


if __name__ == '__main__':
    unittest.main()
