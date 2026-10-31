"""Audit the narrow runtime-envelope consumers before cache dispatch."""
import ast
from pathlib import Path


FIELD_MAPPING = {
    'harness': ['recipe.backend.files', 'recipe.producers.implementation'],
    'seed_binding_reference': ['recipe.files', 'recipe.dependencies', 'transport.checked_bindings'],
    'native_delta': ['recipe.files', 'recipe.dependencies', 'transport.checked_bindings'],
    'native_route': ['recipe.backend.tactics', 'recipe.files', 'recipe.dependencies', 'configuration.execution_vectors'],
    'dependency_batch': ['recipe.backend.features.dependency_waves_disabled'],
    'declaration_checks': ['recipe.backend.features.control_sessions_disabled'],
    'control_session': ['recipe.backend.features.control_sessions_disabled'],
    'coqc_wrapper': ['recipe.backend.files', 'recipe.configuration.environment.ROCQ_COQC_BINARY'],
    'ocamlpath': ['recipe.configuration.environment.OCAMLPATH'],
    'build_dir': ['recipe.configuration.environment.AGENT_BUILD_DIR'],
    'runtime_path': ['transport.runtime_envelope'],
    'runtime_sha256': ['transport.runtime_envelope'],
    'bindings': ['recipe.files', 'transport.checked_bindings'],
    'target': ['recipe.module', 'recipe.proof', 'recipe.files'],
    'ordered_modules': ['recipe.dependencies', 'recipe.producers', 'configuration.execution_vectors'],
    'mcp_argv': ['configuration.execution_vectors'],
    'phase': ['recipe.backend.features.phase'],
    'canonical_admission': ['recipe.configuration.environment.ZESU_MODULE_CLAIM_BYTES'],
    'module_files': ['recipe.files', 'recipe.dependencies'],
    'expected_mcp_flags': ['recipe.configuration.argv', 'recipe.configuration.load_paths'],
    'physical_flags': ['recipe.configuration.argv', 'recipe.configuration.load_paths'],
    'job_output': ['transport.diagnostic_output'],
    'prospective_directory': ['transport.checked_actual_environment', 'transport.checked_mcp_launch', 'configuration.execution_vectors'],
}

KNOWN_SINKS = {'check_operation', 'proof_environment', 'prerequisite_environment', 'check_proof_bindings', 'validate_runtime'}


def audit(path):
    """Refuse an unclassified runtime read or an unreviewed runtime escape."""
    path = Path(path)
    source = path.read_text()
    tree = ast.parse(source)
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    fields, escapes = [], []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Name) or node.id != 'runtime' or not isinstance(node.ctx, ast.Load):
            continue
        parent = parents[node]
        name = None
        if isinstance(parent, ast.Subscript) and parent.value is node:
            if not isinstance(parent.slice, ast.Constant) or not isinstance(parent.slice.value, str):
                raise ValueError('A runtime field read is dynamic and unmapped.')
            name = parent.slice.value
        elif isinstance(parent, ast.Attribute) and parent.value is node:
            call = parents.get(parent)
            if not isinstance(call, ast.Call) or call.func is not parent:
                raise ValueError('A runtime method escapes the audited consumer.')
            if parent.attr == 'get':
                if not call.args or not isinstance(call.args[0], ast.Constant):
                    raise ValueError('A runtime get() field is dynamic and unmapped.')
                name = call.args[0].value
            elif parent.attr == 'update':
                if call.args or {word.arg for word in call.keywords} - {'runtime_path', 'runtime_sha256'}:
                    raise ValueError('A runtime update changes an unaudited semantic field.')
                escapes.append({'line': call.lineno, 'sink': 'validated transport injection'})
            else:
                raise ValueError('A runtime method has no transport mapping.')
        elif isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name) and parent.func.id in KNOWN_SINKS:
            escapes.append({'line': parent.lineno, 'sink': parent.func.id})
        else:
            raise ValueError('A runtime value escapes the audited consumers.')
        if name is not None:
            if name not in FIELD_MAPPING:
                raise ValueError('A runtime semantic field has no typed mapping: ' + str(name))
            fields.append({'field': name, 'line': parent.lineno,
                           'source': ast.get_source_segment(source, parent),
                           'typed_targets': FIELD_MAPPING[name]})
    return {'source': str(path), 'field_reads': fields, 'reviewed_sinks': escapes,
            'dynamic_reads': False, 'unmapped_fields': []}


def assert_covered(reports, mapping):
    """Require a concrete typed target for every observed source field."""
    required = {row['field'] for report in reports for row in report['field_reads']}
    if set(mapping) != required or any(not mapping[name] for name in required):
        raise ValueError('The concrete transport mapping is incomplete or contains unknown fields.')
    return True
