#!/usr/bin/env python3
"""Prepare an owned diagnostic scope without editing its original workspace.

The caller owns the exit watcher. Preparation performs dependency builds only.
It never starts a native proof or an MCP transport.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from trace_block_filtered import bind_descriptors, guard_manifest, typed_guards
import trace_block_package as package

OWNER = Path(__file__).resolve().parents[2]
BRIDGE = package.BRIDGE
PLUGIN = package.FILTERED
RUNTIME_FILES = ("tools/resource_guard.sh", "tools/native_admission.py",
                 "tools/coqc_findlib.py", "tools/coqc_recipe.py",
                 "tools/dune_trace_guard.py", "tools/dune_coqc_guarded.sh",
                 "tools/rocq_coqc_guarded.sh", "tools/rocq_mcp_guarded.sh",
                 "tools/guard-bin/dune", "tools/block/trace_block_coqc.sh")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path = Path(path)
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() != payload:
        raise ValueError("The immutable preparation record changed: " + str(path))
    if not path.exists():
        path.write_bytes(payload)


def command_spans(text):
    """Find vernacular terminators outside strings and nested comments."""
    start = index = depth = 0
    quoted = False
    while index < len(text):
        pair = text[index:index + 2]
        if not quoted and pair == "(*":
            depth += 1
            index += 2
            continue
        if depth:
            if pair == "*)":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if text[index] == '"':
            if quoted and pair == '""':
                index += 2
                continue
            quoted = not quoted
        if (not quoted and text[index] == "."
                and (index + 1 == len(text) or text[index + 1].isspace()
                     or text[index + 1:index + 3] == "(*")):
            yield start, index + 1
            start = index + 1
        index += 1
    if depth or quoted:
        raise ValueError("The instrumented source has an unclosed comment or string.")
    if text[start:].strip() and not text[start:].strip().startswith("(*"):
        raise ValueError("The instrumented source has an unterminated command.")


def _quoted(value):
    return '"' + value.replace('"', '""') + '"'


def trigger_guard(stop):
    kind, value = stop["kind"], stop["value"]
    if kind == "goal-head" and value == "mem_mapsto_kind":
        return ("lazymatch goal with |- ?target => "
                "let inner := lazymatch target with envs_entails _ ?body => body | _ => target end in "
                "let rec head term := lazymatch term with ?function ?argument => head function | _ => term end in "
                "let actual := head inner in constr_eq actual mem_mapsto_kind end")
    if kind == "goal-head":
        return 'lazymatch goal with |- LiTactic (normalize_instr_addr _) => idtac | _ => fail 0 "requested goal head is absent" end'
    if kind == "instruction" and value == "WriteMem":
        return 'lazymatch goal with |- envs_entails _ (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) => idtac | _ => fail 0 "requested WriteMem is absent" end'
    if kind == "instruction" and value == "FindMemMapsTo":
        return 'lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac | _ => fail 0 "requested FindMemMapsTo is absent" end'
    if kind == "pc":
        literal = str(int(value, 16))
        return ('lazymatch goal with |- envs_entails _ (find_in_context (FindInstrKind ?address _) _) => '
                'assert_fails (has_evar address); let expected := constr:(' + literal + '%Z) in '
                'constr_eq address expected | _ => fail 0 "requested PC is absent" end')
    if kind == "instruction" and value == "jalr":
        return ("lazymatch goal with "
            "| |- LiTactic (normalize_instr_addr (bv_unsigned "
            "(bv_or (bv_and (bv_add _ (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)))) => idtac "
            "| |- LiTactic (normalize_instr_addr (bv_unsigned "
            "(bv_or (bv_and _ (BV 64 18446744073709551614)) (BV 64 0)))) => idtac "
            '| _ => fail 0 "requested masked-return trigger is absent" end')
    return None


def return_clause_commands(client):
    """Expose original prefixes without a new premise or normalization."""
    common = "zesu_switch_enabled constr:(ZesuStepReturnRoute); unLET; "
    full = "(bv_or (bv_and (bv_add ?ra (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0))"
    reduced = "(bv_or (bv_and ?ra (BV 64 18446744073709551614)) (BV 64 0))"
    def bind(action):
        action = "assert_fails (has_evar ra); " + action
        if client == "ReturnRoute.normalize":
            target = ("lazymatch goal with "
                "| |- LiTactic (normalize_instr_addr (bv_unsigned " + full + ")) => " + action + " "
                "| |- LiTactic (normalize_instr_addr (bv_unsigned " + reduced + ")) => " + action + " end")
        elif client == "ReturnRoute.fault":
            target = ("lazymatch goal with |- SimplAnd (bv_extract 0 1 (bv_shiftr "
                + full + " (BV 64 1)) = BV 1 1) False => " + action + " end")
        elif client == "ReturnRoute.implication":
            target = ("lazymatch goal with |- SimplImpl ?predicate ?simplified => "
                "lazymatch predicate with bv_extract 0 1 (bv_shiftr " + full
                + " (BV 64 1)) = BV 1 1 => unify simplified False; "
                "change (SimplAnd predicate False); " + action + " end end")
        else:
            raise ValueError("The return client has no reviewed clause binding.")
        return common + target
    alignment = ("zesu_return_decode_facts; multimatch goal with "
                 "Haligned : (?address mod 4 = 0)%Z |- _ => "
                 "assert_fails (has_evar address) end")
    return [("switch-check", "zesu_switch_enabled constr:(ZesuStepReturnRoute)"),
            ("closed-ra", bind("idtac")),
            ("zesu_return_decode_facts", bind("zesu_return_decode_facts")),
            ("alignment-selector-after-decode", bind(alignment)),
            ("address-selection", bind("zesu_return_with_address ra "
                "ltac:(fun address Hrange Hvalue HraAligned => idtac)"))]


def around(client, original, stop, rule, class_name, entry_guard=None):
    clauses = [("liShow", "liShow")]
    if rule == "ReturnRoute":
        clauses.extend(return_clause_commands(client))
    guard = trigger_guard(stop)
    if guard:
        clauses.append(("requested-trigger", guard))
    if entry_guard:
        clauses.append(("entry-goal-shape", entry_guard))
    callbacks = "; ".join("(" + _quoted(label) + ", (fun () => ltac1:(" + code + ")))"
                          for label, code in clauses)
    wrapped = ("ltac2:(trace_block_filtered " + _quoted(client) + " "
               + typed_guards()[client] + " [" + callbacks
               + "] (fun () => ltac1:(" + original + ")))")
    descriptor = {"rule": rule, "commands": dict(clauses, **{"whole-rule": original}),
                  "log_filter": [class_name, client, "LiTactic", "normalize_instr_addr",
                                 "SimplAnd", "SimplImpl", "zesu_return_route",
                                 "zesu_conjunct_head_if_enabled", "zesu_match_resource_pure_heads"]}
    descriptor = bind_descriptors({client: descriptor})[client]
    return wrapped, descriptor


def instrument_return_route(text, stop):
    """Wrap all three actual Hint Extern bodies. Keep each body byte-exact."""
    replacements, descriptors = [], {}
    names = ("normalize", "fault", "implication")
    for start, end in command_spans(text):
        command = text[start:end]
        from rule_compare import without_comments
        masked = without_comments(command)
        match = re.search(r"#\[export\]\s+Hint\s+Extern\b", masked)
        if not match:
            continue
        if len(descriptors) >= len(names):
            raise ValueError("ReturnRoute has an unreviewed extra Hint Extern.")
        arrow = command.find("=>", match.end())
        tail = re.search(r"\s*:\s*typeclass_instances\s*\.$", command)
        if arrow < 0 or tail is None or tail.start() <= arrow:
            raise ValueError("A ReturnRoute hint has an unsupported body boundary.")
        body = command[arrow + 2:tail.start()]
        client = "ReturnRoute." + names[len(descriptors)]
        wrapped, descriptor = around(client, body, stop, "ReturnRoute", "ZesuStepReturnRoute")
        descriptors[client] = descriptor
        replacements.append((start + arrow + 2, start + tail.start(), "\n  " + wrapped))
    if len(descriptors) != 3:
        raise ValueError("ReturnRoute must expose exactly three reviewed Hint Extern entries.")
    for start, end, replacement in reversed(replacements):
        text = text[:start] + replacement + text[end:]
    return package.BRIDGE_IMPORT + "\n" + text, descriptors


def replace_ltac(text, name, transform):
    matches = []
    for start, end in command_spans(text):
        command = text[start:end]
        from rule_compare import without_comments
        match = re.search(r"\bLtac\s+" + re.escape(name) + r"\s*:=", without_comments(command))
        if match:
            body_start = start + match.end()
            matches.append((body_start, end - 1, text[body_start:end - 1]))
    if len(matches) != 1:
        raise ValueError("The tactic definition is missing or ambiguous: " + name)
    start, end, original = matches[0]
    return text[:start] + transform(original) + text[end:], original


def instrument_hooks(text, stop, conjunct):
    descriptors = {}
    if conjunct:
        def transform(original):
            wrapped, descriptor = around("Hooks.zesu_conjunct_head_if_enabled", original,
                stop, "ConjunctMatch", "ZesuStepConjunctMatch",
                'lazymatch goal with |- envs_entails _ _ => idtac | _ => fail 0 "entry wrapper is absent" end')
            descriptors["Hooks.zesu_conjunct_head_if_enabled"] = descriptor
            return "\n  " + wrapped
        text, _ = replace_ltac(text, "zesu_conjunct_head_if_enabled", transform)
    checkpoint = ("\n lazymatch goal with\n"
        " | |- envs_entails _ (find_in_context (FindInstrKind ?trace_pc _) _) =>\n"
        '     let observe := ltac2:(pc |- trace_block_checkpoint "instruction-lookup" (Option.get (Ltac1.to_constr pc))) in observe trace_pc\n'
        " | _ => idtac\n end;")
    guard = trigger_guard(stop)
    if guard:
        checkpoint += ("\n tryif (" + guard + ")\n"
                       ' then ltac2:(trace_block_checkpoint "requested-trigger" constr:(tt))\n'
                       " else idtac;")
    text, original = replace_ltac(text, "zesu_liAStep", lambda body: checkpoint + body)
    return package.BRIDGE_IMPORT + "\n" + text, descriptors, original


def instrument_memory_access(hooks_text, module_text):
    """Wrap only the reviewed historical MemoryAccess entry shapes."""
    call = 'zesu_memory_access_if_enabled zesu_integer_array_facts'
    expected_body = '''
  (lazymatch address with
   | bv_unsigned (bv_add (Z_to_bv 64 ?base) ?offset) =>
       unify key FICSyntactic;
       exact (memory_access_array_inst (Z_to_bv 64 base) offset)
   end)'''
    filters = ['MemoryAccess', 'FindMemMapsTo', 'FindInContext',
               'MemoryAccessSelection', 'FICSyntactic', 'zesu_memory_access']
    descriptors = {}
    def wrapper(client, clauses, callback):
        callbacks = '; '.join('(' + _quoted(label) + ', (fun () => ltac1:(' + command + ')))'
                              for label, command in clauses)
        return ('trace_block_filtered ' + _quoted(client) + ' ' + typed_guards()[client]
                + ' [' + callbacks + '] ' + callback)
    def hook(body):
        marker = '| ' + call + '\n'
        if body.count(marker) != 1:
            raise ValueError('The MemoryAccess Hooks callback is missing, repeated, or unsupported.')
        clauses = [('switch-check', 'zesu_switch_enabled constr:(ZesuStepMemoryAccess)'),
                   ('goal-shape', 'lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end'),
                   ('liShow', 'liShow')]
        descriptors['MemoryAccess.Hooks'] = {'rule': 'MemoryAccess',
            'commands': dict(clauses, **{'whole-rule': call}), 'log_filter': filters}
        observed = 'ltac2:(' + wrapper('MemoryAccess.Hooks', clauses,
                                       '(fun () => ltac1:(' + call + '))') + ')'
        return body.replace(marker, '| ' + observed + '\n')
    updated_hooks, _ = replace_ltac(hooks_text, 'zesu_liAStep', hook)
    matches = []
    for start, end in command_spans(module_text):
        command = module_text[start:end]
        if 'Hint Extern' not in command or 'FindInContext' not in command or 'FindMemMapsTo' not in command:
            continue
        signature = 'Global Hint Extern 0 (FindInContext (FindMemMapsTo ?address) ?key)'
        arrow = command.find('=>')
        tail = re.search(r'\s*:\s*typeclass_instances\s*\.$', command)
        if (arrow < 0 or not tail or command[:arrow].strip() != signature
                or command[arrow + 2:tail.start()] != expected_body):
            raise ValueError('The MemoryAccess FindInContext callback has an unsupported source shape.')
        body = command[arrow + 2:tail.start()]
        clauses = [('goal-shape', 'lazymatch goal with |- FindInContext (FindMemMapsTo _) _ => idtac end')]
        descriptors['MemoryAccess.FindInContext'] = {'rule': 'MemoryAccess',
            'commands': dict(clauses, **{'whole-rule': 'lazymatch goal with |- FindInContext (FindMemMapsTo ?address) ?key => ' + body + ' end'}),
            'log_filter': filters}
        callback = '(fun () => Ltac1.apply original [Ltac1.of_constr constr:(tt)] (fun result => Ltac1.run result))'
        observed = (' let original := ltac:(fun unused => ' + body
                    + ') in let observe := ltac2:(original |- '
                    + wrapper('MemoryAccess.FindInContext', clauses, callback)
                    + ') in observe original ')
        matches.append((start + arrow + 2, start + tail.start(), observed))
    if len(matches) != 1:
        raise ValueError('The MemoryAccess FindInContext callback is missing or repeated.')
    start, end, observed = matches[0]
    updated_module = package.BRIDGE_IMPORT + '\n' + module_text[:start] + observed + module_text[end:]
    return updated_hooks, updated_module, bind_descriptors(descriptors)

def insert_bridge_import(prefix):
    """Keep Automation.All as the first import in the scratch proof."""
    from rule_compare import without_comments
    spans = list(command_spans(prefix))
    if not spans:
        raise ValueError("The scratch source has no import commands.")
    start, end = spans[0]
    if not re.fullmatch(r"\s*Require\s+Import\s+ZesuSsz\.Automation\.All\s*\.\s*",
                        without_comments(prefix[start:end])):
        raise ValueError("The scratch proof must import Automation.All first.")
    return prefix[:end] + "\n" + package.BRIDGE_IMPORT + prefix[end:]


def _git(workspace, *arguments):
    return subprocess.check_output(["git", "-C", str(workspace), *arguments])


def source_inventory(workspace):
    names = set(_git(workspace, "ls-files", "-z").decode().split("\0"))
    names.update(_git(workspace, "ls-files", "--others", "--exclude-standard", "-z").decode().split("\0"))
    result = {}
    for name in sorted(names - {""}):
        if name.startswith(("docs/ai/", "_build/", ".ai-coord/")):
            continue
        path = workspace / name
        if path.is_symlink():
            result[name] = {"symlink": os.readlink(path)}
        elif path.is_file():
            result[name] = {"sha256": digest(path), "mode": path.stat().st_mode & 0o777}
        else:
            result[name] = {"deleted": True}
    return result


def native_inventory(directory):
    """Bind ignored native sources by actual bytes, without regeneration."""
    result = {}
    for parent, directories, filenames in os.walk(directory, followlinks=True):
        for name in filenames:
            path = Path(parent) / name
            if path.is_file():
                result[path.relative_to(directory).as_posix()] = digest(path)
    if not result:
        raise ValueError("The validated native source tree is empty.")
    return dict(sorted(result.items()))


def copy_inventory(source, destination, inventory):
    for name, identity in inventory.items():
        old, new = source / name, destination / name
        if identity.get("deleted"):
            if new.exists() or new.is_symlink():
                new.unlink()
            continue
        new.parent.mkdir(parents=True, exist_ok=True)
        if new.is_symlink():
            new.unlink()
        if "symlink" in identity:
            if new.exists():
                new.unlink()
            new.symlink_to(identity["symlink"])
        else:
            shutil.copy2(old, new)
            if digest(new) != identity["sha256"]:
                raise ValueError("A source changed during its diagnostic copy: " + name)


def writer_identity(request=None):
    if request is not None and "writer_id" in request:
        writer = request["writer_id"]
    else:
        writer = os.environ.get("ZESU_WRITER_ID") or os.environ.get("COORD_AGENT")
    if not isinstance(writer, str) or not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9._-]*", writer):
        raise ValueError("Supply a valid writer identity before diagnostic preparation.")
    return writer


def switch_adjusted_prefix(workspace, request):
    from trace_block_mcp import RULE_SWITCHES
    from rule_compare import switch_instances
    prefix, adjustments = request["source_prefix"], []
    for row in request["rule_set"]:
        cls = RULE_SWITCHES[row["name"]]
        instances = switch_instances(workspace, prefix, cls)
        if not row["enabled"]:
            adjustments.extend("Remove Hints " + name + " : typeclass_instances.\n" for name in instances)
        elif not instances:
            adjustments.append("#[local] Instance : " + cls + " := I.\n")
    location = prefix.index(request["declaration"])
    return prefix[:location] + "".join(adjustments) + prefix[location:], adjustments


def install_guard_manifest(workspace, descriptors, *, bounded=False):
    """Install the exact descriptor manifest under its content hash."""
    if bounded:
        from trace_block_bounded_prepare import bounded_guard_manifest
        value, payload = bounded_guard_manifest(descriptors)
    else:
        value, payload = guard_manifest(descriptors)
    expected = hashlib.sha256(payload).hexdigest()
    path = Path(workspace) / "_build/trace-native" / ("GUARD-MANIFEST-" + expected + ".json")
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.is_symlink() or (path.exists() and path.read_bytes() != payload):
        raise ValueError("The immutable guard manifest changed.")
    if not path.exists():
        path.write_bytes(payload)
    return {"path": str(path.resolve()), "sha256": expected}


def guard_manifest_environment(workspace, descriptors, reference):
    """Validate the exact path, hash and clients before setting the guard input."""
    if not isinstance(reference, dict) or set(reference) != {"path", "sha256"}:
        raise ValueError("The prepared guard manifest binding is unavailable.")
    path = Path(reference["path"])
    if path.is_symlink() or not path.resolve().is_relative_to(Path(workspace).resolve()):
        raise ValueError("The guard manifest leaves the diagnostic workspace.")
    value, payload = guard_manifest(descriptors)
    if digest(path) != reference["sha256"] or path.read_bytes() != payload:
        raise ValueError("The prepared guard manifest does not match its descriptors.")
    return {"ZESU_TRACE_GUARD_MANIFEST": str(path.resolve())}


def build_environment(workspace, writer_id=None, descriptors=None, guard_reference=None):
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith(("ZESU_", "ROCQ_")) and key != "OCAMLPATH"}
    environment.update(ZESU_WRITER_ID=writer_identity({"writer_id": writer_id}), ZESU_MODULE_LIMIT_GIB="6",
                       ZESU_GATE_MODULE_LIMIT_GIB="6", ZESU_PROOF_CPU_LIMIT="1200")
    environment["PATH"] = str(workspace / "bin") + ":/home/cody/.local/bin:" + environment.get("PATH", "")
    if descriptors is not None or guard_reference is not None:
        environment.update(guard_manifest_environment(workspace, descriptors, guard_reference))
    return environment


def request_key(request):
    logical = {key: request[key] for key in ("scope", "rule_set", "stop")}
    logical["capture_surface_policy"] = request.get("capture_surface_policy", "filtered-chunks-v1")
    return hashlib.sha256(json.dumps(logical, sort_keys=True).encode()).hexdigest()


def publish_prepared(request, record):
    """Publish only a successfully compiled, source-bound preparation."""
    if record.get("focused_compilation", {}).get("success") is not True:
        raise ValueError("The focused compilation has not passed.")
    path = OWNER / "_build/trace-preparation/corrected" / (request_key(request) + ".json")
    save(path, record)
    return path


def corrected_prepared(request):
    runtime_package = preparation_package(request)
    path = OWNER / "_build/trace-preparation/corrected" / (request_key(request) + ".json")
    if not path.exists():
        return None
    result = json.loads(path.read_text())
    if result.get("instrumentation", {}).get("protocol") != getattr(runtime_package, "PROTOCOL", "filtered-chunks-v1"):
        raise ValueError("The corrected preparation lacks the filtered capture protocol.")
    preparation_guard_environment(result["workspace"], result["entry_descriptors"], result.get("guard_manifest"), runtime_package)
    runtime_package.validate_runtime(result)
    if result["scope"] != request["scope"] or result.get("focused_compilation", {}).get("success") is not True:
        raise ValueError("The corrected preparation has a different scope or lacks compilation.")
    evidence = result["preparation_evidence"]
    original = Path(evidence["original_workspace"])
    for field, observed in (("original_sources", source_inventory(original)),
                            ("original_native_sources", native_inventory(original / "generated/isla-traces"))):
        record = Path(evidence[field])
        if digest(record) != evidence[field + "_sha256"] or observed != json.loads(record.read_text()):
            raise ValueError("The original frozen inventory changed: " + field)
    for name, expected in result["instrumentation"]["prepared_source_hashes"].items():
        if digest(Path(result["workspace"]) / name) != expected:
            raise ValueError("A corrected diagnostic source changed: " + name)
    manifest = result["focused_compilation"]["objects"]
    for name, expected in manifest.items():
        if digest(Path(result["build_dir"]) / name) != expected:
            raise ValueError("A corrected diagnostic artifact changed: " + name)
    return result


def affected_modules(workspace, roots, changed):
    """Order every affected project consumer after its dependencies."""
    from rule_compare import imported_modules
    affected, visiting, ordered = {}, set(), []
    def visit(module):
        if module in affected:
            return affected[module]
        source = workspace / (module.replace(".", "/") + ".v")
        if not source.is_file():
            affected[module] = False
            return False
        if module in visiting:
            raise ValueError("The diagnostic import graph contains a cycle: " + module)
        visiting.add(module)
        dependencies = [visit(name) for name in imported_modules(source.read_text())]
        visiting.remove(module)
        affected[module] = module in changed or any(dependencies)
        if affected[module]:
            ordered.append(module)
        return affected[module]
    for module in [*changed, *roots]:
        visit(module)
    return ordered



def refresh_preparation(request, completed_path, out_dir, plugin_source):
    """Seal old inputs and prepare an incremental build in a completed scope."""
    from rule_compare import imported_modules
    completed_path, out_dir = Path(completed_path), Path(out_dir)
    previous = json.loads(completed_path.read_text())
    if previous["scope"] != request["scope"]:
        raise ValueError("The completed preparation has a different scope.")
    workspace, original = Path(previous["workspace"]), Path(request["workspace"])
    if digest(Path(request["source"])) != request["scope"]["source_sha256"]:
        raise ValueError("The original frozen source changed.")
    before = previous["instrumentation"]["prepared_source_hashes"]
    for name, expected in before.items():
        source = workspace / name
        if digest(source) != expected:
            raise ValueError("A completed preparation source changed: " + name)
        target = out_dir / "before" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    save(out_dir / "PREVIOUS-PREPARED.json", previous)
    original_record = Path(previous.get("preparation_evidence", {}).get("original_scope_record")
                           or previous["instrumentation"].get("original_scope_record", ""))
    if digest(original_record) != previous["instrumentation"]["original_scope_sha256"]:
        raise ValueError("The original preparation input record changed.")
    inventory = source_inventory(original)
    if inventory != json.loads(original_record.read_text())["inventory"]:
        raise ValueError("The original frozen source inventory changed.")
    native_sources = native_inventory(original / "generated/isla-traces")
    if native_sources != native_inventory(workspace / "generated/isla-traces"):
        raise ValueError("The original and prepared native sources differ.")
    save(out_dir / "ORIGINAL-SOURCES.json", inventory)
    save(out_dir / "ORIGINAL-NATIVE-SOURCES.json", native_sources)
    build = Path(previous["build_dir"])
    artifacts = {str(path.relative_to(build)): digest(path)
                 for path in sorted((build / "default").rglob("*.vo")) if path.is_file()}
    save(out_dir / "PREVIOUS-OBJECTS.json", artifacts)
    if previous.get("instrumentation", {}).get("protocol") != "filtered-chunks-v1":
        raise ValueError("Refresh requires a compiled filtered preparation.")
    package.validate_runtime(previous)
    plugin = workspace / PLUGIN / "trace-observer/filtered_trace_plugin.ml"
    shutil.copy2(plugin_source, plugin)
    selected, entries = previous["selected_rules"], {}
    changed = []
    if "ReturnRoute" in selected:
        path = workspace / "ZesuSsz/Automation/ReturnRoute.v"
        text, rows = instrument_return_route((original / path.relative_to(workspace)).read_text(), request["stop"])
        path.write_text(text)
        entries.update(rows)
        changed.append("ZesuSsz.Automation.ReturnRoute")
    hooks = workspace / "ZesuSsz/Automation/Hooks.v"
    text, rows, step = instrument_hooks((original / hooks.relative_to(workspace)).read_text(),
                                       request["stop"], "ConjunctMatch" in selected)
    if "MemoryAccess" in selected:
        memory = workspace / "ZesuSsz/Automation/MemoryAccess.v"
        text, observed, memory_rows = instrument_memory_access(
            text, (original / memory.relative_to(workspace)).read_text())
        memory.write_text(observed)
        entries.update(memory_rows)
        changed.append("ZesuSsz.Automation.MemoryAccess")
    hooks.write_text(text)
    entries.update(rows)
    changed.append("ZesuSsz.Automation.Hooks")
    scratch = Path(previous["source"])
    prefix, adjustments = switch_adjusted_prefix(workspace, request)
    scratch.write_text(insert_bridge_import(prefix) + "Abort.\n")
    modules = affected_modules(workspace, list(imported_modules(request["source_prefix"])), changed)
    for module in modules:
        relative = Path("default") / (module.replace(".", "/") + ".vo")
        path = build / relative
        if path.is_file():
            target = out_dir / "before-objects" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, target)
    hashes = {name: digest(workspace / name) for name in before}
    guard_reference = install_guard_manifest(workspace, entries)
    hashes[str(Path(guard_reference["path"]).relative_to(workspace))] = guard_reference["sha256"]
    instrumentation = {**previous["instrumentation"], "prepared_source_hashes": hashes,
                       "protocol": "filtered-chunks-v1",
                       "focused_previous_sha256": digest(out_dir / "PREVIOUS-PREPARED.json"),
                       "step_original_sha256": hashlib.sha256(step.encode()).hexdigest()}
    instrumentation.pop("original_scope_record", None)
    instrumentation["switch_adjustments"] = adjustments
    result = dict(previous, writer_id=writer_identity(request), entry_descriptors=entries,
                  guard_manifest=guard_reference, instrumentation=instrumentation,
                  focused_modules=modules, focused_targets=[BRIDGE.replace(".v", ".vo"),
                    *[name.replace(".", "/") + ".vo" for name in modules]],
                  focused_compilation={"success": False, "objects": {}}, preparation_evidence={"old_inputs": str(out_dir / "before"),
                    "old_preparation": str(out_dir / "PREVIOUS-PREPARED.json"),
                    "old_objects": str(out_dir / "PREVIOUS-OBJECTS.json"),
                    "original_workspace": str(original),
                    "original_sources": str(out_dir / "ORIGINAL-SOURCES.json"),
                    "original_sources_sha256": digest(out_dir / "ORIGINAL-SOURCES.json"),
                    "original_native_sources": str(out_dir / "ORIGINAL-NATIVE-SOURCES.json"),
                    "original_native_sources_sha256": digest(out_dir / "ORIGINAL-NATIVE-SOURCES.json")})
    save(out_dir / "FOCUSED-REQUEST.json", result)
    return result


def preparation_package(request):
    policy = request.get("capture_surface_policy", "filtered-chunks-v1")
    if policy == "filtered-chunks-v1":
        return package
    if policy == "bounded-kernel-v1":
        import trace_block_bounded_package
        return trace_block_bounded_package
    raise ValueError("The requested capture surface is unsupported.")


def preparation_guard_environment(workspace, descriptors, reference, runtime_package):
    if runtime_package is package:
        return guard_manifest_environment(workspace, descriptors, reference)
    from trace_block_bounded_prepare import bounded_guard_manifest_environment
    return bounded_guard_manifest_environment(workspace, descriptors, reference)


def bounded_descriptors(descriptors):
    from trace_block_bounded_prepare import bind_bounded_descriptors
    result = {}
    for client, descriptor in descriptors.items():
        value = dict(descriptor)
        guard = dict(value["typed_guard"])
        command = guard["command"]
        if "trace_block_ltac1_guard" in command:
            if command.count("trace_block_ltac1_guard") != 1:
                raise ValueError("The guard bridge has an unsupported boundary.")
            command = command.replace("trace_block_ltac1_guard", "trace_bounded_ltac1_guard")
            guard.update(command=command, sha256=hashlib.sha256(command.encode()).hexdigest())
        value["typed_guard"] = guard
        # The plugin appends whole-rule automatically. Each declared callback runs once.
        value["trials"] = [{"clause": label, "command": code,
            "exposure": "not-exposed" if label in {"liShow", "requested-trigger", "whole-rule"} else "exposed"}
            for label, code in value["commands"].items()]
        result[client] = value
    return bind_bounded_descriptors(result)


def bounded_observation(original, observed, descriptors):
    replacements = {package.BRIDGE_IMPORT: "From P0Bounded Require Import TraceObserver.",
        "trace_block_filtered": "trace_bounded_filtered",
        "trace_block_ltac1_guard": "trace_bounded_ltac1_guard",
        "trace_block_checkpoint": "trace_bounded_checkpoint"}
    for old, new in replacements.items():
        if old in original:
            raise ValueError("The original source already contains observer plumbing.")
        observed = observed.replace(old, new)
    return observed, bounded_descriptors(descriptors)


def prepare_request(request, out_dir):
    """Copy the frozen scope, instrument it, and build only its import closure."""
    runtime_package = preparation_package(request)
    bounded = runtime_package is not package
    ready = corrected_prepared(request)
    if ready is not None:
        return dict(ready, writer_id=writer_identity(request))
    writer = writer_identity(request)
    from trace_block_mcp import RULE_SWITCHES
    from rule_compare import imported_modules, switch_instances
    original = Path(request["workspace"]).resolve()
    source = Path(request["source"]).resolve()
    if not source.is_relative_to(original):
        raise ValueError("The source leaves the original workspace.")
    selected = [row["name"] for row in request["rule_set"]]
    if not selected or any(name not in {"ReturnRoute", "ConjunctMatch", "MemoryAccess"} for name in selected):
        raise ValueError("Every requested observer needs a reviewed descriptor.")
    root = _git(original, "rev-parse", "HEAD").decode().strip()
    if root != request["scope"]["root"] or digest(source) != request["scope"]["source_sha256"]:
        raise ValueError("The original frozen source identity changed.")
    inventory = source_inventory(original)
    native = original / "generated/isla-traces"
    if not native.is_dir():
        raise ValueError("The validated native source tree is absent.")
    native_sources = native_inventory(native)
    overlays = {name: digest(OWNER / name) for name in (*RUNTIME_FILES, *runtime_package.overlay_files(OWNER))}
    key_data = {"scope": request["scope"], "inventory": inventory, "native_sources": native_sources, "overlays": overlays,
                "rules": request["rule_set"], "stop": request["stop"], "helper_sha256": digest(__file__), "writer_id": writer}
    key = hashlib.sha256(json.dumps(key_data, sort_keys=True).encode()).hexdigest()
    record_dir = OWNER / "_build" / "trace-preparation" / key
    ready = record_dir / "PREPARED.json"
    if ready.exists():
        result = json.loads(ready.read_text())
        for name, expected in result["instrumentation"]["prepared_source_hashes"].items():
            if digest(Path(result["workspace"]) / name) != expected:
                raise ValueError("A prepared diagnostic source changed: " + name)
        runtime_package.validate_runtime(result)
        return result
    record_dir.mkdir(parents=True, exist_ok=True)
    common = Path(_git(original, "rev-parse", "--path-format=absolute", "--git-common-dir").decode().strip())
    workspace = common.parent / ".worktrees" / ("worker2-p0-trace-" + request["block_pc"][2:] + "-" + key[:10])
    if workspace.exists():
        raise ValueError("An unfinished diagnostic scope already exists: " + str(workspace))
    save(record_dir / "INPUTS.json", key_data)
    subprocess.run(["git", "-C", str(original), "worktree", "add", "--detach", str(workspace), root], check=True)
    copy_inventory(original, workspace, inventory)
    native = original / "generated/isla-traces"
    if not native.is_dir():
        raise ValueError("The validated native source tree is absent.")
    shutil.copytree(native, workspace / "generated/isla-traces", dirs_exist_ok=True)
    if native_inventory(workspace / "generated/isla-traces") != native_sources:
        raise ValueError("The native source copy differs from its frozen input.")
    for name in overlays:
        target = workspace / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink():
            target.unlink()
        shutil.copy2(OWNER / name, target)
        if digest(target) != overlays[name]:
            raise ValueError("An operational overlay changed during copying: " + name)
    configuration = runtime_package.configure(workspace)
    entries = {}
    changed = {}
    route = workspace / "ZesuSsz/Automation/ReturnRoute.v"
    if "ReturnRoute" in selected:
        before = route.read_bytes()
        after, descriptors = instrument_return_route(before.decode(), request["stop"])
        if bounded:
            after, descriptors = bounded_observation(before.decode(), after, descriptors)
        route.write_text(after)
        entries.update(descriptors)
        changed[str(route.relative_to(workspace))] = {"before_sha256": hashlib.sha256(before).hexdigest(), "after_sha256": digest(route)}
    hooks = workspace / "ZesuSsz/Automation/Hooks.v"
    before = hooks.read_bytes()
    after, descriptors, original_step = instrument_hooks(before.decode(), request["stop"], "ConjunctMatch" in selected)
    if "MemoryAccess" in selected:
        memory = workspace / "ZesuSsz/Automation/MemoryAccess.v"
        memory_before = memory.read_bytes()
        after, observed, memory_rows = instrument_memory_access(after, memory_before.decode())
        if bounded:
            observed, memory_rows = bounded_observation(memory_before.decode(), observed, memory_rows)
        memory.write_text(observed)
        entries.update(memory_rows)
        changed[str(memory.relative_to(workspace))] = {
            "before_sha256": hashlib.sha256(memory_before).hexdigest(), "after_sha256": digest(memory)}
    if bounded:
        after, descriptors = bounded_observation(before.decode(), after, descriptors)
        entries = bounded_descriptors(entries)
    hooks.write_text(after)
    entries.update(descriptors)
    changed[str(hooks.relative_to(workspace))] = {"before_sha256": hashlib.sha256(before).hexdigest(), "after_sha256": digest(hooks)}
    prefix, adjustments = switch_adjusted_prefix(workspace, request)
    scratch = workspace / "_build/trace-native" / source.name
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch_prefix = insert_bridge_import(prefix)
    if bounded:
        scratch_prefix = scratch_prefix.replace(package.BRIDGE_IMPORT, runtime_package.BRIDGE_IMPORT)
    scratch.write_text(scratch_prefix + "Abort.\n")
    build = workspace / "_build/agents" / writer
    build.mkdir(parents=True)
    default = workspace / "_build/default"
    default.symlink_to(build / "default", target_is_directory=True)
    imports = sorted({name.replace(".", "/") + ".vo" for name in imported_modules(request["source_prefix"])
                      if name.startswith("ZesuSsz.") and (workspace / (name.replace(".", "/") + ".v")).is_file()})
    targets = sorted(set(imports + [runtime_package.BRIDGE.replace(".v", ".vo")]
        + (["ZesuSsz/Automation/MemoryAccess.vo"] if "MemoryAccess" in selected else [])))
    guard_reference = install_guard_manifest(workspace, entries, bounded=bounded)
    environment = build_environment(workspace, writer)
    environment.update(preparation_guard_environment(workspace, entries, guard_reference, runtime_package))
    opam = shutil.which("opam", path=environment["PATH"])
    if not opam:
        raise ValueError("The pinned opam executable is absent.")
    stages = []
    install_targets = list(getattr(runtime_package, "INSTALL_TARGETS", ("p0-filtered-trace.install", package.WRITER_TARGET)))
    for targets_now in (install_targets, ["zesu-signature-gates.install"], targets):
        command = [opam, "exec", "--switch=/home/cody/islaris", "--", "dune", "build", "--root", str(workspace),
                   "--build-dir", str(build), "--cache=enabled", "-j32", *targets_now]
        print("COMMAND " + json.dumps(command), flush=True)
        started = time.monotonic()
        process = subprocess.run(command, cwd=workspace, env=environment)
        stages.append({"command": command, "exit_code": process.returncode, "elapsed_seconds": time.monotonic() - started})
        save(record_dir / ("BUILD-%02d.json" % len(stages)), stages[-1])
        if process.returncode:
            raise ValueError("The diagnostic dependency build failed. See " + str(record_dir))
    if native_inventory(native) != native_sources:
        raise ValueError("The original native sources changed during preparation.")
    if inventory != source_inventory(original) or digest(source) != request["scope"]["source_sha256"]:
        raise ValueError("The original source scope changed during preparation.")
    findlib = build / "coqc-ocamlpath.json"
    if not findlib.is_file():
        raise ValueError("The private compiler findlib record is absent.")
    record = json.loads(findlib.read_text())
    if record.get("workspace") != str(workspace) or record.get("private_build") != str(build):
        raise ValueError("The private compiler findlib record has a different scope.")
    objects = {str(path.relative_to(build)): digest(path)
               for path in sorted((build / "default").rglob("*.vo")) if path.is_file()}
    objects_file = record_dir / "OBJECTS.json"
    save(objects_file, objects)
    hashes = {name: digest(workspace / name) for name in changed}
    hashes.update({name: digest(workspace / name) for name in configuration})
    hashes.update({name: digest(workspace / name) for name in overlays})
    hashes[str(scratch.relative_to(workspace))] = digest(scratch)
    hashes[str(Path(guard_reference["path"]).relative_to(workspace))] = guard_reference["sha256"]
    runtime = runtime_package.runtime_inputs(workspace, build)
    result = dict(request, **runtime, writer_id=writer, workspace=str(workspace), source=str(scratch), build_dir=str(build),
                  prefix_commands=[request["prefix_text"]] if request["prefix_text"] else [],
                  native_command="all: zesu_block." if request["prefix_text"] else "zesu_block.",
                  step_command="zesu_liAStep", max_steps=4096, entry_descriptors=entries,
                  selected_rules=selected, guard_manifest=guard_reference,
                  preparation_evidence={"original_scope_record": str(record_dir / "INPUTS.json"),
                      "compiled_objects_record": str(objects_file)},
                  instrumentation={"protocol": getattr(runtime_package, "PROTOCOL", "filtered-chunks-v1"), "method": "source-filtered-v1", "schema": 2, "entry_coverage_complete": True, "instruction_coverage_complete": True,
                      "switch_adjustments": adjustments,
                      "changes": changed, "operational_overlays": overlays, "prepared_source_hashes": hashes,
                      "original_scope_sha256": digest(record_dir / "INPUTS.json"),
                      "instruction_checkpoint": "Typed FindInstrKind lookup and requested stop. No executed-instruction claim.",
                      "step_original_sha256": hashlib.sha256(original_step.encode()).hexdigest(),
                      "findlib_record_sha256": digest(findlib),
                      "native_source_count": len(native_sources),
                      "compiled_objects_sha256": digest(objects_file), "compiled_object_count": len(objects)})
    if bounded:
        result["capture_surface_policy"] = "bounded-kernel-v1"
    save(ready, result)
    print("PREPARED " + str(ready), flush=True)
    return result


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("Use trace_block_prepare.py REQUEST.json OUTPUT-DIRECTORY.")
    result = prepare_request(json.loads(Path(sys.argv[1]).read_text()), Path(sys.argv[2]))
    save(Path(sys.argv[2]) / "PREPARED.json", result)
