"""Reject native scratches that omit their declared function hints or switches."""
import argparse
import hashlib
import json
from pathlib import Path

from check_data_only_lemmas import command_imports, rocq_commands


APPROVED = "ZesuSsz.Automation.Approved"


def function_hints(function, workspace):
    """Select the single Hints source in the function's registrations list."""
    root = Path(workspace).resolve()
    if not isinstance(function, str) or not function:
        raise ValueError("The native launch needs an explicit function name.")
    matches = []
    for path in sorted((root / "ZesuSsz/Evidence").glob("*_function_text.json")):
        manifest = json.loads(path.read_text())
        declared = manifest.get("function")
        # The original decodeItem manifest uses the unqualified inventory name.
        if declared == function or (isinstance(declared, str) and "." not in declared
                                    and declared == function.rsplit(".", 1)[-1]):
            matches.append((path, manifest))
    if len(matches) != 1:
        raise ValueError("The native launch needs one function manifest: " + function)
    path, manifest = matches[0]
    registrations = manifest.get("registrations")
    if not isinstance(registrations, list) or any(not isinstance(item, str)
                                                  for item in registrations):
        raise ValueError("Invalid registrations in " + path.name)
    umbrellas = [item for item in registrations if Path(item).name.endswith("Hints.v")]
    if len(umbrellas) != 1:
        raise ValueError("The manifest must list one hint umbrella: " + path.name)
    umbrella = (root / umbrellas[0]).resolve()
    compliance = (root / "ZesuSsz/Compliance").resolve()
    if (not umbrella.is_relative_to(compliance) or
            not umbrella.is_relative_to(root) or not umbrella.is_file()):
        raise ValueError("The hint umbrella is not a Compliance source: " + umbrellas[0])
    module = ".".join(umbrella.relative_to(root).with_suffix("").parts)
    return path, umbrella, module


def require_modules(source):
    """Read explicit Require commands before the first proof body."""
    modules = set()
    for command in rocq_commands(source):
        values = [token for token, _ in command]
        if values and values[0] == "Proof":
            break
        if values and (values[0] == "Require" or
                       (values[0] == "From" and len(values) > 2 and values[2] == "Require")):
            position = values.index("Require") + 1
            if position < len(values) and values[position] not in {"Import", "Export"}:
                values.insert(position, "Import")
            imported, _ = command_imports(values)
            modules.update(imported)
    return modules


def validate_launch_imports(source, function, workspace):
    """Check the actual scratch without adding imports or running proof tools."""
    manifest, umbrella, module = function_hints(function, workspace)
    required = [module, APPROVED]
    imported = require_modules(source)
    missing = [name for name in required if name not in imported]
    if missing:
        raise ValueError("The native scratch omits required imports: " + ", ".join(missing))
    return {"function": function, "required": required,
            "inputs": {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in (manifest, umbrella)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--function", required=True)
    parser.add_argument("--workspace", type=Path, default=Path.cwd())
    args = parser.parse_args()
    checked = validate_launch_imports(args.source.read_text(), args.function, args.workspace)
    print(json.dumps(checked, sort_keys=True))


if __name__ == "__main__":
    main()
