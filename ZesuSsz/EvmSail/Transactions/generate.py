#!/usr/bin/env python3
"""Stage bounded, decoder-only Sail slices at the pinned upstream revisions."""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "Rlp"))
from generate import EVM_REVISION, SAIL_REVISION, check_source, digest

ROOTS = ("decode_legacy_tx", "decode_access_list_tx", "decode_fee_market_tx",
         "decode_blob_tx", "decode_set_code_tx", "rlp_decode_tx")
EXTERNS = {
    "host/scratch.sail": (
        "host_scratch_reserve", "host_scratch_store_byte",
        "host_scratch_store_stateless_input", "host_scratch_store_word",
        "host_scratch_truncate"),
    "primitives/crypto.sail": (
        "stateless_input_keccak256", "scratch_keccak256"),
}
FIELD_TYPE = {
    "tx_type": "TxType", "sender": "address", "raw": "StatelessInputSlice",
    "nonce": "word", "chain_id": "chain_identifier", "gas_limit": "transaction_gas",
    "is_create": "bool", "recipient": "address", "value": "word",
    "input_src": "TransactionInputSlice", "access_list": "AccessListRef",
    "max_fee": "word", "max_blob_fee": "word", "max_priority_fee": "word",
    "authorizations": "AuthorizationListRef",
    "blob_hashes": "BlobHashesFields('blob_limit)", "pubkey": "StatelessInputSlice",
    "signing_hash": "hash", "sig_v": "word", "sig_r": "word", "sig_s": "word",
}


def stage_transactions(original):
    staged = original
    helper_args = ",\n    ".join(f"{name} : {kind}" for name, kind in FIELD_TYPE.items())
    helper_fields = ",\n        ".join(f"{name} = {name}" for name in FIELD_TYPE)
    helper = ("/* Stage-only pure record extraction; call sites reconstruct source fields. */\n"
              "function staged_tx_record forall 'blob_limit, "
              "transaction_blob_limit_value('blob_limit). (\n    " + helper_args +
              "\n) -> TransactionFields('blob_limit) = struct {\n        " +
              helper_fields + "\n}\n\n")
    first = staged.index("function decode_legacy_tx forall")
    staged = staged[:first] + helper + staged[first:]
    for root in ROOTS[:-1]:
        start = staged.index(f"function {root} forall")
        end = staged.index("\n}\n", start) + 2
        body = staged[start:end]
        source_body = body
        matches = list(re.finditer(
            r"    let (\w+_f) = rlp_decode_item\(fields\);\n"
            r"    let fields = rlp_cursor_advance\(fields, \1.source.len\);\n", body))
        assert len(matches) >= 9, (root, len(matches))
        assert all(matches[i].end() == matches[i + 1].start() for i in range(len(matches) - 1))
        count = len(matches) // 2
        prefix = body[matches[0].start():matches[count - 1].end()]
        names = [match.group(1) for match in matches[:count]]
        anchor = names[0]
        cap = ''.join(word.title() for word in root.split('_'))
        any_type = cap + "AnyField"
        prefix_type = cap + "PrefixFields"
        existential_type = cap + "Prefix"
        field_lines = [f"    {anchor} : RlpFieldRef('first_off, 'first_len, 'first_content),"]
        field_lines += [f"    {name} : {any_type}," for name in names[1:]]
        field_lines += ["    fields : RlpCursor('next_off, 'next_len),"]
        pack_args = [f"    {anchor} : RlpFieldRef('first_off, 'first_len, 'first_content),"]
        pack_args += [f"    {name} : {any_type}," for name in names[1:]]
        pack_args += ["    fields : RlpCursor('next_off, 'next_len)"]
        pack_fields = ", ".join(f"{name} = {name}" for name in names + ["fields"])
        params = ", ".join(names + ["fields"])
        decl = f'''/* Typed handoff after {count} of {len(matches)} {root} fields. */
type {any_type} = {{
    'off 'full 'content, rlp_field_ref_valid('off, 'full, 'content).
    RlpFieldRef('off, 'full, 'content)
}}

struct {prefix_type}(
    'first_off : Int, 'first_len : Int, 'first_content : Int,
    'next_off : Int, 'next_len : Int
), rlp_field_ref_valid('first_off, 'first_len, 'first_content)
   & source_valid_range('next_off, 'next_len)
   & 'first_off <= 'next_off = {{
{chr(10).join(field_lines)}
}}

type {existential_type} = {{
    'first_off 'first_len 'first_content 'next_off 'next_len,
    rlp_field_ref_valid('first_off, 'first_len, 'first_content)
    & source_valid_range('next_off, 'next_len)
    & 'first_off <= 'next_off.
    {prefix_type}('first_off, 'first_len, 'first_content, 'next_off, 'next_len)
}}

function {root}_prefix_pack forall
    'first_off 'first_len 'first_content 'next_off 'next_len,
    rlp_field_ref_valid('first_off, 'first_len, 'first_content)
    & source_valid_range('next_off, 'next_len)
    & 'first_off <= 'next_off. (
{chr(10).join(pack_args)}
) -> {prefix_type}('first_off, 'first_len, 'first_content, 'next_off, 'next_len) =
    struct {{ {pack_fields} }}

function {root}_prefix forall 'source_off 'source_len,
    source_valid_range('source_off, 'source_len). (
    fields : RlpCursor('source_off, 'source_len)
) -> {existential_type} = {{
{prefix}    {root}_prefix_pack({params})
}}

'''
        wrapper = (f"    let prefix = {root}_prefix(fields);\n" +
                   ''.join(f"    let {name} = prefix.{name};\n" for name in names) +
                   "    let fields = prefix.fields;\n")
        assert body.count(prefix) == 1
        body = body.replace(prefix, wrapper, 1)
        record_start = body.index("    struct {\n        tx_type = ")
        record_end = body.index("\n    }", record_start) + len("\n    }")
        record = body[record_start:record_end]
        parsed = dict(re.findall(r"^        (\w+) = (.*?),$", record, re.MULTILINE))
        assert set(parsed) == set(FIELD_TYPE), (root, set(FIELD_TYPE) - set(parsed))
        call = "    staged_tx_record(\n        " + ",\n        ".join(parsed[name] for name in FIELD_TYPE) + "\n    )"
        body = body[:record_start] + call + body[record_end:]
        assert body.replace(call, record, 1).replace(wrapper, prefix, 1) == source_body
        staged = staged[:start] + decl + body + staged[end:]
    return staged


def bounded(command, cwd, env, log, stdin=None):
    started = time.monotonic()
    peak = 0
    with log.open("w") as stream:
        proc = subprocess.Popen(command, cwd=cwd, env=env, stdin=stdin,
                                stdout=stream, stderr=subprocess.STDOUT)
        while proc.poll() is None:
            try:
                status = Path(f"/proc/{proc.pid}/status").read_text()
                peak = max(peak, int(next(line.split()[1] for line in status.splitlines()
                                         if line.startswith("VmRSS:"))))
            except (FileNotFoundError, StopIteration):
                pass
            if time.monotonic() - started >= 60 or peak > 2097152:
                proc.kill()
                break
            time.sleep(0.1)
        proc.wait()
    elapsed = round(time.monotonic() - started, 3)
    return {"seconds": elapsed, "peakRssKiB": peak, "exit": proc.returncode,
            "withinLimits": elapsed < 60 and peak <= 2097152 and proc.returncode == 0}


def extern_declarations(source):
    declarations = []
    for file, names in EXTERNS.items():
        content = (source / file).read_text()
        for name in names:
            pattern = rf"^val {name}\s*=.*?\s:\s*(.*?)(?=\n(?:/\*!|val |function |\n)|\Z)"
            match = re.search(pattern, content, re.MULTILINE | re.DOTALL)
            assert match, (file, name)
            declarations.append({
                "name": name, "source": "sail/" + file,
                "line": content.count("\n", 0, match.start()) + 1,
                "declaredType": " ".join(match.group(1).split()),
            })
    return declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evm-source", type=Path, required=True)
    parser.add_argument("--sail-source", type=Path, required=True)
    parser.add_argument("--sail-build", type=Path, required=True)
    parser.add_argument("--build-dir", type=Path, required=True)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--compile-only", action="store_true")
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    if args.publish and not args.compile_only:
        parser.error("--publish requires --compile-only")
    repo = Path(__file__).resolve().parents[3]
    check_source(args.evm_source, EVM_REVISION)
    check_source(args.sail_source, SAIL_REVISION)
    compiler = args.sail_build / "default/src/bin/sail.exe"
    plugin = args.sail_build / "default/src/sail_coq_backend/sail_plugin_coq.cmxs"
    assert SAIL_REVISION in subprocess.check_output([compiler, "--version"], text=True)
    stage = args.stage.resolve()
    assert stage.is_relative_to((repo / "build/tx-handoff").resolve())
    if not args.compile_only:
        shutil.rmtree(stage, ignore_errors=True)
        shutil.copytree(args.evm_source / "sail", stage / "source")
        shutil.copy(repo / "ZesuSsz/EvmSail/Transactions/decoder.sail_project",
                    stage / "source/decoder.sail_project")
        shutil.copytree(repo / "ZesuSsz/EvmSail/Rlp/shim", stage / "source/shim")
        (stage / "sail").mkdir()
        (stage / "sail/lib").symlink_to(args.sail_source.resolve() / "lib", target_is_directory=True)
        tx = stage / "source/lib/rlp/codecs/transactions.sail"
        source = tx.read_text()
        tx.write_text(stage_transactions(source))
    env = os.environ.copy()
    env.update(SAIL_NO_PLUGINS="1", SAIL_DIR=str(stage / "sail"))
    env["PATH"] = str(repo / "bin") + os.pathsep + env["PATH"]
    if not args.compile_only:
        (stage / "output").mkdir()
        results = {}
        for root in ROOTS:
            module = "evm_" + root
            commands = (f":slice_roots {root} initialize_registers\n:slice_keep_std\n"
                        f":slice\n:recheck_types\n:rewrites coq\n:target coq, {module}\n:quit\n")
            command_file = stage / f"{root}.commands"
            command_file.write_text(commands)
            with command_file.open() as stream:
                result = bounded([str(compiler), "--plugin", str(plugin),
                                  "--coq-semantic-range-types", "--coq-undef-axioms",
                                  "--coq-output-dir", "output", "--project",
                                  "source/decoder.sail_project", "--all-modules",
                                  "--interact-custom"], stage, env,
                                 stage / f"{root}.log", stream)
            results[root] = {"generation": result}
            if not result["withinLimits"]:
                break
    else:
        results = json.loads((stage / "results.json").read_text())
        stdpp = args.build_dir.resolve() / "default/generated/sail-stdpp"
        assert (stdpp / "Real.vo").is_file()
        for root in ROOTS:
            module = "evm_" + root
            for name in (module + "_types.v", module + ".v"):
                result = bounded(["opam", "exec", "--switch=/home/cody/islaris",
                                  "--", "coqc", "-Q", str(stdpp), "SailStdpp",
                                  "-Q", "output", "", "-time", "output/" + name],
                                 stage, env, stage / (name + ".log"))
                results[root][name] = result
                if not result["withinLimits"]:
                    break
            if not all(item["withinLimits"] for key, item in results[root].items()
                       if key != "generation"):
                break
    (stage / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    if args.publish:
        if set(results) != set(ROOTS) or not all(
                set(results[root]) == {
                    "generation", "evm_" + root + "_types.v", "evm_" + root + ".v"
                } and all(item["withinLimits"] for item in results[root].values())
                for root in ROOTS):
            raise SystemExit("Only fully bounded, compiled slices can be published.")
        output = repo / "generated/evm-sail-coq/transactions"
        output.mkdir(parents=True, exist_ok=True)
        modules = {}
        reached = {}
        known_externs = {name for names in EXTERNS.values() for name in names}
        for root in ROOTS:
            module = "evm_" + root
            for name in (module + "_types.v", module + ".v"):
                shutil.copyfile(stage / "output" / name, output / name)
                modules[name] = digest(output / name)
            body = (output / (module + ".v")).read_text()
            assert re.search(rf"^Definition {root}\b", body, re.MULTILINE)
            reached[root] = sorted(set(re.findall(r"^Axiom (\w+)\s*:", body,
                                                 re.MULTILINE)))
            if not set(reached[root]) <= known_externs:
                raise SystemExit(f"Unaudited extern reached by {root}: {reached[root]}")
        manifest = {
            "evmSailRevision": EVM_REVISION,
            "sailCompilerRevision": SAIL_REVISION,
            "sailCompilerSha256": digest(compiler),
            "sailCoqPluginSha256": digest(plugin),
            "projectSha256": digest(repo / "ZesuSsz/EvmSail/Transactions/decoder.sail_project"),
            "stagedTransactionsSha256": digest(stage / "source/lib/rlp/codecs/transactions.sail"),
            "inputShimSha256": digest(stage / "source/shim/input.sail"),
            "sourceRelation": "Each field-walk and record replacement reconstructs the pinned source text exactly.",
            "roots": ROOTS,
            "c4PremiseCandidates": extern_declarations(args.evm_source / "sail"),
            "reachedExternsByRoot": reached,
            "measurements": results,
            "modulesSha256": modules,
        }
        (output / "SOURCE.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
