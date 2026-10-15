# Free hold-out protocol

This draft protocol is unexecuted. Infra C owns execution.
Record: "contract corrected before run: ownership omitted the 8-byte header".
Checked packet009 owns184 bytes,22 heads, and slot offset `8+8*class`.
Packet008 and the original933 interface/508 metadata counts remain historical.
Artifact packet006 binds packet009. All43 corrected entry applications compiled through MCP.
No native free execution is permitted before `cp-av-rules-frozen`.
The entry is `0x80041f38`. The return blocks are `0x80042144` and `0x80042160`.
The dynamic caller target is `freeReturnAddress args`, not either return-block PC.
Both returns use the 16-byte frame, with x8 at offset0 and ra at offset8.

1. Bind the integrated Root, frozen rule tag, private build, and exact generator files in `RUN-INPUTS.json`.
2. Confirm all 43 signatures against packet008. Seal a new first-run directory before execution.
3. Run discovery, then probe each non-closed native source to completion with unchanged inputs.
4. Preserve every response, error, source hash, compiler record, and first full result.
5. Label later runs after a rule change as training. Never overwrite the first hold-out result.

Artifact packet006 supplies exact design, premises, terminal descriptor, and byte/CFG bindings.
The trace import is `ZesuSsz.Stock.Free.index_free`.
The selected-code import is `ZesuSsz.Contracts.FreeSelected`.
The application report010 binds the corrected sources and all43 applications.
Its ten bindings and packet006's fourteen bindings match.
Health and normal owner closure passed. No Pet or native proof ran.
The integration identity and frozen-rule tag remain pending. Native readiness remains pending.
Root4073c8d3 supports `--terminal-descriptor`; use the bound free descriptor.
`RUN-INPUTS.json` records exact packet paths and hashes. Earlier packets remain historical.

## Store prediction after R2 failure

[Issue13 comment6183989697](https://github.com/codygunton/zesislar/issues/13#issuecomment-6183989697) closes Phase1 R2 as failed.
[Supplement6184005012](https://github.com/codygunton/zesislar/issues/13#issuecomment-6184005012) binds the final candidate and measurements.
R2 stays disabled. Stores are a hand prediction for this unexecuted free hold-out.
The literal frame stores at0x80041f3c/0x80041f40 belong to block0x80041f38.
The buffer store at0x80042174 and indexed state store at0x80042178 belong to block0x80042160.
All four stores have width8. The two data stores share one return block.
The buffer address is x11+0. The state address is x10+8 after x10=stateBase+(class<<3).
These are static input facts and predictions, not running proof results.
No exact hand-line count is predicted. All measured fields remain null.
Preserve an unexpected native closure as a finding. Do not revise the frozen first result.

## Discovery

Bind each `FREE_*` variable from the input seal. These commands were not executed.
The `${name:?message}` expressions reject missing input values.

```sh
cd "${FREE_WORKSPACE:?Bind private workspace}"
FREE_RULE_FREEZE="$(git rev-parse 'cp-av-rules-frozen^{commit}')"
test "$FREE_RULE_FREEZE" = "${FREE_EXPECTED_FREEZE:?Bind sealed freeze SHA}" || exit 1
test ! -e "${FREE_RUN:?Bind new private run directory}" || exit 1
ai-coord watch --label infra-c-free-first-discovery -- \
  env -u ZESU_IN_GATE ZESU_WRITER_ID="${FREE_WRITER_ID:?Bind admitted writer}" \
  python tools/block/discovery.py \
  --design "${FREE_DESIGN:?Bind checked free design}" \
  --cfg build/stock-zisk/cfg.json --manifest build/stock-zisk/build-recipe.json \
  --terminal 'freeReturnAddress args' \
  --terminal-descriptor "${FREE_TERMINAL_DESCRIPTOR:?Bind corrected free descriptor}" \
  --trace-import "${FREE_TRACE_IMPORT:?Bind compiled free trace module}" \
  --code-premises "${FREE_CODE_PREMISES:?Bind exact free code premises}" \
  --binding-report "${FREE_BINDING_REPORT:?Bind successful binding report}" \
  --probe-import ZesuSsz.Compliance.FreeHints \
  --probe-import ZesuSsz.Contracts.FreeSelected \
  --build-dir "${FREE_BUILD_DIR:?Bind absolute private build directory}" \
  --out "$FREE_RUN" --jobs 6 --seconds 300
```

The 300-second value is an API discovery budget. A budget failure is not a proof rejection.
The first full frozen-rule result includes discovery and its completion probes.

## Completion probes

Bind the exact retained native source and a new block output directory.
Use the same frozen statement, imports, and rules.

```sh
test ! -e "${FREE_PROBE_OUT:?Bind new block output directory}" || exit 1
ai-coord watch --label "${FREE_PROBE_LABEL:?Bind unique watcher label}" -- \
  env -u ZESU_IN_GATE ZESU_WRITER_ID="$FREE_WRITER_ID" \
  ZESU_DIAGNOSTIC_PROBE=1 ZESU_PROBE_ISSUE=10 \
  ZESU_PROOF_CPU_LIMIT=unlimited ZESU_PRIMARY_CPU_LIMIT=none \
  ZESU_PRIMARY_WALL_LIMIT=none ZESU_SCRATCH_WALL_SECONDS=none \
  ZESU_PRIMARY_MEMORY_GIB=64 ZESU_SCRATCH_MEMORY_GIB=64 ZESU_MODULE_LIMIT_GIB=64 \
  python tools/block/coqc_primary.py \
  --compile "${FREE_NATIVE_SOURCE:?Bind retained native source}" --build-dir "$FREE_BUILD_DIR" \
  --out "$FREE_PROBE_OUT" --diagnostic-probe --memory-gib 64
```

Record issue10 policy and actual process limits. Measure one probe before a parallel batch.
Use the smaller of 48 and the memory-derived safe worker count. Retain guard admission limits.
Record compiler CPU, wall time, peak RSS, exit code, and the exact residual.
Separate setup and admission time from compiler time.
`coqc_primary.py` certifies module compilation only. Its missing native goal groups remain unavailable.
Require all four MCP groups, actual Qed, exact statement SHA verification, assumptions, and normal owner closure.
Keep explicit theorem premises separate from `Print Assumptions`.
A fifth residual pattern changes the function's role to training. Preserve the original result.
This protocol does not authorize alloc block reads.
