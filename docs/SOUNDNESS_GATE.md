# PUBLIC soundness gate

Run `tools/soundness_gate.py` with the pinned opam environment and the Python interpreter that owns `rocq-mcp`.
Use a new isolated worktree for each invocation.
The worktree must have no tracked changes.

```sh
ai-coord watch --label soundness-release -- \
  "$MCP_PYTHON" -B tools/soundness_gate.py \
  --output "$PWD/_build/agents/soundness-release" \
  --source-workspace "$SOURCE_WORKSPACE" \
  --trace-source "$TRACE_SOURCE"
```

`SOURCE_WORKSPACE` owns the pinned guest, Zesu, and Zisk source checkouts.
`TRACE_SOURCE` supplies the trace sources that the tracked build recipe binds.
The script checks every trace hash before staging.
It copies no compiled project object into the fresh build.
Existing local trace sources need no `--trace-source` option.
The script refuses an existing output directory.

The gate performs these stages:

1. It builds both existing plugins, then the PUBLIC dependency closure.
2. It compiles five isolated negative candidates and requires the expected checker refusals.
3. It verifies the four protected PUBLIC statements and compiles four checker-owned typed wrappers.
4. It runs recursive `coqchk` with the compiler recipe's supported load-path flags.

The negative candidates cover `Admitted`, an extra axiom, installed `Coq.Compat.AdmitAxiom`, a wrong statement, and a doctored expected type.
An unavailable import or failed candidate compilation does not pass a negative control.
The checker expects `False` in both statement controls, independently of each candidate.
Every positive `module_m` check requires an empty assumption list.
All four wrapper assumption reports must say `Closed under the global context`.
The gate supplies no external axiom allowlist.
The wrapper source stays under the owned output's `scratch/` directory.
The compiler uses its existing private artifact mapping.
`coqchk` receives one exact load-path entry for that scratch object.
The gate leaves no wrapper source in the production tree.

The gate pins its PUBLIC sources and trust contexts to the reviewed `dbefab79` baseline.
It refuses a changed protected source before proof work.
A maintainer must review that boundary before updating the baseline.
It verifies each PUBLIC source independently.
This avoids selecting an unrelated generated module as a statement target.

Each stage uses existing canonical admission and guard tools.
The aggregate claim and fence are 64 GiB.
Source compilation uses 32 GiB module fences and two Dune workers.
The remaining stages use 24 GiB fences.
Every TMPDIR belongs to the output directory under `/home`.
Both caches stay disabled.
The script freezes source receipts before the verification stages.
It preserves raw MCP responses, exact types, object hashes, costs, actor closure, and claim release.
It checks that `coqchk` changes no project object.
It stops at the first failed stage and retains the attempt.

This gate checks the PUBLIC closure.
It does not replace `make check-fast` or the full `make check-iris` gate.

The stock gates use the repository's build Python, which needs `pyelftools`.
Keep that interpreter separate from the MCP interpreter.
Put the stock tests' TMPDIR under an owned `/home` path outside Git, Dune, and ai-coord roots.
Otherwise, temporary fixtures can inherit the real workspace.
If system tools differ from the tracked pins, use the existing private tool namespace.
Do not change the pins or shared tool paths.

The accepted `dbefab79` measurement used these aggregate CPU costs:

| Stage | CPU seconds |
| --- | ---: |
| Fresh source closure | 6898.630738 |
| Typed wrappers | 203.121850 |
| Recursive coqchk | 382.844395 |

Those figures exclude earlier failed attempts and the separate negative controls.
Each new run records its own wall time, CPU time, and peak memory.
