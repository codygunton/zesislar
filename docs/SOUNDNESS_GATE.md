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
It copies no compiled project object into the build itself.
The dependency closure may restore objects from the Dune cache (stage 1).
Existing local trace sources need no `--trace-source` option.
The script refuses an existing output directory.

The gate performs these stages:

1. It keeps the Dune cache enabled in every step, because Dune reruns every rule when the cache mode changes.
   It builds both existing plugins from the cache: a fresh native plugin records its worktree path and changes every Coq rule digest.
   It builds the dependencies of the three PUBLIC theorem files from the cache, without the PUBLIC files themselves.
   Then it builds the PUBLIC files with the reproducibility check: Dune reruns `coqc` for each file.
   The compiler route keeps each new object before Dune links the target to an equal cache entry.
   `PUBLIC-FRESH.json` records, for each PUBLIC object, the `coqc` run from the Dune trace and the hashes of the fresh object and of the object in `_build`.
   The gate fails when a run is absent or when the two hashes differ.
2. It compiles five isolated negative candidates and requires the expected checker refusals.
   Each MCP compile may run 600 s once the guard admits it; the guarded compiler wrappers start that limit inside the guard scope.
   A separate allowance (`ZESU_ADMISSION_WAIT_SECONDS`, default 7200 s) bounds the admission wait. A call that exceeds it is logged and retried, up to `ZESU_ADMISSION_RETRIES` (default 3) times.
3. It verifies the four protected PUBLIC statements and compiles four checker-owned typed wrappers
   (selected, registers, compositional, and the generated theorem).
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

The gate pins its PUBLIC sources and trust contexts to the reviewed `d73a7a5a` baseline,
the switch of the PUBLIC theorems to the 24 generated block proofs (the earlier baseline was `dbefab79`).
It refuses a changed protected source before proof work.
A maintainer must review that boundary before updating the baseline.
It verifies each PUBLIC source independently.
This avoids selecting an unrelated generated module as a statement target.

Each stage uses existing canonical admission and guard tools.
The aggregate claim and fence are 64 GiB.
Source compilation uses two Dune workers.
The source stage uses 16 GiB module fences: closure callers peak at 10.9 GiB. The negative and wrapper stages use 8 GiB fences; their compiles peak at most 1.25 GiB.
The coqchk stage uses a 24 GiB fence.
Every TMPDIR belongs to the output directory under `/home`.
The proof cache stays disabled.
The Dune cache serves the PUBLIC dependency closure and the plugins; the PUBLIC theorem files compile again in the gate.
The script freezes source receipts before the verification stages.
It preserves raw MCP responses, exact types, object hashes, costs, actor closure, and claim release.
It checks that `coqchk` changes no project object.
It stops at the first failed stage and retains the attempt.

## Cache trust

A Dune cache entry is keyed by the digests of the compile action's inputs: the source file, the dependency objects, and the compiler command.
A cached dependency object therefore comes from an earlier compile of the same source with the same dependencies, if the local cache is intact.
Recursive `coqchk` re-checks every object, cached or fresh, against the kernel.
A cached object cannot add an unchecked proof or a hidden axiom: `coqchk` rejects an ill-typed term, and the wrapper assumption reports must stay closed.
`coqchk` does not compare an object with its source file.
A tampered cache entry could therefore change a dependency definition that a PUBLIC statement unfolds to, while every term still checks.
The fresh compile of the PUBLIC theorem files, together with the statement checks against the reviewed baseline source, binds the statements themselves; the definitions they unfold to rely on the integrity of the account's Dune cache.
The gate does not rely on Dune's handling of a reproducibility mismatch: it compares the fresh object with the object in `_build` itself.
Compiling the trust-context files fresh as well (`PUBLIC_CONTEXTS`, option `--fresh-contexts`) narrows this to definitions outside those files.
The option takes only the context files inside the PUBLIC closure; `Evidence/SignatureGates.v` is outside it, so no PUBLIC term can come from it.
Every closure object above a fresh file then compiles in the fresh step too.

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
