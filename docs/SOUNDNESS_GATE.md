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

1. It builds both existing plugins without the Dune cache. It builds the PUBLIC dependency closure with the Dune cache enabled. Then it removes the outputs of the three PUBLIC theorem files and compiles them again with the cache disabled. `PUBLIC-FRESH.json` records the removed outputs and the fresh objects.
2. It compiles five isolated negative candidates and requires the expected checker refusals.
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
Source compilation uses 32 GiB module fences and two Dune workers.
The remaining stages use 24 GiB fences.
Every TMPDIR belongs to the output directory under `/home`.
The proof cache stays disabled.
The Dune cache serves only the PUBLIC dependency closure; the plugins and the PUBLIC theorem files build without it.
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
Compiling the four trust-context files fresh as well (`PUBLIC_CONTEXTS`) would narrow this to definitions outside those files.

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
