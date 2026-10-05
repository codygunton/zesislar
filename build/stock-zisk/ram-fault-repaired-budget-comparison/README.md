The comparison uses root `fe24838e24461aaa028e0dd8a33fac4e062a2692`.
Both arms use the same domain and generated source bodies.
The arms differ only in the RamFault import.
The report measures the full RamFault switch.

The driver separates preparation from the primary tactic.
Preparation receives 60 seconds.
The single `try zesu_block.` call receives exactly 300 seconds.
The report records SDK hashes, call arguments, and sentence budgets.
SDK division is the leading explanation for historical 21-second timeouts.
The historical batch divided 299 seconds across 14 sentences.
The historical root differs, so this report makes no sole-budget causal claim.

The off arm records these block classes:

- Twelve blocks reach abstract successors.
- Five blocks stall at entry.
- Three blocks stall during execution.
- Three blocks have no interactive primary state.
- ROOT has a successful primary and incomplete recorder output.

The on arm records these block classes:

- Twelve blocks reach abstract successors.
- Five blocks stall at entry.
- Three blocks stall during execution.
- Four blocks have no interactive primary state.

Twenty blocks execute in both arms with identical class sets.
No contract closes.
An abstract successor reach does not establish contract closure.
Both ROOT off calls succeed in approximately 44 seconds.
SDK feedback truncation prevents a known boundary class for those calls.
ROOT on has no interactive primary state.
The comparison establishes no ROOT switch effect.

The resumed run reuses 20 completed boundaries.
It executes only the 56 missing boundaries.
The exporter saves complete feedback and keeps SDK responses unchanged.
The client checks exported hashes before it parses recorder output.
The four capture tests include the frozen malformed ROOT tail.

The resumed probes take 280.146 seconds with six workers.
The maximum recorded worker RSS is 2021.473 MiB.
Machine CPU activity averages 12.210 percent during the resumed probes.
That measurement includes other machine jobs.
Admission wait was not measured.
Pet memory remains unknown when startup returns no process identifier.
The interrupted attempt did not save separate Pet diagnostics for reused captures.

`report.json` retains bounded metadata and hashes for exact residuals.
`archive-index.json` binds full calls, feedback, source files, and logs.
The archive stores each artifact under its SHA-256 hash.
The measured generator files remain in the archive.
Three policy strings changed after execution.
Those changes do not alter invocation or parsing logic.
`manifest-fragment.json` supplies records for coordinator binding.

The report binds all 109 original file hashes.
It retains payloads for 80 primary capture files and 26 other original files.
Three original activation payloads are unavailable.
Those files are `activation.json` and the two activation `.aux` files.
The report binds their original hashes and replacement artifacts separately.
The replacement activation checks pass.
All 62 recorded primary calls succeed with the isolated 300-second budget.
The maximum primary time is 44.457 seconds.
No recorded primary reaches a genuine tactic timeout.
The report closes the historical timeout classification as a tooling artifact.
The report records the coordinator-reported spec review separately.
