# Level 1 boundary evidence

The QEMU trace plugin observes the unchanged production RV64 ELF. The Nix target
zesuSszDecodeLevel1Evidence obtains snapshot PCs exclusively from the generated Level 1 manifest,
runs one successful and one rejected SSZ input, and records:

- all integer registers whenever an exercised Level 1 entry is reached;
- executed PCs and concrete load/store address, width, and value records;
- observed transitions leaving each generated Level 1 execution extent;
- the exact observed dynamic interval from `ssz.decode` entry to `writeSuccess` or `writeFailure`,
  including its step count, changed integer registers, and success result address;
- the exact production ELF SHA-256 digest.

The analyzer requires the union of vectors to reach every selected Level 1 entry. Its tests reject a
different ELF, a deleted entry snapshot, and malformed records. The report is admission evidence,
not a theorem premise: it explicitly leaves universal path coverage, step bounds, complete register
and memory frames, and the semantic result relation unmeasured. Contract-specific checkers must add
source-probe expectations before any of those clauses can appear in Level1ContractAssumptions.

The Rocq port keeps the shared tools byte-identical to `binary-fv-experiment@38a3a14a`.
`contracts/level1-evidence-parity.json` records their reviewed hashes.

`generate_level1_rocq.py` replaces the Lean boundary generator.
Nix regenerates `ZesuSsz/Generated/Level1.v` and rejects any difference.
The Level 1 contracts import that file for their execution regions and exit PCs.

`generate_write_success_certificate.py` checks the pinned `writeSuccess` CFG.
It rejects unknown edges, missing exits, changed ELF data, and PCs outside the Level 1 region.
It emits the complete instruction graph and a concrete entry-to-exit Rocq witness.
Nix regenerates both certificate files and rejects any difference.

The `level1-viewer-data` Nix package contains all Level 1 review data.
Its checker rejects any proof claim.

The evidence derivation runs QEMU with an empty guest environment.
This keeps the initial guest stack address independent of Nix builder variables.
The derivation generates two complete trace sets and requires byte equality.
It also generates two JSON reports and requires byte equality.

`contract_evidence.py` supplies the shared contract-checking framework.
The `zkvm_exit` checker tests the entry code, terminal PC, exit-code store, memory frame, stdout frame, and step count.
The `writeFailure` checker tests failure encoding, output writes, the return PC, the memory frame, and preserved integer registers.
The remaining checkers cover `readInput`, `allocatorGet`, `sszDecode`, and `writeSuccess`.
They test concrete ABI values, memory frames, outcomes, output framing, and observed step counts.
Each report separately lists the clauses that the current trace cannot measure.
