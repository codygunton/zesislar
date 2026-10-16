The Phase 3d installation remains unproved.

```coq
Lemma NextUint64CalleeInstallation :
  ZesuSsz.Contracts.NextUint64Selected.nextUint64SelectedCode -∗
  □ instr_pre 0x800d6960 NextUint64CallState800d62b4.
```

The observation retains one goal. The stack, shelf, and given-up groups are empty.
The controller executes `idtac.` only. It executes zero machine instructions.
The caller and `decodeItem` remain unexecuted.
