Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

Lemma decodeItemInputEndColumnLookup (Sigma : gFunctors)
    (args : DecodeItemArgs) :
  @LiTactic Sigma _
    (regcol_compute_hint (regcol_lookup (KindReg "zisk_input_end"))
      (decodeItemSysRegs args)).
Proof. typeclasses eauto. Qed.

Print Assumptions decodeItemInputEndColumnLookup.
