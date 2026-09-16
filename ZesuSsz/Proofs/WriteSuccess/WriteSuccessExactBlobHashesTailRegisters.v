Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.

Lemma blob_tail_registers `{!islaG Sigma} `{!threadG} (count : bv 64) :
  reg_col (list_delete 19%nat writeSuccessBlobHashesBodyOtherRegShapes) ∗
  "x27" ↦ᵣ RVal_Bits count -∗ reg_col writeSuccessBlobHashesOtherRegShapes.
Proof.
  iIntros "[Hregs H27]".
  iAssert (reg_col [(KindReg "x27", BitsShape 64)]) with "[H27]" as "Hcount".
  { rewrite reg_col_cons reg_col_nil. iSplit; last done. iExists _. iFrame. done. }
  iCombine "Hregs Hcount" as "Hall".
  iEval (unfold reg_col; rewrite -big_sepL_app) in "Hall".
  unfold reg_col. iApply (big_sepL_submseteq with "Hall").
  cbn [writeSuccessBlobHashesBodyOtherRegShapes writeSuccessBlobHashesBodyOtherRegisters
    writeSuccessBlobHashesOtherRegShapes writeSuccessBlobHashesOtherRegisters fmap list_delete].
  solve_submseteq.
Qed.
Print Assumptions blob_tail_registers.
