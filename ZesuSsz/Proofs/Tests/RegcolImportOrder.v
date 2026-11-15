Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Automation2.All.

(* A system-register collection over a record projection of a variable keeps the projection
   when Lithium computes its lookup, also after a later import of isla's automation (which
   reinstates upstream's VM hint body). *)
Module after_isla_import.
Import isla.riscv64.riscv64.

Lemma regcol_projection_kept `{!islaG Sigma} (args : ParentHeaderArgs) :
  ⊢ li_tactic (regcol_compute_hint (Σ:=Sigma) (regcol_extract (KindReg "zisk_input_end")) (parentHeaderSysRegs args))
      (λ p : valu_shape * list (reg_kind * valu_shape), ⌜p.1 = ExactShape (RVal_Bits (parentHeaderInputEnd args))⌝).
Proof.
  iStartProof. liTactic. liSimpl.
  tryif (match goal with |- context [match args with _ => _ end] => idtac end)
  then fail "The lookup unfolded the record projection" else idtac.
  lazymatch goal with |- context [parentHeaderInputEnd args] => idtac end.
  by iPureIntro.
Qed.
Print Assumptions regcol_projection_kept.
End after_isla_import.
