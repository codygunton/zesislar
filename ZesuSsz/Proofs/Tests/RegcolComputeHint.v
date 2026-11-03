Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.All.

Lemma regcol_symbolic_input_end (Sigma : gFunctors) (args : DecodeItemArgs) :
  LiTactic (regcol_compute_hint (Σ:=Sigma)
    (regcol_lookup (KindReg "zisk_input_end")) (decodeItemSysRegs args)).
Proof. isla.automation.solve_regcol_compute_hint. Qed.

Lemma regcol_symbolic_value (Sigma : gFunctors) (value : bv 64) :
  LiTactic (regcol_compute_hint (Σ:=Sigma)
    (regcol_lookup (KindReg "value"))
    [(KindReg "value", ExactShape (RVal_Bits value))]).
Proof. isla.automation.solve_regcol_compute_hint. Qed.

Lemma regcol_closed_lookup (Sigma : gFunctors) :
  LiTactic (regcol_compute_hint (Σ:=Sigma)
    (regcol_lookup (KindReg "value"))
    [(KindReg "value", BitsShape 64)]).
Proof. isla.automation.solve_regcol_compute_hint. Qed.

Lemma regcol_closed_field (Sigma : gFunctors) :
  LiTactic (regcol_compute_hint (Σ:=Sigma)
    (regcol_lookup_field "status" "bits")
    [(KindField "status" "bits", BitsShape 64)]).
Proof. isla.automation.solve_regcol_compute_hint. Qed.


Lemma regcol_symbolic_field_reduction (args : DecodeItemArgs) :
 regcol_lookup_field "mstatus" "bits" (decodeItemSysRegs args) =
 Some (false, MaskShape 64 131072 0).
Proof. reflexivity. Qed.

Lemma regcol_symbolic_field_hint (Sigma : gFunctors) (args : DecodeItemArgs) :
 LiTactic (regcol_compute_hint (Σ:=Sigma)
   (regcol_lookup_field "mstatus" "bits") (decodeItemSysRegs args)).
Proof. let result := eval hnf in (regcol_lookup_field "mstatus" "bits" (decodeItemSysRegs args)) in
 lazymatch result with Some _ => idtac | _ => fail "The symbolic field lookup did not expose Some." end.
 isla.automation.solve_regcol_compute_hint. Qed.


Print Assumptions regcol_symbolic_input_end.
Print Assumptions regcol_symbolic_value.
Print Assumptions regcol_closed_lookup.
Print Assumptions regcol_closed_field.
Print Assumptions regcol_symbolic_field_reduction.
Print Assumptions regcol_symbolic_field_hint.
