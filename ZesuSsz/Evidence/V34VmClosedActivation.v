Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation.VmClosed.
Open Scope Z_scope.
Lemma regcol_switch_off (Sigma : gFunctors) :
  LiTactic (regcol_compute_hint (Σ:=Sigma) (fun n : nat => Some (S n)) 0%nat).
Proof.
  Fail ZesuSsz.Automation.Hooks.zesu_regcol_compute_vm_if_enabled.
  typeclasses eauto.
Qed.
#[local] Instance vm_compute_enabled :
  ZesuSsz.Automation.Hooks.ZesuStepRegcolVMCompute := {}.
Set Ltac Profiling.
Lemma closed_scalar_proofs :
  (3 <= 4)%nat /\ (8 <= 64)%N /\
  bv_unsigned (Z_to_bv 64 (3 + 4)) = 7.
Proof.
  split; [ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide |].
  split; ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide.
Qed.
Lemma regcol_ground (Sigma : gFunctors) :
  LiTactic (regcol_compute_hint (Σ:=Sigma) (fun n : nat => Some (S n)) 0%nat).
Proof. typeclasses eauto. Qed.
Lemma regcol_symbolic (Sigma : gFunctors) (input : Z) :
  LiTactic (regcol_compute_hint (Σ:=Sigma) (fun value : Z => Some value) input).
Proof.
  Fail ZesuSsz.Automation.Hooks.zesu_regcol_compute_vm_if_enabled.
  typeclasses eauto.
Qed.
Lemma evaluator_guards : True.
Proof.
  let value := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed constr:((2 + 3)%N) in
  constr_eq value constr:(5%N).
  assert (Hsymbolic : forall input : Z, True) by
    (intros input; assert_fails ltac:(solve [let value := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed constr:(input) in idtac value; exact I]); exact I).
  clear Hsymbolic.
  Fail assert (Hfalse : (2 = 3)%Z) by ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide.
  exact I.
Qed.
Show Ltac Profile CutOff 0.
Print Assumptions regcol_switch_off.
Print Assumptions closed_scalar_proofs.
Print Assumptions regcol_ground.
Print Assumptions regcol_symbolic.
Print Assumptions evaluator_guards.
