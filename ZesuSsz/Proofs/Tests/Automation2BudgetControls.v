From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
From stdpp.bitvector Require Import definitions tactics.
Require Import ZesuSsz.Automation2.MemoryAddress.
Require Import ZesuSsz.Automation2.SearchBudget.
From Ltac2 Require Import Ltac2 Ref.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.
Ltac use_two tick check := let _ := tick constr:(tt) in let _ := tick constr:(tt) in let _ := check constr:(tt) in idtac.
Ltac2 use_limit n :=
 let failed := Ref.ref false in
 Ltac1.apply (Ltac1.ref [@ZesuSsz; @Proofs; @Tests; @Automation2BudgetControls; @use_two])
 [ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed n;
 ZesuSsz.Automation2.SearchBudget.zesu_budget_checker failed] Ltac1.run.
Goal True.
Proof. ltac2:(use_limit 2). exact I. Qed.
Goal True.
Proof. Fail ltac2:(use_limit 1). exact I. Qed.
Goal True.
Proof.
 ltac2:(let failed := Ref.ref false in
 let run () := Ltac1.apply (Ltac1.ref [@ZesuSsz; @Proofs; @Tests; @Automation2BudgetControls; @use_two])
 [ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 2;
 ZesuSsz.Automation2.SearchBudget.zesu_budget_checker failed] Ltac1.run in
 run (); run (); ZesuSsz.Automation2.SearchBudget.zesu_budget_check failed).
 exact I.
Qed.
Goal (2048%nat = 2048%nat).
Proof. Fail ZesuSsz.Automation2.SearchBudget.zesu_check_atomic_input. reflexivity. Qed.
Lemma bounded_address : forall base : Z,
 0 <= base -> base + 16 < 2 ^ 64 ->
 bv_unsigned (bv_add (Z_to_bv 64%N base) (BV 64%N 8%Z)) = base + 8.
Proof.
 intros base Hlower Hupper.
 ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic.
Qed.
Print Assumptions bounded_address.

From Coq Require Import ZArith.ZArith Lia.
From Ltac2 Require Import Ltac2 Ref.
Require Import ZesuSsz.Automation2.MemoryAddress.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.
Definition paired (P Q:Prop) := P /\ Q.
Ltac2 split_limit limit :=
 let failed := Ref.ref false in
 Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_split_pure_steps])
 [ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed limit;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 32;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_checker failed] Ltac1.run.
Ltac2 normalize_limit hypothesis limit :=
 let failed := Ref.ref false in
 Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_normalize_hypothesis_steps])
 [hypothesis; ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 32768;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed limit] Ltac1.run;
 ZesuSsz.Automation2.SearchBudget.zesu_budget_check failed.
Module M.
Lemma split_accepts (P Q:Prop) (H:paired P Q) : True.
Proof. ltac2:(split_limit 32). exact I. Qed.
Lemma split_refuses_without_visits (P Q:Prop) (H:paired P Q) : True.
Proof. Fail ltac2:(split_limit 0). exact I. Qed.
Lemma closed_normalization (H:0 <= 1+2) : True.
Proof.
 ltac2:(normalize_limit (Ltac1.of_ident @H) 64).
 lazymatch type of H with 0 <= 3 => idtac end.
 exact I.
Qed.
Lemma normalization_refuses_without_rewrites (H:0 <= 1+2) : True.
Proof. Fail ltac2:(normalize_limit (Ltac1.of_ident @H) 0). exact I. Qed.
Lemma symbolic_normalization (x y:Z) (H:x<=x+y) : True.
Proof. ltac2:(normalize_limit (Ltac1.of_ident @H) 0). exact I. Qed.
End M.
Definition expected_split : forall P Q:Prop, paired P Q -> True := M.split_accepts.
Definition expected_refusal : forall P Q:Prop, paired P Q -> True := M.split_refuses_without_visits.
Definition expected_closed : 0<=1+2 -> True := M.closed_normalization.
Definition expected_no_rewrites : 0<=1+2 -> True := M.normalization_refuses_without_rewrites.
Definition expected_symbolic : forall x y:Z, x<=x+y -> True := M.symbolic_normalization.
Print Assumptions M.split_accepts.
Print Assumptions M.split_refuses_without_visits.
Print Assumptions M.closed_normalization.
Print Assumptions M.normalization_refuses_without_rewrites.
Print Assumptions M.symbolic_normalization.
