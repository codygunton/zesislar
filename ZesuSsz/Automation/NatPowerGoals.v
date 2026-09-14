Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.NatBounds.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.

Class ZesuBinaryNatBound (bound : nat) (integer : Z) : Prop :=
  zesu_binary_nat_bound : Z.of_nat bound = integer.

Ltac zesu_binary_nat_expression number :=
  lazymatch number with
  | Nat.mul ?left ?right =>
      let l := zesu_binary_nat_expression left in
      let r := zesu_binary_nat_expression right in constr:((l * r)%Z)
  | Nat.pow ?base ?exponent =>
      let b := zesu_binary_nat_expression base in
      constr:((b ^ Z.of_nat exponent)%Z)
  | O => constr:(0%Z)
  | S ?rest =>
      let r := zesu_binary_nat_expression rest in constr:((1 + r)%Z)
  end.

Global Hint Extern 0 (ZesuBinaryNatBound ?bound ?integer) =>
  (lazymatch bound with Nat.mul _ _ => idtac | Nat.pow _ _ => idtac end;
   let binary := zesu_binary_nat_expression bound in
   unify integer binary;
   change (Z.of_nat bound = binary);
   rewrite !Nat2Z.inj_mul ?Nat2Z.inj_pow; reflexivity) : typeclass_instances.

(* Normalize the bound before Lithium tries unary conversion. *)
Lemma simplify_large_nat_bound {Sigma : gFunctors} number bound integer (G : iProp Sigma)
    `{!ZesuBinaryNatBound bound integer} :
  (⌜Z.of_nat number < integer⌝ ∗ G) ⊢
  simplify_goal (⌜(number < bound)%nat⌝) G.
Proof.
  have Hbound : Z.of_nat bound = integer.
  { exact zesu_binary_nat_bound. }
  iIntros "[%Hnumber HG]". iSplit; last iExact "HG".
  iPureIntro. apply Nat2Z.inj_lt. rewrite Hbound. exact Hnumber.
Qed.
Print Assumptions simplify_large_nat_bound.
Definition simplify_large_nat_bound_inst := [instance @simplify_large_nat_bound with 0%N].
Global Existing Instance simplify_large_nat_bound_inst | 0.

Ltac zesu_run_nat_safe :=
  zesu_normalize_nat_powers; zesu_run.
