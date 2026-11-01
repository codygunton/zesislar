Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.Switches.RegionFault.
Require Import ZesuSsz.Automation.Switches.RegionFaultNormalization.
Open Scope Z_scope.

Lemma region_normalization_alias (value : Z) : value + 2 ^ 3 = value + 8.
Proof.
  pose (constant := 2 ^ 3).
  change (value + constant = value + 8).
  zesu_region_reduce_closed constant.
  reflexivity.
Qed.

Lemma region_normalization_symbolic (value : Z) : value = value.
Proof.
  Fail zesu_region_reduce_closed value.
  reflexivity.
Qed.

Lemma region_normalization_evar : True.
Proof.
  evar (value : Z).
  Fail zesu_region_reduce_closed value.
  let body := eval unfold value in value in is_evar body.
  instantiate (value := 0%Z).
  exact I.
Qed.

Lemma region_normalization_unchanged : True.
Proof.
  Fail zesu_region_reduce_closed constr:(0%Z).
  Fail zesu_region_reduce_closed constr:(1%Z).
  Fail zesu_region_reduce_closed constr:((-1)%Z).
  exact I.
Qed.

Lemma region_normalization_changed : (3 + 4 = 7)%Z.
Proof.
  zesu_region_reduce_closed constr:((3 + 4)%Z).
  reflexivity.
Qed.

Lemma region_normalization_rollback : (3 + 4 = 7)%Z.
Proof.
  first [zesu_region_reduce_closed constr:((3 + 4)%Z); fail 0 | idtac].
  match goal with |- ?statement =>
    constr_eq statement constr:((3 + 4 = 7)%Z)
  end.
  reflexivity.
Qed.

Lemma region_normalization_literal_constructors : True.
Proof.
 zesu_region_integer_literal constr:(0%Z).
 zesu_region_integer_literal constr:(1%Z).
 zesu_region_integer_literal constr:((-1)%Z).
 zesu_region_integer_literal constr:(2684354560%Z).
 Fail zesu_region_integer_literal constr:((3 + 4)%Z).
 pose (alias := 0%Z). Fail zesu_region_integer_literal alias.
 evar (unknown : Z). Fail zesu_region_integer_literal unknown.
 let body := eval unfold unknown in unknown in
 tryif zesu_region_integer_literal body then fail 1 "unexpected evar literal" else is_evar body.
 instantiate (unknown := 0%Z). exact I.
Qed.
Lemma region_normalization_literal_symbolic : forall p : positive, True.
Proof. intros p. Fail zesu_region_integer_literal constr:(Zpos p). exact I. Qed.
Lemma region_normalization_literal_nested_alias : True.
Proof.
 pose (part := xH).
 Fail zesu_region_integer_literal constr:(Zpos (xO part)).
 Fail zesu_region_integer_literal constr:(Zpos (Pos.add xH xH)).
 exact I.
Qed.

Set Default Proof Using "Type".

Section assertion_tests.
  Context `{!islaG Sigma} `{!threadG}.
  Lemma region_normalization_lower es ann (address : bv 64) (minimum : Z)
      (Hbound : minimum <= bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= minimum)))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_region_fault_if_enabled. Qed.
  Lemma region_normalization_upper es ann (address : bv 64) (maximum : Z)
      (Hbound : bv_unsigned address <= maximum) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) <= maximum)))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_region_fault_if_enabled. Qed.
End assertion_tests.

Print Assumptions region_normalization_alias.
Print Assumptions region_normalization_lower.
Print Assumptions region_normalization_upper.
