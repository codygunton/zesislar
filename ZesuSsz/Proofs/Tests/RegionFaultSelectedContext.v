From Coq Require Import ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* The region arithmetic first runs on the facts its bound reaches, then on
   the whole context. The probe arithmetic below refuses a context that still
   holds a fact unrelated to the bound or a local definition, so a test that
   closes through it shows what the selected attempt kept. *)
Definition region_probe_unrelated (value : Z) : Prop := 0 <= value.

#[local] Ltac ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic_full ::=
  assert_fails (idtac; match goal with _ : region_probe_unrelated _ |- _ => idtac end);
  assert_fails (idtac; match goal with _ := _ |- _ => idtac end);
  lia.

(* Fires: the bound reaches its facts through a local definition; the
   unrelated fact and the unused definition are gone before the arithmetic. *)
Lemma region_selected_context_fires (base other : Z)
    (Hbase : 0 <= base <= 100)
    (Hother : region_probe_unrelated other) :
  let unused := other + 3 in
  let address := base + 8 in
  address + 8 <= 116.
Proof.
  intros unused address.
  Fail solve [ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic_full].
  ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic.
Qed.

(* Refused: the fact that closes the bound is three atoms away, past the
   selection's depth; the selected attempt fails and the whole context
   closes it. *)
Lemma region_selected_context_falls_back (a b c d : Z)
    (Hab : a = b) (Hbc : b = c) (Hcd : c = d) (Hd : d <= 10) :
  a <= 10.
Proof.
  Fail solve [ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic_selected].
  ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_arithmetic.
Qed.
