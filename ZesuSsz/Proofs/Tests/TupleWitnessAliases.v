Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Definition tuple_witness_integer_alias : Type := Z.
Definition tuple_witness_natural_alias : Type := nat.

Lemma tuple_witness_integer_alias_unresolved : True.
Proof.
  let T := constr:(li_prod tuple_witness_integer_alias unit) in
  let witness := ZesuSsz.Automation2.Hooks.zesu_primitive_tuple_witness T in
  lazymatch witness with li_pair ?value tt =>
    is_evar value;
    unify value (7%Z)
  end.
  exact I.
Qed.

Lemma tuple_witness_labelled_alias_unresolved : True.
Proof.
  let T := constr:(li_prod (lvar "index" Z) unit) in
  let witness := ZesuSsz.Automation2.Hooks.zesu_primitive_tuple_witness T in
  lazymatch witness with li_pair ?value tt =>
    is_evar value;
    unify value (9%Z)
  end.
  exact I.
Qed.

Lemma tuple_witness_nested_aliases_unresolved : True.
Proof.
  let T := constr:(li_prod (bv 64)
    (li_prod (lvar "index" tuple_witness_integer_alias)
      (li_prod tuple_witness_natural_alias unit))) in
  let witness := ZesuSsz.Automation2.Hooks.zesu_primitive_tuple_witness T in
  lazymatch witness with li_pair ?word (li_pair ?integer (li_pair ?natural tt)) =>
    is_evar word; is_evar integer; is_evar natural;
    unify word (Z_to_bv 64 3);
    unify integer (11%Z);
    unify natural (5%nat)
  end.
  exact I.
Qed.

Local Ltac tuple_witness_unsupported_probe :=
  let T := constr:(li_prod string unit) in
  let witness := ZesuSsz.Automation2.Hooks.zesu_primitive_tuple_witness T in idtac witness.

Lemma tuple_witness_unsupported_component_refuses : True.
Proof.
  Fail tuple_witness_unsupported_probe.
  exact I.
Qed.

Lemma tuple_witness_unused_scalars_remain_unresolved : True.
Proof.
  let T := constr:(li_prod (bv 64)
    (li_prod (lvar "index" tuple_witness_integer_alias)
      (li_prod tuple_witness_natural_alias unit))) in
  let witness := ZesuSsz.Automation2.Hooks.zesu_primitive_tuple_witness T in
  ZesuSsz.Automation2.MemoryTupleConsumer.zesu_memory_default_unused witness constr:(True);
  lazymatch witness with li_pair ?word (li_pair ?integer (li_pair ?natural tt)) =>
    constr_eq word constr:(Z_to_bv 64 0);
    is_evar integer; is_evar natural;
    unify integer (13%Z); unify natural (6%nat)
  end.
  exact I.
Qed.
