Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WrappedWord.
Require Import isla.riscv64.riscv64.
Local Open Scope Z_scope.

Lemma zesu_wrapped_boolean_bounds (base : Z) :
  16 <= base < bv_modulus 64 ->
  bool_decide (0 <= bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)) &&
  bool_decide (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8) < bv_modulus 64) = true.
Proof.
  intros [Hlower Hupper].
  apply andb_true_iff; split; apply bool_decide_eq_true_2;
    zesu_wrapped_word_range ltac:(cbv [bv_unsigned bv_modulus] in *; lia).
Qed.

Lemma zesu_wrapped_owned_lookup `{!islaG Sigma} `{!threadG} (base : Z) :
  16 <= base < bv_modulus 64 ->
  (base - 16) ↦ₘ? 16 -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)))
    (fun _ => True%I).
Proof.
  intros Hrange. iIntros "Hframe".
  zesu_wrapped_memory_lookup.
  liStep.
Qed.

Print Assumptions zesu_wrapped_boolean_bounds.
Print Assumptions zesu_wrapped_owned_lookup.

Definition wrapped_alias_limit425 : Z := 16.
Definition wrapped_alias_modulus425 : Z := bv_modulus 64.
Definition wrapped_symbolic_alias425 (value : Z) : Z := value + 1.
Definition wrapped_bool_alias425 : bool := true.

Lemma zesu_wrapped_alias_preservation425 (base : Z)
    (Hlower : wrapped_alias_limit425 <= base)
    (Hupper : base < wrapped_alias_modulus425) :
    16 <= base < bv_modulus 64.
Proof.
  zesu_reduce_closed_Z_aliases.
  lazymatch type of Hlower with
  | ?lower <= _ => constr_eq lower constr:(16%Z)
  end.
  lazymatch type of Hupper with
  | _ < ?upper => constr_eq upper constr:(bv_modulus 64)
  end.
  split; assumption.
Qed.

Lemma zesu_wrapped_symbolic_alias_refusal425 (base value : Z)
    (Hbound : wrapped_symbolic_alias425 value <= base) : True.
Proof.
  Fail progress zesu_reduce_closed_Z_aliases.
  exact I.
Qed.

Lemma zesu_wrapped_symbolic_width_refusal425 (width : N) (base : Z)
    (Hbound : base < bv_modulus width) : True.
Proof.
  Fail progress zesu_reduce_closed_Z_aliases.
  exact I.
Qed.

Lemma zesu_wrapped_noninteger_alias_refusal425
    (Hbound : wrapped_bool_alias425 = true) : True.
Proof.
  Fail progress zesu_reduce_closed_Z_aliases.
  exact I.
Qed.

Print Assumptions zesu_wrapped_alias_preservation425.
Print Assumptions zesu_wrapped_symbolic_alias_refusal425.
Print Assumptions zesu_wrapped_symbolic_width_refusal425.
Print Assumptions zesu_wrapped_noninteger_alias_refusal425.
