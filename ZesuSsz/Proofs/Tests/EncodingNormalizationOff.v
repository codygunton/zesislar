Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EncodingNormalization.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Lemma encoding_switch_default_off (left right : bv 64)
    (Hcompare : bv_signed (bv_zero_extend 128 left) <
                bv_signed (bv_zero_extend 128 right)) :
    bv_unsigned left < bv_unsigned right.
Proof.
  assert_fails (idtac; zesu_encoding_normalization_if_enabled).
  rewrite !zesu_bv_signed_zero_extend_wide in Hcompare; [exact Hcompare | lia..].
Qed.

Module KeyedOff.
Section Controls.
Context {Sigma : gFunctors}.
Definition source (fact : Prop) : iProp Sigma := ⌜fact⌝%I.
Local Typeclasses Opaque source.
#[local] Instance registered fact : ZesuEntryIntro (source fact) fact.
Proof. unfold ZesuEntryIntro, source. iIntros "%H". done. Qed.
Lemma encoding_keyed_off (P Q predicate : Prop) `{Decision predicate}
    (value : bool -> Z) (HP : P)
    (Hfacts : (P -> value (bool_decide predicate) = if bool_decide predicate then 1 else 0) /\
              (Q -> value (bool_decide predicate) = if bool_decide predicate then 2 else 0)) :
    value (bool_decide predicate) = value (bool_decide predicate).
Proof using Sigma.
  let facts := type of Hfacts in
  pose proof (@ZesuEntryIntroWasApplied Sigma (source facts) facts (registered facts)) as Happlied.
  Fail zesu_encoding_normalization_if_enabled.
  assert_fails (idtac; match goal with _ : ZesuEncodingConditionalUsed _ _ _ _ |- _ => idtac end).
  reflexivity.
Qed.
End Controls.
End KeyedOff.
