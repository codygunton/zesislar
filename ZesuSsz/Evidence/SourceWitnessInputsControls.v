Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import lithium.lvar.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
From Coq Require Import Strings.String.
Local Open Scope string_scope.

Lemma source_value_keys (left_value right_value : bv 64)
    (index : lvar "owned-index" Z) : True.
Proof.
  pose proof (@ZesuSourceWitnessHere (bv 64) "source.left" left_value) as Hleft.
  pose proof (@ZesuSourceWitnessHere (bv 64) "source.right" right_value) as Hright.
  pose proof (@ZesuSourceWitnessHere (lvar "owned-index" Z) "source.index" index) as Hindex.
  SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("source.left")
    ltac:(fun value => constr_eq value left_value).
  SourceWitnessInputs.zesu_read_source_value constr:(lvar "owned-index" Z) constr:("source.index")
    ltac:(fun value => constr_eq value index).
  Fail SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("source.left")
    ltac:(fun value => constr_eq value right_value).
  Fail SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("source.missing")
    ltac:(fun value => idtac).
  Fail SourceWitnessInputs.zesu_read_source_value constr:(bv 8) constr:("source.left")
    ltac:(fun value => idtac).
  exact I.
Qed.
Print Assumptions source_value_keys.

Lemma source_value_ambiguity (left_value right_value : bv 64) : True.
Proof.
  pose proof (@ZesuSourceWitnessHere (bv 64) "source.same" left_value) as Hleft.
  pose proof (@ZesuSourceWitnessHere (bv 64) "source.same" right_value) as Hright.
  Fail SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("source.same")
    ltac:(fun value => idtac).
  exact I.
Qed.
Print Assumptions source_value_ambiguity.

Section OwnedSource.
Context `{!islaG Sigma} `{!threadG}.
Definition source_owned_values (K : iProp Sigma) : iProp Sigma :=
  (∃ (left_value right_value : bv 64) (index : lvar "owned-index" Z),
    "x11" ↦ᵣ RVal_Bits left_value ∗
    "x12" ↦ᵣ RVal_Bits right_value ∗ ⌜(0 ≤ index)%Z⌝ ∗ K)%I.

#[local] Instance source_owned_values_origin (K : iProp Sigma) :
  ZesuSourceOwner (source_owned_values K)
    (ZesuSourceOwnerSlot (bv 64) (Some "owner.left")
      (ZesuSourceOwnerSlot (bv 64) (Some "owner.right")
        (ZesuSourceOwnerSlot (lvar "owned-index" Z) (Some "owner.index")
          ZesuSourceOwnerEnd))) :=
  {| zesu_source_owner_original := source_owned_values K;
     zesu_source_owner_original_eq := eq_refl |}.

Lemma source_owner_preserved (K : iProp Sigma) :
  source_owned_values K -∗ source_owned_values K.
Proof.
  iIntros "Hsource".
  SourceWitnessInputs.zesu_capture_source_owner.
  SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("owner.left")
    ltac:(fun left_value =>
      SourceWitnessInputs.zesu_read_source_value constr:(bv 64) constr:("owner.right")
        ltac:(fun right_value =>
          SourceWitnessInputs.zesu_read_source_value constr:(lvar "owned-index" Z) constr:("owner.index")
            ltac:(fun index => iExists left_value, right_value, index))).
  iExact "Hsource".
Qed.
Print Assumptions source_owner_preserved.

Lemma source_register_reader_preserved (K : iProp Sigma) :
  source_owned_values K -∗ source_owned_values K.
Proof.
  iIntros "Hsource".
  SourceWitnessInputs.zesu_capture_source_owner.
  iDestruct "Hsource" as "[Hleft [Hright [Hbounds HK]]]".
  SourceWitnessInputs.zesu_read_source_input
    constr:(ZesuSourcePair (ZesuSourceRegister 64 "x11")
      (ZesuSourcePair (ZesuSourceValue (bv 64) "owner.right")
        (ZesuSourcePair (ZesuSourceValue (lvar "owned-index" Z) "owner.index")
          ZesuSourceUnit)))
    ltac:(fun values =>
      let left_value := eval cbv beta iota delta [fst snd] in (fst values) in
      let right_value := eval cbv beta iota delta [fst snd] in (fst (snd values)) in
      let index := eval cbv beta iota delta [fst snd] in (fst (snd (snd values))) in
      iExists left_value, right_value, index).
  iFrame.
Qed.
Print Assumptions source_register_reader_preserved.
End OwnedSource.
