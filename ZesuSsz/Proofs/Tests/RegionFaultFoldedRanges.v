From Coq Require Import ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* Region-fault arithmetic over folded facts: the one-pass split, the
   removal of equal copies, and the single attempt per assertion. *)
Record region_args := { region_pointer : Z; region_length : Z }.

Definition region_ranges (args : region_args) : Prop :=
  0 <= region_pointer args /\ region_pointer args + region_length args <= 100.

Definition region_well_formed (args : region_args) : Prop :=
  region_ranges args /\ 0 <= region_length args.

#[local] Instance region_well_formed_ranges (args : region_args) :
  ZesuDomainRanges (region_well_formed args) (region_ranges args).
Proof. intros [Hranges _]. exact Hranges. Qed.

(* The one-pass split opens nested folded conjunctions and keeps a
   registered domain once, as the rescanning loop did. *)
Lemma region_split_folded_all (args : region_args)
    (Hwell : region_well_formed args) :
  region_pointer args <= 100.
Proof.
  ZesuSsz.Automation2.PureFacts.zesu_split_folded_all.
  match goal with _ : ZesuSsz.Automation2.PureFacts.zesu_kept_domain (region_well_formed args) |- _ => idtac end.
  match goal with _ : 0 <= region_pointer args |- _ => idtac end.
  match goal with _ : region_pointer args + region_length args <= 100 |- _ => idtac end.
  match goal with _ : 0 <= region_length args |- _ => idtac end.
  lia.
Qed.

(* Three equal copies of one disjunction split into two cases, not eight. *)
Definition region_either (args : region_args) : Prop :=
  (0 <= region_pointer args <= 10 \/ 20 <= region_pointer args <= 30) /\ True.

Lemma region_copies_split_once (args : region_args)
    (H1 : region_either args) (H2 : region_either args) (H3 : region_either args) :
  region_pointer args <= 30.
Proof.
  ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_prepare; [lia | lia].
Qed.

Set Default Proof Using "Type".

(* Refused under `∧ True`: liStep splits that form and the assertion alone is
   decided once. *)
Section conjunction_tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma region_fault_assert_after_split es ann (address : bv 64)
      (Hbound : 0xa0000000 <= bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 0xa0000000)))
      Mk_annot) Mk_annot)) ann :t: es) ∧ True.
  Proof.
    iStartProof.
    Fail ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled.
    iSplit; [ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled | done].
  Qed.
End conjunction_tests.
