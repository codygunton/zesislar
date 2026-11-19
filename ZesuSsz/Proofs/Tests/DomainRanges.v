Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A folded domain whose range no solver opens. *)
Definition toyDomain (pointer : bv 64) : Prop :=
  4096 <= bv_unsigned pointer /\ bv_unsigned pointer + 64 <= 8192.
Definition toyOtherDomain (pointer : bv 64) : Prop :=
  4096 <= bv_unsigned pointer < 8192.

#[local] Instance toyDomainRanges (pointer : bv 64) :
  ZesuDomainRanges (toyDomain pointer)
    (4096 <= bv_unsigned pointer /\ bv_unsigned pointer + 64 <= 8192).
Proof. exact (fun domain => domain). Qed.

(* The Lithium introduction of a domain premise poses its ranges. *)
Lemma domain_ranges_at_intro (pointer : bv 64) (offset : Z) :
  toyDomain pointer -> 0 <= offset < 64 -> bv_unsigned pointer + offset < 8192.
Proof.
  liImpl. liImpl.
  match goal with _ : bv_unsigned pointer + 64 <= 8192 |- _ => idtac end.
  zesu_lia.
Qed.

(* The gate: a premise with registered ranges runs the scan, a premise
   without them is introduced as before. *)
Lemma domain_ranges_premise_guard (pointer : bv 64) :
  toyDomain pointer -> toyOtherDomain pointer -> bv_unsigned pointer < 8192.
Proof.
  zesu_domain_ranges_premise. liImpl.
  tryif zesu_domain_ranges_premise then fail else idtac. liImpl.
  lazymatch goal with _ : bv_unsigned pointer + 64 <= 8192 |- _ => idtac end.
  zesu_lia.
Qed.

(* Posing twice adds nothing: every conjunct is already a hypothesis. *)
Lemma domain_ranges_idempotent (pointer : bv 64) :
  toyDomain pointer -> bv_unsigned pointer < 8192.
Proof.
  intros domain. zesu_pose_domain_ranges. zesu_pose_domain_ranges.
  lazymatch goal with
  | H1 : 4096 <= bv_unsigned pointer, H2 : 4096 <= bv_unsigned pointer |- _ => fail
  | _ => idtac
  end.
  zesu_lia.
Qed.

(* A domain with no instance: the context stays as it was. *)
Lemma domain_ranges_no_instance (pointer : bv 64) :
  toyOtherDomain pointer -> bv_unsigned pointer < 8192.
Proof.
  intros domain. zesu_pose_domain_ranges.
  lazymatch goal with
  | _ : 4096 <= bv_unsigned pointer |- _ => fail
  | _ => idtac
  end.
  unfold toyOtherDomain in domain. destruct domain. zesu_lia.
Qed.

(* decodeParentHeader: the callee frame below the stack pointer, from the
   folded domain alone. *)
Lemma parent_header_frame_address (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args ->
  bv_unsigned (bv_add (parentHeaderStackPointer args) (BV 64 18446744073709551216)) =
    bv_unsigned (parentHeaderStackPointer args) - 400.
Proof. liImpl. bv_solve. Qed.

(* nextUint64: the result object lies below the RAM end. *)
Lemma next_uint64_result_end (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  nextResultPointer (nextUint64Base params) + 16 <= 3221225472.
Proof. liImpl. zesu_lia. Qed.

Print Assumptions parent_header_frame_address.
