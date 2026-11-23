Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import stdpp.bitvector.definitions.
Import ListNotations.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Rules met by the array-list callers (keysToOwnedSlice), whose contract
   names its pointers as bit-vector fields of the arguments and states the
   lengths of its byte arrays in `Z`. *)

Record OwnedRecord := {
  ownedPointer : bv 64;
  ownedBefore : list (bv 8)
}.

Definition ownedDomain (r : OwnedRecord) : Prop :=
  2684354560 <= bv_unsigned (ownedPointer r) /\
  bv_unsigned (ownedPointer r) + 24 <= 3221225472 /\
  Z.of_nat (length (ownedBefore r)) = 24.

#[local] Instance ownedDomainRanges (r : OwnedRecord) :
  ZesuDomainRanges (ownedDomain r)
    (2684354560 <= bv_unsigned (ownedPointer r) /\
     bv_unsigned (ownedPointer r) + 24 <= 3221225472 /\
     Z.of_nat (length (ownedBefore r)) = 24).
Proof. exact (fun domain => domain). Qed.

(* A length stated in `Z` with a numeral also enters as its `nat` form. *)
Lemma owned_domain_nat_length (r : OwnedRecord) :
  ownedDomain r -> length (ownedBefore r) = 24%nat.
Proof.
  intros domain. zesu_pose_domain_ranges.
  lazymatch goal with H : length (ownedBefore r) = 24%nat |- _ => exact H end.
Qed.

(* A symbolic size gives no `nat` form. *)
Lemma owned_domain_symbolic_length (bytes : list (bv 8)) (count : Z) :
  Z.of_nat (length bytes) = count * 32 -> True.
Proof.
  intros Hlength.
  ZesuSsz.Automation2.DomainRanges.zesu_domain_ranges_split Hlength.
  lazymatch goal with
  | _ : length bytes = _ |- _ => fail
  | _ => exact I
  end.
Qed.

Section owned_record.
  Context `{!islaG Sigma} `{!threadG}.

  (* The second store into the record (`R + 8`) after the first rewrote its
     first word: the address normalizes to `bv_unsigned R + 8` although `R`
     is a field, not a variable, and the array holds it. *)
  Lemma owned_record_second_word (r : OwnedRecord)
      (w0 w1 w2 w3 w4 w5 w6 w7 : bv 8) :
    ownedDomain r ->
    bv_unsigned (ownedPointer r)
      ↦ₘ∗ (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 ::
           drop 8 (ownedBefore r)) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (ownedPointer r + BV 64 8)))
      (fun _ => True)%I.
  Proof.
    intros domain. zesu_pose_domain_ranges.
    iStartProof. iIntros "Hbytes".
    ZesuSsz.Automation2.Hooks.zesu_normalize_find_mem_address.
    lazymatch goal with
    | |- envs_entails _ (find_in_context
        (FindMemMapsTo (bv_unsigned (ownedPointer r) + 8)) _) => idtac
    end.
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* A field root with no array at it: the rule leaves the address as it is
     (the word rules read it). *)
  Goal forall (r : OwnedRecord) (cell : bv 64),
    ownedDomain r ->
    (bv_unsigned (ownedPointer r) + 8) ↦ₘ cell -∗
    find_in_context (FindMemMapsTo (bv_unsigned (ownedPointer r + BV 64 8)))
      (fun _ => True)%I.
  Proof.
    intros r cell domain. zesu_pose_domain_ranges.
    iStartProof. iIntros "Hcell".
    Fail ZesuSsz.Automation2.Hooks.zesu_normalize_symbolic_mem_address. Abort.

  (* A list's items of symbolic size and its unused tail answer one
     uninitialized request for the whole buffer (a `free` premise). *)
  Lemma items_and_tail_uninit (pointer count capacity : Z) (items : list (bv 8)) :
    Z.of_nat (length items) = count * 32 ->
    0 <= count -> count <= capacity -> capacity <= 2 ^ 24 ->
    1 <= pointer -> pointer < 2 ^ 64 -> pointer + capacity * 32 <= 3221225472 ->
    pointer ↦ₘ∗ items -∗
    (pointer + count * 32) ↦ₘ? ((capacity - count) * 32) -∗
    pointer ↦ₘ? (capacity * 32).
  Proof.
    intros. iStartProof. iIntros "Hitems Htail".
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* The same request spelled as the machine computes it. *)
  Lemma items_and_tail_uninit_machine (pointer count capacity : Z)
      (items : list (bv 8)) :
    Z.of_nat (length items) = count * 32 ->
    0 <= count -> count <= capacity -> capacity <= 2 ^ 24 ->
    1 <= pointer -> pointer < 2 ^ 64 -> pointer + capacity * 32 <= 3221225472 ->
    pointer ↦ₘ∗ items -∗
    (pointer + count * 32) ↦ₘ? ((capacity - count) * 32) -∗
    bv_unsigned (Z_to_bv 64 pointer) ↦ₘ?
      bv_unsigned (bv_shiftl (Z_to_bv 64 capacity) (BV 64 5)).
  Proof.
    intros. iStartProof. iIntros "Hitems Htail".
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* An opaque token with no Lithium relation, requested with its arguments
     as the machine spells them after a call. *)
  Definition ownedToken (pointer bytes align : Z) : iProp Sigma :=
    ((pointer + bytes) ↦ₘ? align)%I.
  #[local] Opaque ownedToken.

  Lemma owned_token_machine_arguments (pointer capacity : Z) :
    1 <= pointer -> pointer < 2 ^ 64 -> 0 <= capacity <= 2 ^ 24 ->
    ownedToken pointer (capacity * 32) 0 -∗
    ownedToken (bv_unsigned (Z_to_bv 64 pointer))
      (bv_unsigned (bv_shiftl (Z_to_bv 64 capacity) (BV 64 5)))
      (bv_unsigned (BV 64 0)) ∗ True.
  Proof.
    intros. iStartProof. iIntros "Htoken".
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* Arguments that differ in value: no rewrite. *)
  Lemma owned_token_other_arguments (pointer capacity : Z) :
    1 <= pointer -> pointer < 2 ^ 64 -> 0 <= capacity <= 2 ^ 24 ->
    ownedToken pointer (capacity * 32) 0 -∗
    ownedToken pointer (capacity * 32) 8 ∗ True.
  Proof.
    intros. iStartProof. iIntros "Htoken".
    Fail ZesuSsz.Automation2.Hooks.zesu_opaque_atom_arguments. Abort.
End owned_record.

(* The stated size is the class's answer; without it there is none. *)
Lemma byte_array_symbolic_known_length (items : list (bv 8)) (count : Z) :
  Z.of_nat (length items) = count * 32 -> True.
Proof.
  intros Hlength.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuByteArrayKnownLength
    items (count * 32)) in idtac.
  clear Hlength.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuByteArrayKnownLength
    items _) in idtac.
  exact I.
Qed.

(* Two stores into one array: the rest of the first image cut again. *)
Lemma nested_drop_image (before : list (bv 8)) (w : bv 8) :
  w :: drop (N.to_nat 8) (drop (N.to_nat 8) before) = w :: drop 16 before.
Proof. ZesuSsz.Automation2.Finish.zesu_finish_known_list_shape. Qed.

Print Assumptions owned_record_second_word.
Print Assumptions items_and_tail_uninit.
Print Assumptions items_and_tail_uninit_machine.
Print Assumptions nested_drop_image.
