Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Automation2.CallDeclarations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The predecessor's exit: the call block declares the slice with its bounds, the piece at the
   call's argument address and the restore wand. The step lends the piece from the owned whole
   array at the stated offset and length; what is left is the stated bounds with the address
   equation, and the rest of the goal. *)
Lemma call_declarations_lend `{!islaG Sigma} (base argument length : Z) (bytes : list (bv 8)) (R : iProp Sigma) :
  (0 <= argument - base)%Z -> (0 <= length)%Z -> (argument - base + length <= Z.of_nat (List.length bytes))%Z ->
  base ↦ₘ∗ bytes ∗ R ⊢
  ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes))%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗
   (((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R)).
Proof.
  iIntros (Hoff Hlen Hend) "[Hbytes HR]". iStartProof.
  zesu_lend_declared_call_input.
  lazymatch goal with
  | |- envs_entails _ (⌜_ /\ base + (argument - base) = argument⌝ ∗ (base ↦ₘ∗ bytes ∗ R))%I => idtac
  end.
  iSplit; [iPureIntro; lia|]. iFrame.
Qed.
Print Assumptions call_declarations_lend.

(* Inside Lithium's packed binders: the declaration mentions none of them. *)
Lemma call_declarations_lend_packed `{!islaG Sigma} (base argument length : Z) (bytes : list (bv 8)) (P : Z → iProp Sigma) :
  (0 <= argument - base)%Z -> (0 <= length)%Z -> (argument - base + length <= Z.of_nat (List.length bytes))%Z ->
  base ↦ₘ∗ bytes ∗ P 1 ⊢
  ∃ₗ x : Z *ₗ unit, ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes))%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗
   (((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) -∗ base ↦ₘ∗ bytes) ∗ P x.1ₗ)).
Proof.
  iIntros (Hoff Hlen Hend) "[Hbytes HP]". iStartProof.
  zesu_lend_declared_call_input.
  iSplit; [iPureIntro; lia|]. iFrame. iExists (1, tt)ₗ. iFrame.
Qed.
Print Assumptions call_declarations_lend_packed.

(* The step reads the declaration only: an array goal without the restore wand beside it is
   not a declared slice, and the step leaves it (the generic lemma still lends it by hand). *)
Lemma call_declarations_lend_needs_wand `{!islaG Sigma} (base argument length : Z) (bytes : list (bv 8)) :
  (0 <= argument - base)%Z -> (0 <= length)%Z -> (argument - base + length <= Z.of_nat (List.length bytes))%Z ->
  base ↦ₘ∗ bytes ⊢
  ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes))%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗ True).
Proof.
  iIntros (Hoff Hlen Hend) "Hbytes". iStartProof.
  tryif zesu_lend_declared_call_input then fail else idtac.
  iDestruct (zesu_byte_array_lend_declared base (argument - base) length bytes with "Hbytes")
    as "[Hpiece _]"; [done..|].
  replace (base + (argument - base)) with argument by lia.
  iSplit; [iPureIntro; lia|]. iFrame.
Qed.
Print Assumptions call_declarations_lend_needs_wand.

(* After the call: the whole array from the declared wand and the returned piece. *)
Lemma call_declarations_restore `{!islaG Sigma} (base argument : Z) (bytes piece : list (bv 8)) (R : iProp Sigma) :
  (argument ↦ₘ∗ piece -∗ base ↦ₘ∗ bytes) ∗ argument ↦ₘ∗ piece ∗ R ⊢ base ↦ₘ∗ bytes ∗ R.
Proof.
  iIntros "(Hrestore & Hpiece & HR)". iStartProof.
  zesu_restore_declared_call_input.
  iFrame.
Qed.
Print Assumptions call_declarations_restore.

(* The call's argument address reads as the declared region address. *)
Lemma call_declarations_address `{!islaG Sigma} (argument region : Z) (after : list (bv 8)) :
  zesu_call_address argument region ->
  region ↦ₘ∗ after ⊢ argument ↦ₘ∗ after.
Proof.
  iIntros (Hdeclared) "Hregion". iStartProof.
  zesu_rewrite_declared_call_address.
  iExact "Hregion".
Qed.
Print Assumptions call_declarations_address.

(* A named equation over packed binders is an ordinary equation: Lithium instantiates the binder. *)
Lemma call_declarations_named_packed `{!islaG Sigma} (value : Z) :
  ⊢@{iProp Sigma} ∃ₗ x : Z *ₗ unit, ⌜zesu_named_eq x.1ₗ value⌝ ∗ ⌜x.1ₗ = value⌝ ∗ True.
Proof.
  iStartProof.
  liSideCond.
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod _ _) (λ x, bi_sep (bi_pure (li_fst x = value)) _)) => idtac
  end.
  liSideCond.
  iSplit; [done|]. done.
Qed.
Print Assumptions call_declarations_named_packed.
