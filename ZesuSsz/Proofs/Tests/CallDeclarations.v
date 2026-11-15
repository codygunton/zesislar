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
  ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes) /\
    Z.of_nat (List.length (take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes))) = length)%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗
   (((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R)).
Proof.
  iIntros (Hoff Hlen Hend) "[Hbytes HR]". iStartProof.
  zesu_lend_declared_call_input ltac:(fail).
  lazymatch goal with
  | |- envs_entails _ (⌜_ /\ base + (argument - base) = argument⌝ ∗ (base ↦ₘ∗ bytes ∗ R))%I => idtac
  end.
  iSplit; [iPureIntro; lia|]. iFrame.
Qed.
Print Assumptions call_declarations_lend.

(* Inside Lithium's packed binders: the declaration mentions none of them. The given solver
   closes the bounds premise. *)
Lemma call_declarations_lend_packed `{!islaG Sigma} (base argument length : Z) (bytes : list (bv 8)) (P : Z → iProp Sigma) :
  (0 <= argument - base)%Z -> (0 <= length)%Z -> (argument - base + length <= Z.of_nat (List.length bytes))%Z ->
  base ↦ₘ∗ bytes ∗ P 1 ⊢
  ∃ₗ x : Z *ₗ unit, ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes) /\
    Z.of_nat (List.length (take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes))) = length)%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗
   (((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) -∗ base ↦ₘ∗ bytes) ∗ P x.1ₗ)).
Proof.
  iIntros (Hoff Hlen Hend) "[Hbytes HP]". iStartProof.
  zesu_lend_declared_call_input ltac:(lia).
  iFrame. iExists (1, tt)ₗ. iFrame.
Qed.
Print Assumptions call_declarations_lend_packed.

(* The step reads the declaration only: an array goal without the restore wand beside it is
   not a declared slice, and the step leaves it (the generic lemma still lends it by hand). *)
Lemma call_declarations_lend_needs_wand `{!islaG Sigma} (base argument length : Z) (bytes : list (bv 8)) :
  (0 <= argument - base)%Z -> (0 <= length)%Z -> (argument - base + length <= Z.of_nat (List.length bytes))%Z ->
  base ↦ₘ∗ bytes ⊢
  ⌜(0 <= argument - base /\ 0 <= length /\ argument - base + length <= Z.of_nat (List.length bytes) /\
    Z.of_nat (List.length (take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes))) = length)%Z⌝ ∗
  ((argument ↦ₘ∗ take (Z.to_nat length) (drop (Z.to_nat (argument - base)) bytes)) ∗ True).
Proof.
  iIntros (Hoff Hlen Hend) "Hbytes". iStartProof.
  tryif zesu_lend_declared_call_input ltac:(lia) then fail else idtac.
  iDestruct (zesu_byte_array_lend_declared base (argument - base) length bytes with "Hbytes")
    as "[Hpiece _]"; [done..|].
  replace (base + (argument - base)) with argument by lia.
  iSplit; [iPureIntro; rewrite length_take length_drop; lia|]. iFrame.
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

(* The same when the goal's remaining binders are still open (a successor entry under ∃ₗ). *)
Lemma call_declarations_restore_packed `{!islaG Sigma} (base argument : Z) (bytes piece : list (bv 8)) (P : Z → iProp Sigma) :
  (argument ↦ₘ∗ piece -∗ base ↦ₘ∗ bytes) ∗ argument ↦ₘ∗ piece ∗ P 1 ⊢
  ∃ₗ x : Z *ₗ unit, base ↦ₘ∗ bytes ∗ P x.1ₗ.
Proof.
  iIntros "(Hrestore & Hpiece & HP)". iStartProof.
  zesu_restore_declared_call_input.
  iExists (1, tt)ₗ. iFrame.
Qed.
Print Assumptions call_declarations_restore_packed.

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

(* The callee claims its frame at the caller's stack register: inside an owned frame region the
   claim's address takes the region's normal form, in the whole goal (the claim and the frame
   the callee returns). *)
Lemma call_declarations_frame_claim `{!islaG Sigma} (sp : bv 64) :
  (512 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp - 400 - 16) ↦ₘ? 16 ⊢
  (bv_unsigned (bv_add sp (BV 64 18446744073709551216)) - 16) ↦ₘ? 16 ∗
  ((bv_unsigned (bv_add sp (BV 64 18446744073709551216)) - 16) ↦ₘ? 16 -∗ True).
Proof.
  iIntros (Hsp) "Hframe". iStartProof.
  zesu_frame_claim_address.
  lazymatch goal with
  | |- envs_entails _ (((bv_unsigned sp - 400 - 16) ↦ₘ? 16) ∗
                       ((bv_unsigned sp - 400 - 16) ↦ₘ? 16 -∗ True))%I => idtac
  end.
  iFrame "Hframe". by iIntros "_".
Qed.
Print Assumptions call_declarations_frame_claim.

(* Without an owned region that holds the claim, the address stays as the callee states it. *)
Lemma call_declarations_frame_claim_needs_owner `{!islaG Sigma} (sp : bv 64) (Q : iProp Sigma) :
  (512 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp - 400 - 112) ↦ₘ? 96 ∗ Q ∗
  (Q -∗ (bv_unsigned (bv_add sp (BV 64 18446744073709551216)) - 16) ↦ₘ? 16) ⊢
  (bv_unsigned (bv_add sp (BV 64 18446744073709551216)) - 16) ↦ₘ? 16 ∗ True.
Proof.
  iIntros (Hsp) "(Hframe & HQ & Hclaim)". iStartProof.
  tryif zesu_frame_claim_address then fail else idtac.
  iDestruct ("Hclaim" with "HQ") as "$".
Qed.
Print Assumptions call_declarations_frame_claim_needs_owner.
