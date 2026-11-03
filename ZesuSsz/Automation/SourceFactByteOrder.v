Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.VmClosed.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith NArith Lia.
From stdpp Require Import bitvector.definitions.
Local Open Scope Z_scope.

Lemma zesu_masked_byte_signed_order_view (width wide : N) (byte : bv 8)
    (Hwidth : (8 <= width)%N) (Hwide : (9 <= wide)%N) :
  bv_signed (bv_zero_extend wide
    (bv_and (bv_sign_extend width byte) (Z_to_bv width (2 ^ 8 - 1)))) =
  bv_unsigned byte.
Proof.
  pose proof (bv_unsigned_in_range 8 byte) as Hbyte.
  change (0 <= bv_unsigned byte < 256) in Hbyte.
  pose proof (bv_modulus_le_mono 8 width Hwidth) as Hmodulus.
  change (256 <= bv_modulus width) in Hmodulus.
  pose proof (bv_half_modulus_le_mono 9 wide Hwide) as Hhalf.
  change (256 <= bv_half_modulus wide) in Hhalf.
  rewrite (ByteMaskCast.zesu_sign_extended_byte_mask width byte Hwidth).
  rewrite bv_zero_extend_signed.
  rewrite (Z_to_bv_small width (bv_unsigned byte) ltac:(lia)).
  apply bv_swrap_small. lia.
Qed.

(* This consumer evaluates only closed widths, masks, and signed bounds. *)
Ltac zesu_source_byte_order_goal :=
  let requested := match goal with |- ?requested => requested end in
  assert_fails (has_evar requested);
  lazymatch requested with
  | context [bv_unsigned ?byte] =>
      let T := type of byte in constr_eq T constr:(bv 8);
      multimatch goal with
      | Hsource : context [bv_signed (bv_zero_extend ?wide
          (bv_and (bv_sign_extend ?width byte) ?mask))] |- _ =>
          VmClosed.zesu_vm_closed width;
          VmClosed.zesu_vm_closed wide;
          VmClosed.zesu_vm_closed mask;
          let Hwidth := fresh "HbyteOrderWidth" in
          let Hwide := fresh "HbyteOrderWide" in
          let Hmask := fresh "HbyteOrderMask" in
          assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
          assert (Hwide : (9 <= wide)%N) by (vm_compute; congruence);
          assert (Hmask : mask = Z_to_bv width (2 ^ 8 - 1)) by
            (apply bv_eq; vm_compute; reflexivity);
          let Hview := fresh "HbyteOrderView" in
          pose proof (zesu_masked_byte_signed_order_view
            width wide byte Hwidth Hwide) as Hview;
          rewrite <- Hmask in Hview;
          let Hderived := fresh "HbyteOrderSource" in
          pose proof Hsource as Hderived;
          rewrite Hview in Hderived;
          repeat lazymatch type of Hderived with
          | context [bv_signed ?bound] =>
              VmClosed.zesu_vm_closed bound;
              let value := eval vm_compute in (bv_signed bound) in
              change (bv_signed bound) with value in Hderived
          end;
          solve [clear - Hderived; lia]
      end
  end.

Ltac zesu_source_byte_order_fact requested :=
  lazymatch requested with
  | bool_decide ?fact = true => zesu_source_byte_order_fact fact
  | bool_decide ?fact = false => zesu_source_byte_order_fact (~ fact)
  | negb (bool_decide ?fact) = true => zesu_source_byte_order_fact (~ fact)
  | negb (bool_decide ?fact) = false => zesu_source_byte_order_fact fact
  | ?left /\ ?right =>
      zesu_source_byte_order_fact left; zesu_source_byte_order_fact right
  | _ =>
      tryif has_evar requested then idtac else
        let Hderived := fresh "HsourceByteOrder" in
        tryif (assert (Hderived : requested) by zesu_source_byte_order_goal)
        then idtac else idtac
  end.

Ltac zesu_source_byte_order_tree requested :=
  lazymatch requested with
  | @bi_pure _ ?fact => zesu_source_byte_order_fact fact
  | @bi_sep _ ?left ?right =>
      zesu_source_byte_order_tree left; zesu_source_byte_order_tree right
  | _ => idtac
  end.
