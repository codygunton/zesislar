Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.VmClosed.
From iris.proofmode Require Import tactics environments.
From Coq Require Import ZArith NArith Lia.
From stdpp Require Import bitvector.tactics.
Local Open Scope Z_scope.

Lemma zesu_masked_byte_distinct (width : N) (byte : bv 8) (value : Z)
    (Hwidth : (8 <= width)%N) :
  bv_and (bv_sign_extend width byte) (Z_to_bv width (2 ^ 8 - 1)) <>
    Z_to_bv width value ->
  bv_unsigned byte <> value.
Proof.
  rewrite (ByteMaskCast.zesu_sign_extended_byte_mask width byte Hwidth).
  intros Hdifferent Hequal. apply Hdifferent.
  rewrite Hequal. reflexivity.
Qed.

(* Compute only the closed width, mask, result, and comparison value. *)
Ltac zesu_source_byte_distinct :=
  lazymatch goal with
  | |- bv_unsigned ?byte <> ?value =>
      let T := type of byte in constr_eq T constr:(bv 8);
      assert_fails (has_evar byte);
      VmClosed.zesu_vm_closed value;
      multimatch goal with
      | Hsource : bv_and (bv_sign_extend ?width byte) ?mask <> ?result |- _ =>
          VmClosed.zesu_vm_closed width;
          VmClosed.zesu_vm_closed mask;
          VmClosed.zesu_vm_closed result;
          let Hwidth := fresh "HbyteViewWidth" in
          let Hmask := fresh "HbyteViewMask" in
          let Hresult := fresh "HbyteViewResult" in
          assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
          assert (Hmask : mask = Z_to_bv width (2 ^ 8 - 1)) by
            (apply bv_eq; vm_compute; reflexivity);
          assert (Hresult : result = Z_to_bv width value) by
            (apply bv_eq; vm_compute; reflexivity);
          apply (zesu_masked_byte_distinct width byte value Hwidth);
          rewrite <- Hmask; rewrite <- Hresult; exact Hsource
      end
  end.

(* Retain every raw guard. Add only a proved view of its closed comparison. *)
Ltac zesu_source_byte_distinct_views :=
  repeat multimatch goal with
  | Hsource : bv_and (bv_sign_extend ?width ?byte) ?mask <> ?result |- _ =>
      let T := type of byte in constr_eq T constr:(bv 8);
      VmClosed.zesu_vm_closed result;
      let value := eval vm_compute in (bv_unsigned result) in
      tryif match goal with _ : bv_unsigned byte <> value |- _ => idtac end
      then fail 0 "The source comparison already has its unsigned view."
      else
        let Hview := fresh "HsourceByteDifferent" in
        assert (Hview : bv_unsigned byte <> value) by zesu_source_byte_distinct
  end.

Lemma zesu_masked_byte_equal (width : N) (byte : bv 8) (result : bv width)
    (Hwidth : (8 <= width)%N) :
  bv_and (bv_sign_extend width byte) (Z_to_bv width (2 ^ 8 - 1)) = result ->
  bv_unsigned byte = bv_unsigned result.
Proof.
  intro Hsource.
  rewrite (ByteMaskCast.zesu_sign_extended_byte_mask width byte Hwidth) in Hsource.
  pose proof (f_equal (@bv_unsigned width) Hsource) as Hview.
  assert (Hfit : 0 <= bv_unsigned byte < bv_modulus width).
  { pose proof (bv_unsigned_in_range 8 byte) as HbyteRange.
    pose proof (bv_modulus_le_mono 8 width Hwidth) as HmodulusOrder.
    clear - HbyteRange HmodulusOrder. Lia.lia. }
  rewrite (Z_to_bv_small width (bv_unsigned byte) Hfit) in Hview.
  exact Hview.
Qed.

Ltac zesu_source_byte_equal :=
  lazymatch goal with
  | |- bv_unsigned ?byte = ?value =>
      let T := type of byte in constr_eq T constr:(bv 8);
      assert_fails (has_evar byte);
      VmClosed.zesu_vm_closed value;
      multimatch goal with
      | Hsource : bv_and (bv_sign_extend ?width byte) ?mask = ?result |- _ =>
          VmClosed.zesu_vm_closed width;
          VmClosed.zesu_vm_closed mask;
          VmClosed.zesu_vm_closed result;
          let Hwidth := fresh "HbyteViewWidth" in
          let Hmask := fresh "HbyteViewMask" in
          let Hresult := fresh "HbyteViewResult" in
          assert (Hwidth : (8 <= width)%N) by (vm_compute; congruence);
          assert (Hmask : mask = Z_to_bv width (2 ^ 8 - 1)) by
            (apply bv_eq; vm_compute; reflexivity);
          assert (Hresult : bv_unsigned result = value) by
            (vm_compute; reflexivity);
          transitivity (bv_unsigned result);
          [apply (zesu_masked_byte_equal width byte result Hwidth);
           rewrite <- Hmask; exact Hsource | exact Hresult]
      end
  end.

Ltac zesu_source_byte_equal_views :=
  repeat multimatch goal with
  | Hsource : bv_and (bv_sign_extend ?width ?byte) ?mask = ?result |- _ =>
      let T := type of byte in constr_eq T constr:(bv 8);
      VmClosed.zesu_vm_closed result;
      let value := eval vm_compute in (bv_unsigned result) in
      tryif (match goal with _ : bv_unsigned byte = value |- _ => idtac end;
             match goal with _ : value <= bv_unsigned byte |- _ => idtac end;
             match goal with _ : bv_unsigned byte <= value |- _ => idtac end)
      then fail 0 "The source equality already has its unsigned views."
      else
        let Hequal := fresh "HsourceByteEqual" in
        let Hlower := fresh "HsourceByteLower" in
        let Hupper := fresh "HsourceByteUpper" in
        assert (Hequal : bv_unsigned byte = value) by zesu_source_byte_equal;
        assert (Hlower : value <= bv_unsigned byte) by
          (rewrite Hequal; apply Z.le_refl);
        assert (Hupper : bv_unsigned byte <= value) by
          (rewrite Hequal; apply Z.le_refl)
  end.

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

(* Use proved bounds. Evaluate only their closed constants. *)
Ltac zesu_source_signed_order_goal :=
  let requested := match goal with |- ?requested => requested end in
  assert_fails (has_evar requested);
  let word := lazymatch requested with
    | context [bv_zero_extend 128 ?value] => constr:(value)
    | context [bv_unsigned ?value] => constr:(value)
    end in
    let T := type of word in constr_eq T constr:(bv 64);
    lazymatch word with
    | context [Z_to_bv 64 ?quantity] =>
      let finish := ltac:(fun Hzero Hrange Hsource =>
        clear - Hzero Hrange Hsource;
        repeat lazymatch goal with
        | |- context [bv_signed (bv_add (bv_zero_extend 128 ?value) ?offset)] =>
          VmClosed.zesu_vm_closed offset;
          let Hoffset := fresh "HsignedOrderOffset" in
          assert (Hoffset : bv_unsigned offset < 2 ^ 64) by
            (vm_compute; congruence);
          rewrite (BitvectorFacts.zesu_signed_zero_extend_add_64_128
            value offset Hoffset); clear Hoffset
        end;
        repeat rewrite BitvectorFacts.zesu_signed_zero_extend_64_128;
        bv_solve) in
      multimatch goal with
      | Hzero : ?minimum <= quantity, Hrange : ?endpoint < ?modulus |- _ =>
        VmClosed.zesu_vm_closed minimum;
        VmClosed.zesu_vm_closed modulus;
        let floor := eval vm_compute in minimum in
        let limit := eval vm_compute in modulus in
        change (floor <= quantity) in Hzero;
        change (endpoint < limit) in Hrange;
        first [constr_eq endpoint quantity |
          lazymatch endpoint with
          | quantity + ?extent =>
            VmClosed.zesu_vm_closed extent;
            let count := eval vm_compute in extent in
            change (quantity + count < limit) in Hrange
          end];
        first [
          multimatch goal with
          | Hsource : ?lower <= quantity |- _ =>
            VmClosed.zesu_vm_closed lower;
            let bound := eval vm_compute in lower in
            change (bound <= quantity) in Hsource;
            finish Hzero Hrange Hsource
          end
        | multimatch goal with
          | Hsource : ?ending <= ?upper |- _ =>
            VmClosed.zesu_vm_closed upper;
            let bound := eval vm_compute in upper in
            change (ending <= bound) in Hsource;
            first [constr_eq ending quantity |
              lazymatch ending with
              | quantity + ?span =>
                VmClosed.zesu_vm_closed span;
                let count := eval vm_compute in span in
                change (quantity + count <= bound) in Hsource
              end];
            finish Hzero Hrange Hsource
          end]
      end
    end.

(* This consumer evaluates only closed widths, masks, and signed bounds. *)
Ltac zesu_source_byte_order_goal :=
  first [zesu_source_signed_order_goal |
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
  end].

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

Ltac zesu_source_byte_views :=
  zesu_source_byte_distinct_views; zesu_source_byte_equal_views;
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      zesu_source_byte_order_tree requested
  | _ => idtac
  end.
