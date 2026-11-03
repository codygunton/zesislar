Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteMaskCast.
Require Import ZesuSsz.Automation.VmClosed.
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

Ltac zesu_source_byte_views :=
  zesu_source_byte_distinct_views; zesu_source_byte_equal_views.
