Require Import isla.riscv64.riscv64.

Class ZesuExitMeaning {Sigma} (source : iProp Sigma) (facts : Prop) : Prop :=
  zesu_exit_meaning : source ⊢ ⌜facts⌝.
#[global] Hint Mode ZesuExitMeaning + + - : typeclass_instances.

(* This marker retains the exact source, facts, and registered evidence. *)
Inductive ZesuExitMeaningApplied {Sigma} (source : iProp Sigma)
    (facts : Prop) (evidence : ZesuExitMeaning source facts) : Prop :=
  ZesuExitMeaningWasApplied.

Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ByteArrays.

Class ZesuStepReturnRoute : Prop := zesu_step_return_route : True.

Lemma zesu_return_mask_address (ret : bv 64) :
  bv_extract 0 1 ret = BV 1 0 ->
  bv_unsigned (bv_or (bv_and (bv_add ret (BV 64 0))
    (BV 64 18446744073709551614)) (BV 64 0)) = bv_unsigned ret.
Proof.
intros Hlow.
pose proof (normalize_instr_addr_riscv64_ret_tac ret _ Hlow eq_refl) as Hmasked.
rewrite !bv_wrap_bv_unsigned in Hmasked.
exact Hmasked.
Qed.

Lemma zesu_return_fault_bit (ret : bv 64) :
  (bv_unsigned ret mod 4 = 0)%Z ->
  bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add ret (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 0.
Proof.
intros Haligned.
assert (Hlow : bv_extract 0 1 ret = BV 1 0) by bv_solve.
assert (Hmasked : bv_or (bv_and (bv_add ret (BV 64 0))
    (BV 64 18446744073709551614)) (BV 64 0) = ret).
{ apply bv_eq.
  pose proof (normalize_instr_addr_riscv64_ret_tac ret _ Hlow eq_refl) as Hnormalized.
  rewrite !bv_wrap_bv_unsigned in Hnormalized.
  exact Hnormalized. }
rewrite Hmasked.
bv_simplify_arith.
change ((bv_unsigned ret / 2) mod 2 = 0)%Z.
assert (Hmultiple : (bv_unsigned ret = (bv_unsigned ret / 4 * 2) * 2)%Z)
  by (pose proof (Z.div_mod (bv_unsigned ret) 4 ltac:(lia)); lia).
rewrite Hmultiple Z.div_mul; last lia.
apply Z.mod_mul; lia.
Qed.

(* Existing decoder equations determine a saved register value. *)
Ltac zesu_return_decode_facts :=
  zesu_witness_facts;
  repeat match goal with
  | H : context [little_endian_to_bv 8
      (take 8 (drop (Z.to_nat ?offset) ?bytes))] |- _ =>
      progress (ring_simplify offset in H; cbn [Z.to_nat N.to_nat] in H)
  end.

(* The address comes from an existing alignment fact and a proved value equation. *)
Ltac zesu_return_with_address ra continuation :=
  assert_fails (has_evar ra);
  zesu_return_decode_facts;
  multimatch goal with
  | Haligned : (?address mod 4 = 0)%Z |- _ =>
      assert_fails (has_evar address);
      let Hrange := fresh "HreturnRange" in
      assert (Hrange : (0 <= address < bv_modulus 64)%Z)
        by first [apply bv_unsigned_in_range | assumption | lia];
      let Hvalue := fresh "HreturnValue" in
      assert (Hvalue : ra = Z_to_bv 64 address)
        by first [rewrite ?Z_to_bv_bv_unsigned; reflexivity | congruence];
      let HraAligned := fresh "HreturnAligned" in
      assert (HraAligned : (bv_unsigned ra mod 4 = 0)%Z)
        by (rewrite Hvalue Z_to_bv_unsigned (bv_wrap_small 64 address Hrange);
            exact Haligned);
      continuation address Hrange Hvalue HraAligned
  end.

Ltac zesu_return_route_normalize :=
  zesu_switch_enabled constr:(ZesuStepReturnRoute);
  unLET;
  lazymatch goal with
  | |- LiTactic (normalize_instr_addr (bv_unsigned
      (bv_or (bv_and (bv_add ?ra (BV 64 0))
        (BV 64 18446744073709551614)) (BV 64 0)))) =>
      zesu_return_with_address ra
        ltac:(fun address Hrange Hvalue Haligned =>
          let Hlow := fresh "HreturnLowBit" in
          assert (Hlow : bv_extract 0 1 ra = BV 1 0)
            by (clear -Haligned; bv_solve);
          eapply (normalize_instr_addr_hint _ address);
          apply normalize_instr_addr_riscv64_ret_tac; [exact Hlow |];
          rewrite Hvalue Z_to_bv_unsigned bv_wrap_bv_wrap; reflexivity)
  end.

Ltac zesu_return_route_reduced_normalize :=
  zesu_switch_enabled constr:(ZesuStepReturnRoute);
  lazymatch goal with
  | |- LiTactic (normalize_instr_addr (bv_unsigned
      (bv_or (bv_and ?ra (BV 64 18446744073709551614)) (BV 64 0)))) =>
      zesu_return_with_address ra
        ltac:(fun address Hrange Hvalue Haligned =>
          let Hlow := fresh "HreturnLowBit" in
          assert (Hlow : bv_extract 0 1 ra = BV 1 0)
            by (clear -Haligned; bv_solve);
          let Hmask := fresh "HreturnMask" in
          pose proof (zesu_return_mask_address ra Hlow) as Hmask;
          rewrite (bv_add_0_r ra (BV 64 0) eq_refl) in Hmask;
          eapply (normalize_instr_addr_hint _ address);
          rewrite Hmask Hvalue Z_to_bv_unsigned bv_wrap_bv_wrap; reflexivity)
  end.
#[export] Hint Extern 5 (LiTactic (normalize_instr_addr _)) =>
  zesu_switch_enabled constr:(ZesuStepReturnRoute); unLET;
  first [zesu_return_route_normalize | zesu_return_route_reduced_normalize]
  : typeclass_instances.

Ltac zesu_return_route_fault :=
  zesu_switch_enabled constr:(ZesuStepReturnRoute);
  unLET;
  lazymatch goal with
  | |- SimplAnd (bv_extract 0 1 (bv_shiftr
      (bv_or (bv_and (bv_add ?ra (BV 64 0))
        (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False =>
      zesu_return_with_address ra
        ltac:(fun address Hrange Hvalue Haligned =>
          unfold SimplAnd; split; [intros [] |];
          let Hfault := fresh "HreturnFault" in
          intro Hfault; rewrite (zesu_return_fault_bit ra Haligned) in Hfault;
          discriminate)
  end.

#[export] Hint Extern 5
  (SimplAnd (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add _ (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False) =>
  zesu_return_route_fault : typeclass_instances.

#[export] Hint Extern 5 (SimplImpl _ _) =>
  zesu_switch_enabled constr:(ZesuStepReturnRoute); unLET;
  lazymatch goal with
  | |- SimplImpl ?predicate ?simplified =>
      lazymatch predicate with
      | bv_extract 0 1 (bv_shiftr
          (bv_or (bv_and (bv_add _ (BV 64 0))
            (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1 =>
          unify simplified False;
          change (SimplAnd predicate False); zesu_return_route_fault
      end
  end : typeclass_instances.
