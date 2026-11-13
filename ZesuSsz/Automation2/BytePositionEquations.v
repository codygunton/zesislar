From Coq Require Import ZArith.ZArith Lists.List NArith.NArith Lia.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

(* Specs state a value loaded from a byte list as byte positions of the list:
   `nth k L 0`, and for a load of c bytes at k the byte concatenation
   `bv_concat (8 * c) (... (bv_concat 16 (nth (k+c-1) L 0) (nth (k+c-2) L 0)) ...) (nth k L 0)`.
   The block state holds the same value as a window
   `Z_to_bv (8 * c) (little_endian_to_bv 8 (take c (drop k L)))`, or as a byte
   variable v with `L !! k = Some v`. When the list on the spec side is still a
   Lithium existential, the equation between the two forms stops Lithium:
   unification cannot see the list through the window or the variable. The
   step below rewrites the window into the concatenation and the variable into
   its position, after which unification sets the existential. The window
   identity holds for any list (nth defaults to 0 past the end), so the
   rewrite needs no length fact. *)

Lemma zesu_le_window_byte (k : nat) (bytes : list (bv 8)) :
  Z_to_bv 8 (little_endian_to_bv 8 (take 1 (drop k bytes))) = nth k bytes (BV 8 0).
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  revert bytes; induction k as [|k IH]; intros [|b bytes]; cbn; try done.
  - unfold little_endian_to_bv; cbn. rewrite Z.shiftl_0_l Z.lor_0_r.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  - apply IH.
Qed.

Lemma zesu_le_window_concat (n m : N) (count k : nat) (bytes : list (bv 8)) :
  n = (m + 8)%N ->
  Z_to_bv n (little_endian_to_bv 8 (take (S count) (drop k bytes))) =
  bv_concat n (Z_to_bv m (little_endian_to_bv 8 (take count (drop (S k) bytes))))
    (nth k bytes (BV 8 0)).
Proof.
  intros ->.
  assert (Hshape : forall (rest : list (bv 8)) (first : bv 8),
    Z_to_bv (m + 8) (little_endian_to_bv 8 (first :: rest)) =
    bv_concat (m + 8) (Z_to_bv m (little_endian_to_bv 8 rest)) first).
  { intros rest first. apply bv_eq.
    rewrite bv_concat_unsigned' !Z_to_bv_unsigned. unfold little_endian_to_bv; cbn [fmap list_fmap little_endian_to_Z].
    set (E := little_endian_to_Z (Z.of_N 8) (bv_unsigned <$> rest)).
    unfold bv_wrap, bv_modulus.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_N (m + 8))) as [Hlt|Hge].
    2: { rewrite !Z.mod_pow2_bits_high; [done|lia|lia]. }
    rewrite !Z.mod_pow2_bits_low; [|lia|lia].
    rewrite !Z.lor_spec orb_comm. f_equal.
    change (Z.of_N 8) with 8. rewrite !Z.shiftl_spec; [|lia|lia].
    destruct (Z.ltb_spec (i - 8) 0).
    { rewrite !Z.testbit_neg_r; [done|lia|lia]. }
    rewrite Z.mod_pow2_bits_low; [done|lia]. }
  assert (Hempty : Z_to_bv (m + 8) (little_endian_to_bv 8 (@nil (bv 8))) =
    bv_concat (m + 8) (Z_to_bv m (little_endian_to_bv 8 (take count (@nil (bv 8))))) (BV 8 0)).
  { rewrite take_nil. transitivity (Z_to_bv (m + 8) (little_endian_to_bv 8 [BV 8 0]));
      [reflexivity | apply Hshape]. }
  revert bytes; induction k as [|k IH]; intros [|b bytes].
  - exact Hempty.
  - cbn [drop take nth]. apply Hshape.
  - exact Hempty.
  - cbn [drop nth]. apply IH.
Qed.

(* The concatenation of the c bytes at k, most significant byte innermost. *)
Ltac zesu_le_window_bytes width count start bytes :=
  lazymatch count with
  | 1%nat => constr:(nth start bytes (BV 8 0))
  | S ?rest =>
      let inner_width := eval vm_compute in (width - 8)%N in
      let inner := zesu_le_window_bytes inner_width rest (S start) bytes in
      constr:(bv_concat width inner (nth start bytes (BV 8 0)))
  end.

Ltac zesu_le_window_prove :=
  repeat match goal with
  | |- context [Z_to_bv 8 (little_endian_to_bv 8 (take 1 (drop ?start ?bytes)))] =>
      rewrite (zesu_le_window_byte start bytes)
  | |- context [Z_to_bv ?width (little_endian_to_bv 8 (take (S ?rest) (drop ?start ?bytes)))] =>
      let inner_width := eval vm_compute in (width - 8)%N in
      rewrite (zesu_le_window_concat width inner_width rest start bytes eq_refl)
  end; reflexivity.

(* Rewrite one window whose width is 8 bits per byte, with a closed count of
   at least one and a closed start. *)
Ltac zesu_le_window_rewrite_one :=
  match goal with
  | |- context [Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?bytes)))] =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed start;
      let c := eval vm_compute in count in
      let k := eval vm_compute in start in
      let w := eval vm_compute in width in
      lazymatch eval vm_compute in
        (bool_decide (w = 8 * N.of_nat c)%N && bool_decide (1 <= c)%nat)%bool with
      | true => idtac end;
      let window := constr:(Z_to_bv width (little_endian_to_bv 8 (take count (drop start bytes)))) in
      let concat := zesu_le_window_bytes w c k bytes in
      let Hwindow := fresh "Hwindow" in
      assert (Hwindow : window = concat) by
        (change window with (Z_to_bv w (little_endian_to_bv 8 (take c (drop k bytes))));
         zesu_le_window_prove);
      rewrite Hwindow; clear Hwindow
  end.

(* A byte variable known from a lookup becomes its list position, when the
   left side reads the same position. The goal is `lhs = ?normalized`; the
   replacement is proved apart, so that the variable in the evar's instance
   stays untouched. *)
Ltac zesu_lookup_value_rewrite_one :=
  lazymatch goal with
  | |- ?lhs = _ =>
      match goal with
      | Hvalue : ?bytes !! ?index = Some ?value |- _ =>
          is_var value;
          lazymatch lhs with context [value] => idtac end;
          lazymatch lhs with context [@nth (bv 8) index _ _] => idtac end;
          lazymatch eval pattern value in lhs with
          | ?body _ =>
              let replaced := eval cbv beta in (body (nth index bytes (BV 8 0))) in
              let Hposition := fresh "Hposition" in
              assert (Hposition : lhs = replaced) by
                (rewrite (nth_lookup_Some bytes index (BV 8 0) value Hvalue); reflexivity);
              rewrite Hposition; clear Hposition
          end
      end
  end.

(* A local definition (a trace let) that the left side mentions is unfolded
   in the equation when it holds a window or sits in a window's start; the
   window rewrite and the index step then see the terms. *)
Ltac zesu_byte_position_unfold_let :=
  lazymatch goal with
  | |- ?lhs = _ =>
      match goal with
      | local := ?body |- _ =>
          lazymatch lhs with context [local] => idtac end;
          first [
            lazymatch body with context [little_endian_to_bv _ _] => idtac end
          | match lhs with
            | context [little_endian_to_bv _ (take _ (drop ?start _))] =>
                lazymatch start with context [local] => idtac end
            end ];
          unfold local
      end
  end.

(* The run-loop step: a pure equation at the head of a lazy existential that
   reads byte positions of a list. Lithium's side-condition step refused it
   (the step runs last). *)
Ltac zesu_byte_position_pure_step :=
  lazymatch goal with
  | |- environments.envs_entails _
         (@bi_exist _ (li_prod _ _) (fun x => bi_sep (bi_pure (@?P x)) _)) =>
      lazymatch P with context [@nth (bv 8) _ _ _] => idtac end;
      notypeclasses refine (tac_normalize_goal_and_liex _ _ _ _ _ _);
        [intros ?;
         progress (repeat first [zesu_byte_position_unfold_let
                                | zesu_le_window_rewrite_one
                                | zesu_lookup_value_rewrite_one]);
         reflexivity
        | cbv beta]
  end.
