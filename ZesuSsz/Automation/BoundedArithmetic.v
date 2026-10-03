Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.NatBounds.
Require Import ZesuMachineMap.Machine.

Class ZesuStepBoundedArithmetic : Prop := zesu_step_bounded_arithmetic : True.

(* Configure the default in Hooks.v; explicit callers can supply a bound. *)
Ltac zesu_arithmetic_seconds := 5.

Ltac zesu_bounded_arithmetic_with seconds action := timeout seconds action.

Ltac zesu_bounded_arithmetic action :=
  tryif let _ := constr:(_ : ZesuStepBoundedArithmetic) in idtac
  then let seconds := zesu_arithmetic_seconds in
       zesu_bounded_arithmetic_with seconds action
  else action.

Ltac zesu_index_fact_relevant statement bytes index pointer base :=
  first
    [lazymatch statement with context[length bytes] => idtac end
    |lazymatch statement with context[index] => idtac end
    |lazymatch statement with context[bv_unsigned pointer] => idtac end
    |lazymatch statement with context[bv_signed pointer] => idtac end
    |lazymatch statement with context[base] => idtac end].

Ltac zesu_index_fact_arithmetic statement :=
  lazymatch statement with
  | @eq Z _ _ => idtac
  | @eq nat _ _ => idtac
  | @eq (bv _) _ _ => idtac
  | Z.le _ _ => idtac
  | Z.lt _ _ => idtac
  | le _ _ => idtac
  | lt _ _ => idtac
  | Nat.le _ _ => idtac
  | Nat.lt _ _ => idtac
  | _ /\ _ => idtac
  | _ -> _ => idtac
  end.

Ltac zesu_select_index_facts bytes index pointer base :=
  repeat match goal with
  | H : ?statement |- _ =>
      zesu_index_fact_arithmetic statement;
      assert_fails (zesu_index_fact_relevant statement bytes index pointer base);
      clear H
  end.

Lemma zesu_mod_sub_upper_bound_nonwrap (value : Z)
    (frame offset limit : Z)
    (Hvalue : (0 <= value)%Z)
    (Hframe : (0 <= frame <= bv_modulus 64)%Z)
    (Hlimit : (limit <= bv_modulus 64 - frame + offset)%Z)
    (Hbound : ((value - frame) mod bv_modulus 64 + offset < limit)%Z) :
  (frame <= value)%Z.
Proof.
  destruct (decide (frame <= value)%Z) as [Hgood|Hwrap]; [exact Hgood|].
  assert (Hmod : ((value - frame) mod bv_modulus 64 =
    value - frame + bv_modulus 64)%Z).
  { symmetry. apply Z.mod_unique with (q := -1); lia. }
  rewrite Hmod in Hbound. lia.
Qed.

Ltac zesu_stack_pointer_arithmetic :=
  let _ := constr:(_ : ZesuStepBoundedArithmetic) in
  multimatch goal with
  | Hbound : (bv_unsigned (?pointer - ?frame) + ?offset < ?limit)%Z |- ?statement =>
      lazymatch statement with context[pointer] => idtac end;
      let amount := eval vm_compute in (bv_unsigned frame) in
      repeat match goal with
      | H : ?fact |- _ =>
          zesu_index_fact_arithmetic fact;
          assert_fails (lazymatch fact with context[pointer] => idtac end);
          clear H
      end;
      bv_simplify_arith Hbound;
      unfold bv_wrap in Hbound;
      let Hnonwrap := fresh "HstackNonwrap" in
      assert (Hnonwrap : (amount <= bv_unsigned pointer)%Z) by
        (apply (zesu_mod_sub_upper_bound_nonwrap (bv_unsigned pointer) amount offset limit);
         [pose proof (bv_unsigned_in_range _ pointer); lia
         |unfold bv_modulus; vm_compute; done
         |unfold bv_modulus; vm_compute; done
         |exact Hbound]);
      solve [lia]
  end.

(* Prepare reverse-stack bounds inside the arithmetic subgoal. *)
Ltac zesu_prepare_stack_nonwrap :=
  multimatch goal with
  | Hbound : (bv_unsigned (?pointer - ?frame) + ?offset < ?limit)%Z |- ?statement =>
      lazymatch statement with context[pointer] => idtac end;
      let amount := eval vm_compute in (bv_unsigned frame) in
      let Hnonwrap := fresh "HstackNonwrap" in
      assert (Hnonwrap : (amount <= bv_unsigned pointer)%Z) by
        zesu_stack_pointer_arithmetic
  end.

(* Normalize pointer offsets with the array bound before general arithmetic. *)
Ltac zesu_byte_unscaled_pointer_arithmetic :=
  let _ := constr:(_ : ZesuStepBoundedArithmetic) in
  multimatch goal with
  | Hindex : (bv_unsigned ?pointer = ?base + Z.of_nat ?index)%Z |- _ =>
      is_var index;
      multimatch goal with
      | Hbound : context[length ?bytes] |- _ =>
          lazymatch type of bytes with list (bv 8) => idtac end;
          lazymatch type of Hbound with context[index] => idtac end;
          lazymatch goal with |- ?statement =>
            first [lazymatch statement with context[pointer] => idtac end
                  |lazymatch statement with context[base] => idtac end
                  |lazymatch statement with context[length bytes] => idtac end]
          end;
          zesu_select_index_facts bytes index pointer base;
          repeat match goal with
          | Hloaded : context[bytes !! _] |- _ => clear Hloaded
          | Hcursor : context[Z.to_nat _] |- _ => clear Hcursor
          end;
          zesu_normalize_binary_nat_hypotheses;
          rewrite ?Nat2Z.inj_add in Hbound;
          cbv [mapRamBase mapRamSize machineRamEnd defaultMap] in *;
          bv_simplify_arith;
          unfold bv_wrap, bv_modulus;
          simpl;
          rewrite ?bv_unsigned_BV;
          solve [repeat (rewrite Z.mod_small; [|lia]); lia]
      end
  end.

Ltac zesu_byte_scalar_pointer_arithmetic :=
  let _ := constr:(_ : ZesuStepBoundedArithmetic) in
  multimatch goal with
  | Hindex : (bv_unsigned ?pointer = ?base + ?stride * Z.of_nat ?index)%Z |- _ =>
      is_var index;
      multimatch goal with
      | Hbound : context[length ?bytes] |- _ =>
          lazymatch type of bytes with list (bv 8) => idtac end;
          lazymatch type of Hbound with context[index] => idtac end;
          lazymatch goal with |- ?statement =>
            first [lazymatch statement with context[pointer] => idtac end
                  |lazymatch statement with context[base] => idtac end
                  |lazymatch statement with context[length bytes] => idtac end]
          end;
          zesu_select_index_facts bytes index pointer base;
          repeat match goal with
          | Hloaded : context[bytes !! _] |- _ => clear Hloaded
          | Hcursor : context[Z.to_nat _] |- _ => clear Hcursor
          end;
          first [lazymatch type of Hbound with
                 | @eq nat _ _ => apply (f_equal Z.of_nat) in Hbound
                 end | idtac];
          zesu_normalize_binary_nat_hypotheses;
          rewrite ?Nat2Z.inj_add ?Nat2Z.inj_mul ?Nat2Z.inj_succ in Hbound;
          cbv [mapRamBase mapRamSize machineRamEnd defaultMap] in *;
          bv_simplify_arith;
          unfold bv_wrap, bv_modulus;
          simpl;
          rewrite ?bv_unsigned_BV;
          solve [repeat (rewrite Z.mod_small; [|lia]); lia]
      end
  end.

Ltac zesu_byte_pointer_arithmetic :=
  first [zesu_byte_unscaled_pointer_arithmetic
        |zesu_byte_scalar_pointer_arithmetic].

(* Keep the array bound, its index relation, and the pointer's non-wrap facts.
   A failed selection backtracks before the general arithmetic attempt. *)
Ltac zesu_byte_index_arithmetic :=
  let _ := constr:(_ : ZesuStepBoundedArithmetic) in
  first [zesu_byte_pointer_arithmetic
  | lazymatch goal with
  | |- context[length ?bytes] =>
      lazymatch type of bytes with list (bv 8) => idtac end;
      multimatch goal with
      | H : (bv_unsigned ?pointer = ?base + Z.of_nat ?index)%Z |- _ =>
          is_var index;
          zesu_select_index_facts bytes index pointer base;
          solve [rewrite ?length_take ?length_drop; lia]
      end
  end].

Ltac zesu_finish_lia :=
  first [zesu_bounded_arithmetic ltac:(zesu_stack_pointer_arithmetic)
        |zesu_bounded_arithmetic ltac:(zesu_byte_index_arithmetic)
        |zesu_bounded_arithmetic ltac:(lia)].

Ltac zesu_finish_witness_arithmetic :=
  tryif let _ := constr:(_ : ZesuStepBoundedArithmetic) in idtac
  then zesu_bounded_arithmetic ltac:(solve [zesu_witness_arith_if_enabled])
  else (timeout 5 (solve [zesu_witness_arith_if_enabled])).
