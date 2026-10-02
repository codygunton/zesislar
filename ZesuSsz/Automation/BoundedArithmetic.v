Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.

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

(* Keep the array bound, its index relation, and the pointer's non-wrap facts.
   A failed selection backtracks before the general arithmetic attempt. *)
Ltac zesu_byte_index_arithmetic :=
  let _ := constr:(_ : ZesuStepBoundedArithmetic) in
  lazymatch goal with
  | |- context[length ?bytes] =>
      lazymatch type of bytes with list (bv 8) => idtac end;
      multimatch goal with
      | H : (bv_unsigned ?pointer = ?base + Z.of_nat ?index)%Z |- _ =>
          is_var index;
          zesu_select_index_facts bytes index pointer base;
          solve [rewrite ?length_take ?length_drop; lia]
      end
  end.

Ltac zesu_finish_lia :=
  first [zesu_bounded_arithmetic ltac:(zesu_byte_index_arithmetic)
        |zesu_bounded_arithmetic ltac:(lia)].

Ltac zesu_finish_witness_arithmetic :=
  tryif let _ := constr:(_ : ZesuStepBoundedArithmetic) in idtac
  then zesu_bounded_arithmetic ltac:(solve [zesu_witness_arith_if_enabled])
  else (timeout 5 (solve [zesu_witness_arith_if_enabled])).
