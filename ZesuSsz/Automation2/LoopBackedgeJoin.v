(* The back edge of a cursor loop re-establishes one class of the loop
   entry. The step chooses the class, the loop index hook supplies the next
   index, and Lithium frames the resources. The pure obligations are retained
   conjuncts, cursor arithmetic, and the byte-window fold step. The rules name
   no address, register, or contract predicate. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.RegisterArrayCursor.
Require Import ZesuSsz.Automation2.LoopIndex.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Automation2.ByteWindowFoldWord.
Require Import ZesuSsz.Automation2.VmClosed.
From iris.proofmode Require Import environments tactics.
From stdpp Require Import bitvector.definitions list.
From Coq Require Import ZArith.ZArith Lia Lists.List.
Local Open Scope Z_scope.

Lemma zesu_loop_lookup_nth_error {A} (values : list A) (index : nat) :
  values !! index = nth_error values index.
Proof. revert index. induction values as [|value values IH]; intros [|index]; simpl; auto. Qed.

(* Choose the first registered class whose body binds the loop index. The
   back edge must step a cursor that a retained conjunct ties to the index. *)
Ltac zesu_loop_class_leaf leaf continuation :=
  let head := get_head leaf in
  let _ := constr:(_ : LithiumUnfold head) in
  let body := eval unfold head in leaf in
  lazymatch body with context [lvar "zesuLoopIndex" Z] => continuation head end.

Ltac zesu_loop_backedge_choice :=
  lazymatch goal with
  | |- envs_entails _ ?target =>
      let leaf := lazymatch target with
        | @bi_sep _ (@bi_or _ ?leaf _) _ => leaf
        | @bi_or _ ?leaf _ => leaf
        end in
      zesu_loop_class_leaf leaf ltac:(fun head =>
        zesu_loop_cursor_guard ltac:(fun _ => idtac);
        lazymatch target with
        | @bi_sep _ _ _ => rewrite bi.sep_or_r
        | _ => idtac
        end;
        iLeft;
        unfold head)
  end.

(* The goal is a retained conjunct of a hypothesis, or the proposition that
   a retained boolean guard decides. *)
Ltac zesu_loop_conjunct_find target proof statement :=
  lazymatch statement with
  | ?left /\ ?right =>
      first [zesu_loop_conjunct_find target constr:(@proj1 left right proof) left |
             zesu_loop_conjunct_find target constr:(@proj2 left right proof) right]
  | bool_decide ?inner = true =>
      first [constr_eq statement target; exact proof |
             constr_eq inner target; exact (bool_decide_eq_true_1 _ proof)]
  | negb (bool_decide ?inner) = true =>
      first [constr_eq statement target; exact proof |
             lazymatch target with
             | ~ ?negated => constr_eq inner negated;
                 exact (bool_decide_eq_false_1 _ (proj1 (negb_true_iff _) proof))
             end]
  | _ => constr_eq statement target; exact proof
  end.

Ltac zesu_loop_conjunct_close :=
  lazymatch goal with
  | |- ?target =>
      lazymatch type of target with Prop => idtac end;
      match goal with
      | H : ?statement |- _ =>
          lazymatch statement with _ /\ _ => idtac end;
          zesu_loop_conjunct_find target H statement
      end
  end.

(* Find the retained fold of the old accumulator. *)
Ltac zesu_loop_fold_conjunct accumulator bytes start proof statement continuation :=
  lazymatch statement with
  | ?left /\ ?right =>
      first [zesu_loop_fold_conjunct accumulator bytes start
               constr:(@proj1 left right proof) left continuation |
             zesu_loop_fold_conjunct accumulator bytes start
               constr:(@proj2 left right proof) right continuation]
  | bv_unsigned accumulator = ByteWindowFold.zesu_byte_window_fold bytes start (Z.to_nat ?count) =>
      continuation proof count
  end.

(* One shift-or step appends the loaded byte to the big-endian window. *)
Ltac zesu_loop_fold_step :=
  lazymatch goal with
  | |- bv_unsigned (bv_or (bv_shiftl ?accumulator ?shift) (bv_zero_extend 64 ?next)) =
       ByteWindowFold.zesu_byte_window_fold ?bytes ?start (Z.to_nat ?count') =>
      let distance := eval vm_compute in (bv_unsigned shift) in
      constr_eq distance 8%Z;
      match goal with
      | H : ?statement |- _ =>
          lazymatch type of statement with Prop => idtac end;
          zesu_loop_fold_conjunct accumulator bytes start H statement ltac:(fun Hfold count =>
            match goal with
            | Hnext : bytes !! ?position = Some next |- _ =>
                let Hposition := fresh "HfoldPosition" in
                assert (Hposition : position = (start + Z.to_nat count)%nat) by
                  RegisterArrayCursor.zesu_cursor_step_solve;
                let Hcount := fresh "HfoldCount" in
                assert (Hcount : Z.to_nat count' = S (Z.to_nat count)) by
                  RegisterArrayCursor.zesu_cursor_step_solve;
                let Hbound := fresh "HfoldBound" in
                assert (Hbound : (S (Z.to_nat count) <= 8)%nat) by
                  RegisterArrayCursor.zesu_cursor_step_solve;
                let Hnth := fresh "HfoldNth" in
                assert (Hnth : nth_error bytes (start + Z.to_nat count) = Some next) by
                  (rewrite -Hposition -zesu_loop_lookup_nth_error; exact Hnext);
                let Hold := fresh "HfoldOld" in
                assert (Hold : Z_to_bv 64 (ByteWindowFold.zesu_byte_window_fold bytes start
                  (Z.to_nat count)) = accumulator) by
                  (rewrite -Hfold; apply Z_to_bv_bv_unsigned);
                rewrite Hcount -Hold;
                exact (ByteWindowFoldWord.zesu_byte_window_unsigned_step bytes start
                  (Z.to_nat count) next Hbound Hnth)
            end)
      end
  end.

(* A pure goal about a loop cursor: try the retained conjuncts, the fold step,
   and selected cursor arithmetic. The last needs a cursor marker on a word
   in the goal. *)
Ltac zesu_loop_pure_finish :=
  lazymatch goal with |- ?target => lazymatch type of target with Prop => idtac end end;
  first [
    solve [zesu_loop_conjunct_close]
  | solve [zesu_loop_fold_step]
  | lazymatch goal with
    | |- context [@bv_unsigned _ ?word] =>
        let register := lazymatch word with bv_add ?inner _ => inner | _ => word end in
        is_var register;
        lazymatch goal with
        | _ : RegisterArrayCursor.zesu_register_cursor_attempted register |- _ =>
            solve [RegisterArrayCursor.zesu_cursor_step_solve]
        end
    end].
