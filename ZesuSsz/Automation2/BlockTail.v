Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.LiaHook.
Require ZesuSsz.Automation2.PureFacts.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.WrappedWord.
Require ZesuSsz.Automation2.CallSlice.
Require ZesuSsz.Automation2.BytePositionEquations.
Require ZesuSsz.Automation2.ByteWindowFold.
Require ZesuSsz.Automation2.Finish.
Require ZesuSsz.Automation2.Hooks.
Require ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Automation2.LoopExit.
From iris.proofmode Require Import environments tactics.
From stdpp Require Import base list decidable bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith Lia Bool.
Local Open Scope Z_scope.

(* The tail that every block runs once on each goal `zesu_block_base` and the
   residual tiers leave: goals in a normal form no earlier step reaches. *)

(* The list index of a load: literal list index, then the window as byte
   positions. *)
Ltac zesu_tail_window_normal :=
  repeat match goal with
  | |- context[drop (Z.to_nat ?e) _] =>
      ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_literal e ltac:(fun Hindex => rewrite Hindex)
  end;
  repeat ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_rewrite_one.

(* Linear arithmetic over the order facts of the context only: no div, mod,
   land or signed view reaches lia. *)
Ltac zesu_tail_keep_fact T :=
  lazymatch T with
  | (_ <= _ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ < _)%Z => idtac
  | (_ >= _)%Z => idtac | (_ > _)%Z => idtac
  | (_ <= _)%Z /\ (_ <= _)%Z => idtac
  | @eq Z _ _ => idtac | not (@eq Z _ _) => idtac
  end;
  lazymatch T with
  | context [Z.modulo] => fail | context [Z.div] => fail | context [Z.land] => fail
  | context [bv_signed] => fail
  | _ => idtac
  end.
Ltac zesu_tail_lia_select :=
  repeat match goal with
  | |- context [bv_unsigned ?w] =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned w < _)%Z |- _ => fail
      | _ => pose proof (bv_unsigned_in_range _ w)
      end
  end;
  repeat match goal with H : ?T |- _ => zesu_tail_keep_fact T; revert H end;
  ZesuSsz.Automation2.WrappedWord.zesu_clear_all_hyps; intros;
  change (bv_modulus 64) with 18446744073709551616 in *;
  repeat match goal with
  | H : context [@length ?T ?x] |- _ =>
      lazymatch T with bv 8 => fail | _ => idtac end;
      change (@length T x) with (@length (bv 8) x) in H
  end;
  repeat match goal with
  | |- context [@length ?T ?x] =>
      lazymatch T with bv 8 => fail | _ => idtac end;
      change (@length T x) with (@length (bv 8) x)
  end;
  ZesuSsz.Automation2.CallSlice.zesu_call_slice_lia.

(* A generated window fact `0 < a -> a <= k -> window` whose premises are
   branch facts. *)
Ltac zesu_tail_order_goal :=
  first [ assumption
        | match goal with H : bv_unsigned ?w <> 0%Z |- (0 < bv_unsigned ?w)%Z => exact (ZesuSsz.Automation2.CallSlice.zesu_call_slice_unsigned_pos _ w H) end
        | solve [zesu_tail_lia_select] ].
Ltac zesu_tail_forward_window_facts :=
  repeat match goal with
  | Himp : ((0 < ?a)%Z -> (?a <= ?k)%Z -> ?r) |- _ =>
      let H := fresh "HtailWindow" in
      assert (H : r) by (apply Himp; zesu_tail_order_goal);
      clear Himp;
      destruct H as [? ?]
  end.
Ltac zesu_tail_add_exact_rewrite :=
  repeat match goal with
  | |- context [bv_unsigned (@bv_add 64 ?a ?b)] =>
      let H := fresh "HtailAdd" in
      assert (H : bv_unsigned (bv_add a b) = (bv_unsigned a + bv_unsigned b)%Z)
        by (apply ZesuSsz.Automation2.CallSlice.zesu_call_slice_add_exact; zesu_tail_lia_select);
      rewrite H; clear H
  end.
(* Every conjunct that closes; a conjunct that does not stays open. *)
Ltac zesu_tail_pure_closer :=
  repeat match goal with |- _ /\ _ => split end;
  first [ reflexivity
        | exact (eq_sym (Z.add_0_r _))
        | assumption
        | solve [zesu_tail_add_exact_rewrite; zesu_tail_lia_select]
        | idtac ].

(* Entering a loop head: the index starts at 0; the invariant follows from the
   window fact of the call before the loop. *)
Ltac zesu_tail_loop_entry :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ (li_prod (lithium.lvar.lvar "zesuLoopIndex" Z) unit) _) =>
      zesu_tail_window_normal;
      try ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
      zesu_tail_forward_window_facts;
      iExists (li_pair 0%Z tt);
      cbv [li_fst li_snd];
      repeat (first [ ZesuSsz.Automation2.Hist.zesu_hist_step
                    | iSplit; [iPureIntro; zesu_tail_pure_closer|]
                    | iSplit; [iPureIntro|] ]);
      try iFrame
  end.

(* A pure equation between two spellings of loaded words. *)
Ltac zesu_tail_window_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- context [little_endian_to_bv 8 (take _ (drop _ _))] =>
      zesu_tail_window_normal;
      first [ reflexivity | solve [ZesuSsz.Automation2.Finish.zesu_finish] ]
  end.

(* A pure existential conjunction whose conjuncts are hypotheses, up to the
   round trip `bv_unsigned (Z_to_bv 64 z) = z` of an in-range integer (the
   finisher rewrites it in the goal). *)
Ltac zesu_tail_roundtrip_exact :=
  match goal with
  | H : ?T |- _ =>
      match T with
      | context [bv_unsigned (Z_to_bv 64 ?z)] =>
          let E := fresh "HtailRound" in
          assert (E : bv_unsigned (Z_to_bv 64 z) = z)
            by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; ZesuSsz.Automation2.WrappedWord.zesu_zroot_range z);
          let H2 := fresh "HtailView" in
          pose proof H as H2;
          rewrite E in H2;
          eexact H2
      end
  end.
Ltac zesu_tail_exists_conj_core :=
  repeat eexists;
  repeat match goal with |- _ /\ _ => split end;
  first [ eassumption | zesu_tail_roundtrip_exact ].
(* A conjunct can follow only from a folded precondition (a domain predicate
   of conjunctions) once it is opened; `repeat eexists` unfolds a defined
   conjunct into its parts, which then stand as separate goals. The opening
   runs only after the plain attempt fails, so a goal that closes without it
   keeps its existing route, and a context with nothing folded fails at once
   (`zesu_open_folded_facts` fails when it opens nothing). *)
Ltac zesu_tail_exists_conj :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- @ex _ _ => idtac
  end;
  first [ solve [zesu_tail_exists_conj_core]
        | ZesuSsz.Automation2.Hooks.zesu_open_folded_facts;
          solve [zesu_tail_exists_conj_core] ].

(* The length of a list built from pieces of known length. *)
Ltac zesu_tail_length_goal :=
  lazymatch goal with
  | |- @eq nat ?l ?r =>
      lazymatch l with context [@length] => idtac end
  end;
  repeat match goal with
  | H : length ?l = _ |- context [length ?l] => rewrite H
  end;
  rewrite ?length_app; cbn [length Nat.add];
  repeat match goal with
  | H : length ?l = _ |- context [length ?l] => rewrite H
  end;
  reflexivity.

(* A branch fact the entry states on the window
   `Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop (Z.to_nat e) l)))` with a
   frame index e, while the goal reads the same word as byte positions: index
   literal and byte-position form in the hypotheses, a signed compare of a
   zero-extended word as the unsigned word, then the fact itself or lia. *)
Ltac zesu_tail_hyp_window :=
  repeat match goal with
  | H : context [drop (Z.to_nat ?e) _] |- _ =>
      ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_literal e ltac:(fun Hi => rewrite Hi in H)
  end;
  repeat match goal with
  | H : context [Z_to_bv ?w (little_endian_to_bv 8 (take ?c (drop ?s ?l)))] |- _ =>
      ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_equation w c s l ltac:(fun Hw => rewrite Hw in H)
  end.
Ltac zesu_tail_signed_closed :=
  repeat match goal with
  | |- context [bv_signed (bv_zero_extend 128 ?x)] => rewrite (zesu_signed_zero_extend_64_128 x)
  end;
  repeat match goal with
  | |- context [@bv_signed ?n ?t] =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed t;
      let v := eval vm_compute in (bv_signed t) in
      change (@bv_signed n t) with v
  end.
Ltac zesu_tail_branch_fact_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- context [bv_concat] => idtac
  end;
  zesu_tail_hyp_window; zesu_tail_signed_closed;
  first [ assumption | solve [zesu_tail_lia_select] ].

(* An edge premise that is a boolean disjunction of branch guards: split every
   bool_decide in goal and hypotheses; a branch that is not `true = true` must
   contradict a branch fact. *)
Ltac zesu_tail_contra :=
  exfalso;
  first [ congruence
        | solve [zesu_tail_hyp_window; zesu_tail_signed_closed;
                 first [contradiction | solve [zesu_tail_lia_select]]]
        | solve [bv_solve]
        | solve [zesu_lia] ].
Ltac zesu_tail_bool_disj :=
  lazymatch goal with |- (orb _ _) = true => idtac | |- negb _ = true => idtac end;
  zesu_tail_window_normal;
  repeat (case_bool_decide);
  cbn [negb orb andb];
  first [ reflexivity | zesu_tail_contra ].

(* An edge premise that is the fold over a zero-length window. *)
Lemma zesu_tail_fold_zero (l : list (bv 8)) (s : nat) (n : Z) :
  n = 0 -> 0 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold l s (Z.to_nat n).
Proof. intros ->. reflexivity. Qed.
Ltac zesu_tail_fold_zero_goal :=
  lazymatch goal with
  | |- bv_unsigned ?z = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold _ _ (Z.to_nat ?n) =>
      change (bv_unsigned z) with 0; apply zesu_tail_fold_zero;
      first [ assumption | solve [zesu_tail_branch_fact_goal] | solve [bv_solve] | solve [zesu_lia]
            | (zesu_tail_hyp_window; solve [zesu_tail_lia_select]) ]
  end.

Ltac ZesuSsz.Automation2.Finish.zesu_block_tail_one ::=
  first
  [ zesu_tail_bool_disj
  | zesu_tail_fold_zero_goal
  | zesu_cursor_index_close
  | zesu_tail_window_goal
  | solve [zesu_tail_exists_conj]
  | solve [zesu_tail_length_goal]
  | solve [zesu_tail_branch_fact_goal]
  | zesu_tail_loop_entry
  | solve [ZesuSsz.Automation2.Hist.zesu_hist_exit_view]
  | zesu_loop_exit_witnesses ].
