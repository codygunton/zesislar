(* The goal-domain solver: each conjunct of an opened sealed callee domain
   over the facts that share its atoms (GoalDomain.v holds the registration
   and the opening). Separate from GoalDomain.v because it needs the hooks
   (Hooks.v) and the context selection: GoalDomain.v is loaded by the
   callees' interfaces, and loading Hooks.v there would change the global
   solver redefinitions (bv_solve, ...) of every module that imports an
   interface. *)
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.Rewrites.
From Coq Require Import ZArith Lia.
Require Import ZesuSsz.Automation2.LiaHook.
Require Import ZesuSsz.Automation2.GoalDomain.
Require ZesuSsz.Automation2.Hooks.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.DomainRanges.
Require ZesuSsz.Automation2.ContextCollection.
From Coq Require Import Strings.String.

(* The closed words of a conjunct as their values (`bv_unsigned` of a
   literal is an atom to lia; a frame-slot address reads two of them). *)
Ltac zesu_goal_domain_closed_words :=
  repeat match goal with
  | |- context [bv_unsigned ?c] =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term c;
      let v := eval vm_compute in (bv_unsigned c) in
      change (bv_unsigned c) with v
  end.

(* The range of every word the conjunct reads, as a fact the selection
   keeps (it shares the word with the conjunct). *)
Ltac zesu_goal_domain_word_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?w] =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned w < _)%Z |- _ => fail
      | _ =>
          let H := fresh "HdomainWord" in
          pose proof (bv_unsigned_in_range _ w) as H;
          unfold bv_modulus in H; cbn [Z.of_N] in H
      end
  end.

(* The integer form of each length fact `length l = n` about a list the
   conjunct reads, at the conjunct's element type: the selection takes
   `Z.of_nat (length l)` and `length l` for different atoms, and lia an
   alias of the element type (`byte`, `bv 8`) for a different list. *)
Ltac zesu_goal_domain_lengths :=
  repeat match goal with
  | |- context [@List.length ?A ?l] =>
      match goal with
      | H : @List.length _ l = ?n |- _ =>
          lazymatch goal with
          | _ : Z.of_nat (@List.length A l) = _ |- _ => fail
          | _ =>
              (* stated at the conjunct's element type (an alias of the
                 hypothesis's may differ, and lia compares atoms
                 syntactically) *)
              let E := fresh "HdomainLength" in
              assert (E : Z.of_nat (@List.length A l) = Z.of_nat n)
                by exact (f_equal Z.of_nat H);
              cbn [Z.of_nat Pos.of_succ_nat] in E
          end
      | H : Z.of_nat (@List.length ?B l) = ?n |- _ =>
          assert_fails (constr_eq A B);
          lazymatch goal with
          | _ : Z.of_nat (@List.length A l) = _ |- _ => fail
          | _ =>
              let E := fresh "HdomainLength" in
              assert (E : Z.of_nat (@List.length A l) = n) by exact H
          end
      end
  end.

(* lia, and for a remainder or divisibility conjunct (an alignment of a
   frame slot, `(8 | (sp + c) mod 2^64)`) the quotients and remainders as
   equations first: lia alone finds no witness for them. *)
Ltac zesu_goal_domain_lia :=
  first
    [zesu_lia
    |(try (apply Z.mod_divide; [zesu_lia|])); Z.div_mod_to_equations; zesu_lia].

(* Each conjunct over the facts that share its atoms, its words' ranges
   among them: a block's whole context makes lia search for a contradiction
   that does not end (r50 0x0248, a keysToOwnedSlice call domain: whole-
   context lia on a modular frame address ran past 120 s). *)
Ltac zesu_goal_domain_part :=
  zesu_final_solver_goal;
  zesu_goal_domain_closed_words;
  zesu_goal_domain_word_ranges;
  zesu_goal_domain_lengths;
  first
    [ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
       ("goal_domain.selected"%string) ltac:(zesu_goal_domain_lia)
    |lazymatch goal with |- context [bv_unsigned _] =>
       ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
         ("goal_domain.bv"%string) ltac:(bv_solve)
     end].

(* An existential goal is refused before anything is unfolded: every part
   of it would be a witness or an existential. *)
Ltac zesu_finish_goal_domain :=
  let _ := constr:(_ : ZesuStepGoalDomain) in
  zesu_final_solver_goal;
  solve [
    zesu_goal_domain_open; cbn;
    zesu_witness_facts;
    (* the plain ranges of the context's domains, small facts the parts'
       selection keeps (DomainRanges.v) *)
    ZesuSsz.Automation2.DomainRanges.zesu_pose_domain_ranges;
    (* the conjunctions of the context as their parts, so the selection
       keeps the parts a conjunct shares atoms with *)
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    autounfold with zesu_contract_constants zesu_goal_domain in *;
    (* one normal form of the machine map in the goal and the hypotheses:
       `cbn` above reduced the goal's `mapRamBase defaultMap` to its value,
       a hypothesis that states the same bound keeps the projection, and
       lia would see two atoms *)
    ZesuSsz.Automation2.Hooks.zesu_normalize_machine_map;
    rewrite ?bv_add_unsigned;
    unfold bv_wrap, bv_modulus in *; cbn [Z.of_N] in *;
    repeat split; zesu_goal_domain_part].
