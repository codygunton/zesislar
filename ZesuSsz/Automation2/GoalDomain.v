From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.Rewrites.
From Coq Require Import ZArith Lia.
Require Import ZesuSsz.Automation2.LiaHook.
Require ZesuSsz.Automation2.Hooks.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.DomainRanges.
Require ZesuSsz.Automation2.ContextCollection.
From Coq Require Import Strings.String.

(* A pure goal whose head a contract registers in `zesu_goal_domain`: a
   callee's call-site domain that is a conjunction of address arithmetic
   (lengths, ranges, separations) over the caller's own domain. The step
   unfolds the registered heads in the goal and in the context, splits the
   conjunctions, and closes every part with `lia` or `bv_solve` over the
   bitvector images. `solve` keeps it all-or-nothing: a goal it cannot close
   stays exactly as it was. A goal with no registered head costs one failed
   `progress`.

   A proved callee's call-site domain is sealed (ZesuSsz/Interfaces/<F>.v):
   the step never unfolds it. Its interface registers the lemma that
   introduces it from the callee's stated precondition as a
   `ZesuGoalDomainIntro` instance, and the precondition's public names in
   `zesu_goal_domain`; the step applies the lemma, then unfolds the
   precondition. *)
Create HintDb zesu_goal_domain.

Class ZesuStepGoalDomain : Prop := zesu_step_goal_domain : True.

Class ZesuGoalDomainIntro (goal premise : Prop) : Prop :=
  zesu_goal_domain_intro : premise -> goal.
#[global] Hint Mode ZesuGoalDomainIntro ! - : typeclass_instances.

(* Apply the registered introduction of a sealed domain and unfold the
   precondition it leaves; or unfold a registered head. The introduction
   comes first: unfolding the arguments of a sealed domain is progress that
   leaves the domain sealed. *)
Ltac zesu_goal_domain_open :=
  first
    [lazymatch goal with
     | |- ?goal =>
         let premise := fresh "premise" in
         evar (premise : Prop);
         let intro := fresh "intro" in
         assert (intro : ZesuGoalDomainIntro goal premise) by (unfold premise; typeclasses eauto);
         unfold premise in intro; clear premise;
         apply intro; clear intro;
         progress (autounfold with zesu_goal_domain)
     end
    |progress (autounfold with zesu_goal_domain)].

(* The goal is a sealed callee domain: it has a registered introduction.
   Such a goal is opaque to every solver; `lia` or `bv_solve` on it only
   search the context for a contradiction, which on a large context does not
   end (Finish.v runs the introduction instead). *)
Ltac zesu_goal_domain_sealed :=
  lazymatch goal with
  | |- ?goal =>
      assert_succeeds (
        let premise := fresh "premise" in
        evar (premise : Prop);
        let intro := fresh "intro" in
        assert (intro : ZesuGoalDomainIntro goal premise)
          by (unfold premise; typeclasses eauto))
  end.

(* lia and bv_solve never close an existential, nor a witness that `split`
   leaves as a goal of a type such as `bv 64`: on a large context they only
   search the whole context for a contradiction (a call's precondition
   restated over fresh names, 274 hypotheses: lia on its first witness grew
   past 8 GiB). *)
Ltac zesu_final_solver_goal :=
  lazymatch goal with
  | |- ex _ => fail 0
  | |- ?target => lazymatch type of target with Prop => idtac end
  end.

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
