(* C6: the facts a side condition needs are folded inside one hypothesis.

   A segment carries its witness's well-formedness as a single premise.
   Every arithmetic side condition the block raises -- an alignment, a
   range, an array index -- is a consequence of it, but no solver can see
   through the name: `bv_solve` and `lia` read hypotheses, and
   `writeSuccessWitnessWellFormed args witness` is not a conjunction until
   something unfolds it.

   Two steps answer that, and neither names a project definition.

   `zesu_split_folded_pure` unfolds a hypothesis one delta step and splits
   it when what comes out is a conjunction. It is the C6 class of the
   residual corpus, and it is cheap because it is tried only on a goal the
   rest of the finisher has already refused.

   `zesu_saturate_derived_facts` adds what a registered lemma derives from
   a hypothesis. A project states the derivation once, as a
   `ZesuDerivedFacts` instance beside the lemma; the tactic finds it by
   the hypothesis's type. This is how a fact about a name the automation
   cannot unfold -- a frame pointer defined from an entry pointer, say --
   reaches the solver without a hand line in any segment. *)

Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.

(* A nonempty owned list supplies its head and tail without guessing data. *)
Lemma zesu_list_cons_witness {A : Type} (values : list A) (count : nat) :
  length values = S count ->
  exists head tail, values = head :: tail /\ length tail = count.
Proof.
  destruct values as [|head tail]; simpl; [discriminate|].
  intro Hlength. exists head, tail. split; [reflexivity|].
  now injection Hlength.
Qed.

Class ZesuDerivedFacts (premise derived : Prop) : Prop :=
  zesu_derived_facts : premise -> derived.

Ltac zesu_split_folded_pure :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac end;
      lazymatch T with
      | _ /\ _ => fail
      | _ =>
          let unfolded := eval hnf in T in
          lazymatch unfolded with
          | _ /\ _ => change unfolded in H; destruct H
          end
      end
  end.

Ltac zesu_saturate_derived_facts :=
  repeat match goal with
  | H : ?T |- _ =>
      let instance := constr:(_ : ZesuDerivedFacts T _) in
      lazymatch type of instance with
      | ZesuDerivedFacts _ ?derived =>
          lazymatch goal with
          | _ : derived |- _ => fail
          | _ => pose proof (zesu_derived_facts (ZesuDerivedFacts := instance) H)
          end
      end
  end.

(* Everything the witness says, in the form a solver reads. *)
Ltac zesu_witness_facts :=
  zesu_saturate_derived_facts; zesu_split_folded_pure.

(* The arithmetic goal an array index raises, once the witness's facts are
   readable: a length behind `take` or `drop`, a machine bound behind a
   name, and a frame pointer inside a bitvector addition. Each step is a
   normalization; `lia` and `bv_solve` do the work.

   `progress` first, and it is not decoration. Without it the step runs
   `lia` and `bv_solve` a second time on every pure goal the finisher has
   already refused, which is most of them, and a proof under an enclosing
   `timeout` loses its budget to work that cannot succeed. With it the
   step costs one failed match wherever there is nothing folded to
   unfold. *)
Ltac zesu_witness_arith :=
  progress zesu_witness_facts;
  rewrite ?length_take ?length_drop ?length_app ?length_insert;
  (* The space before the bracket matters: a star followed straight by
     a bracket closes a Coq comment and truncates the tactic. *)
  try (cbv [machineRamEnd mapRamSize mapRamBase defaultMap] in * );
  first [lia | bv_solve].

(* Opt in, like every other rule on this branch.

   The step changes what the default finisher closes, and a goal that
   closes earlier is still a change: `WriteSuccessExactSuffixHashesTailLoop.v`
   has a hand line that becomes dead, and the proof then fails with "0
   goals are focused". Rule set v1 has to keep its outcomes exactly, so
   the step asks for an instance that only v2 provides. Resolving a class
   with no instance costs one failed lookup. *)
(* Two levels of switch, because they answer two questions.

   `ZesuRuleSetV2` selects the pass: `zesu_run_pass` in `Finish.v` asks
   for it once per pass and runs `zesu_run_pass_v2` when it resolves.
   Each of these steps makes the search close something it used to leave
   open, and a goal that closes earlier breaks a proof that had a line
   for it, so rule set v1 must never reach an instance of it.

   Each step also has a class of its own, so that one benchmark arm can
   measure one rule. `Automation/Switch.v` provides them all;
   `Automation/Switches/<step>.v` provides one, beside the
   `ZesuRuleSetV2` instance that the pass needs in either case. *)
Class ZesuRuleSetV2 : Prop := zesu_rule_set_v2 : True.

Ltac zesu_rule_set_v2_on :=
  let _ := constr:(_ : ZesuRuleSetV2) in idtac.

Class ZesuStepWitnessArith : Prop := zesu_step_witness_arith : True.

Ltac zesu_step_witness_arith_on :=
  let _ := constr:(_ : ZesuStepWitnessArith) in idtac.

Ltac zesu_witness_arith_if_enabled :=
  zesu_step_witness_arith_on; zesu_witness_arith.

(* Expose retained conjunctions without changing their original hypotheses. *)
Ltac zesu_integer_array_emit_facts proof :=
  let statement := type of proof in
  let expanded := eval hnf in statement in
  lazymatch expanded with
  | ?left /\ ?right =>
      let leftProof := constr:(@proj1 left right proof) in
      let rightProof := constr:(@proj2 left right proof) in
      zesu_integer_array_emit_facts leftProof;
      zesu_integer_array_emit_facts rightProof
  | _ =>
      lazymatch goal with
      | _ : statement |- _ => idtac
      | _ => let name := fresh "HarrayFact" in pose proof proof as name
      end
  end.

Ltac zesu_integer_array_facts :=
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      progress zesu_integer_array_emit_facts H
  end.
