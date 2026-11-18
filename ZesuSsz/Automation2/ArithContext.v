From Coq Require Import ZArith.ZArith Lists.List NArith.NArith Lia.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import isla.riscv64.riscv64.
Require SailStdpp.MachineWord.
Require Import ZesuSsz.Contracts.NamedEquation.
Require ZesuSsz.Automation.PureFacts.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.RangeFacts.
Require ZesuSsz.Automation2.ContextCollection.
Require ZesuSsz.Automation2.BytePositionEquations.
Require Import ZesuSsz.Automation2.LiaHook.
Require Import ZesuSsz.Automation2.LinearFirstLia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* One step for a pure arithmetic goal whose facts sit in the context in a
   form no solver reads: a register a call boundary kept under a name
   (`zesu_named_eq`), a sealed callee predicate whose facts its interface
   registers as `ZesuDerivedFacts`, and the function's own precondition
   folded under one name. `zesu_arith_context_solve`
   (i) opens the named equations whose names occur in the goal, and those
       whose names occur in a value already opened;
   (ii) keeps the facts that share a value word with the goal (one hop),
       adds the registered derived facts of the kept sealed predicates, and
       projects the arithmetic conjuncts of the folded precondition over the
       contract arguments the goal reads;
   (iii) normalizes the terms to one atom per value and runs the solver on
       that pruned context.
   It is used wherever such a goal arises: a call-site domain part
   (GoalDomain), the bounds of a lent slice (InteriorByteSlice). All or
   nothing: callers run it under `solve`. *)

(* (i) A named value reads as its value; between bitvectors the unsigned
   images are equal as well. Only names the goal mentions, transitively. *)
Ltac zesu_arith_open_names :=
  repeat match goal with
  | H : zesu_named_eq ?name ?value |- ?target =>
      first [lazymatch target with context [name] => idtac end
            | match goal with
              | _ : @eq _ _ ?opened |- _ => lazymatch opened with context [name] => idtac end
              end];
      let E := fresh "HarithNamed" in
      pose proof (proj1 (zesu_named_eq_iff name value) H) as E; clear H;
      lazymatch type of name with
      | bv ?n => pose proof (f_equal (@bv_unsigned n) E)
      | _ => idtac
      end
  end.

(* A little-endian load window of a list reads as its byte positions, the
   form in which a callee's outputs and the call windows state it. *)
Ltac zesu_arith_le_windows :=
  repeat ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_rewrite_one;
  repeat match goal with
  | H : context [Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?bytes)))] |- _ =>
      ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_equation width count start bytes
        ltac:(fun Hwindow => rewrite Hwindow in H)
  end.

(* (ii) The facts the goal can use: those that mention a value word of the
   goal (a word, integer, count or byte list; local definitions read through
   to the words they are built from), and the facts over contract arguments
   alone (the caller's precondition). One hop: a fact is not kept because it
   shares a word with another kept fact, and a contract argument links
   nothing (every call's sealed facts mention the caller's input). A block
   context chains its calls (each call's cursor is the last one's plus its
   consumed count), so the transitive closure is the whole context: the
   derived-fact saturation on it ran past 800 s on a decodeParentHeader
   block. A fact whose words cannot be read is kept. *)
Ltac2 zesu_arith_value_word (name : ident) :=
  let ty := Constr.type (Control.hyp name) in
  lazy_match! ty with
  | bv _ => true
  | Z => true
  | nat => true
  | N => true
  | bool => true
  | list _ => true
  | _ => false
  end.

Ltac2 zesu_arith_focus () :=
  let hyps := Control.hyps () in
  let variables term :=
    Control.once_plus (fun () => Some (ZesuSsz.Automation2.ContextCollection.zesu_context_variables term))
      (fun _ => None) in
  let seeds := match variables (Control.goal ()) with
    | Some found => found
    | None => Control.zero (Tactic_failure None) end in
  let rec close found :=
    let next := List.fold_left (fun found declaration =>
      let (name, body, _) := declaration in
      match body with
      | Some value =>
          if ZesuSsz.Automation2.ContextCollection.zesu_context_member name found then
            match variables value with
            | Some inner => ZesuSsz.Automation2.ContextCollection.zesu_context_union found inner
            | None => found
            end
          else found
      | None => found
      end) found hyps in
    if Int.equal (List.length next) (List.length found) then found else close next in
  let seeds := List.filter zesu_arith_value_word (close seeds) in
  List.iter (fun declaration =>
    let (name, body, ty) := declaration in
    match body with
    | Some _ => ()
    | None =>
        if ZesuSsz.Automation2.ContextCollection.zesu_context_proposition ty then
          match variables ty with
          | Some found =>
              let words := List.filter zesu_arith_value_word found in
              if Int.equal (List.length words) 0 then ()
              else if ZesuSsz.Automation2.ContextCollection.zesu_context_intersects words seeds then ()
              else Control.once_plus (fun () => Std.clear [name]) (fun _ => ())
          | None => ()
          end
        else ()
    end) (List.rev hyps).

Ltac zesu_arith_focus := ltac2:(zesu_arith_focus ()).

(* Closed integer subterms of one selected fact, evaluated (a contract's
   named constants). The fact is small; the goal is not touched. *)
Ltac zesu_arith_reduce_closed_in H :=
  repeat match type of H with
  | context[?term] =>
      lazymatch type of term with Z => idtac end;
      lazymatch term with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
      let value := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term in
      progress change term with value in H
  end.

(* A value word of a contract argument (`bv_unsigned (accessor argument)`):
   its range facts sit folded in the caller's precondition over that
   argument. Project the conjuncts that state it, as the region bounds do,
   and evaluate their constants. *)
Ltac zesu_arith_root_ranges base :=
  let root := lazymatch base with
    | bv_unsigned (?accessor ?argument) => constr:(argument)
    | _ => base end in
  let collect := ltac2:(v p r |- ZesuSsz.Automation2.RangeFacts.zesu_range_collect
    (Option.get (Ltac1.to_constr v)) (Option.get (Ltac1.to_constr p))
    (Option.get (Ltac1.to_constr r))) in
  collect base base root;
  let reduce := ltac:(fun H => zesu_arith_reduce_closed_in H) in
  let reduce_selected := ltac2:(r |- List.iter (fun h => let (name, _, _) := h in
    if ZesuSsz.Automation2.RangeFacts.zesu_name_prefix (Ident.to_string name) "HrangeFact" 0
    then Ltac1.apply r [Ltac1.of_constr (Control.hyp name)] Ltac1.run
    else ()) (Control.hyps ())) in
  reduce_selected reduce.

(* The contract-argument words of the goal: `bv_unsigned (accessor x)` with
   `x` a variable. *)
Ltac2 rec zesu_arith_argument_words (term : constr) (found : constr list) : constr list :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      let found := Array.fold_left (fun found a => zesu_arith_argument_words a found) found arguments in
      if Bool.and (Constr.equal head '@bv_unsigned) (Int.equal (Array.length arguments) 2) then
        match Constr.Unsafe.kind (Array.get arguments 1) with
        | Constr.Unsafe.App _ fields =>
            if Int.equal (Array.length fields) 1 then
              match Constr.Unsafe.kind (Array.get fields 0) with
              | Constr.Unsafe.Var _ =>
                  if List.exist (fun t => Constr.equal t term) found then found else term :: found
              | _ => found
              end
            else found
        | _ => found
        end
      else found
  | _ => found
  end.

Ltac zesu_arith_goal_ranges :=
  let each := ltac2:(r |- List.iter (fun word => Ltac1.apply r [Ltac1.of_constr word] Ltac1.run)
    (zesu_arith_argument_words (Control.goal ()) [])) in
  each ltac:(fun word => try zesu_arith_root_ranges word).

(* (iii) Element-type and width aliases normalized so that the arithmetic
   sees one atom per term. *)
Ltac zesu_arith_alias_normalize :=
  repeat match goal with
  | H : context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] |- _ =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v in H
  | |- context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v
  | H : context[@length ?T ?l] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l) in H
  | |- context[@length ?T ?l] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l)
  | H : context[@List.nth ?T ?k ?l ?d] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d) in H
  | |- context[@List.nth ?T ?k ?l ?d] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d)
  end.

(* A hypothesis word convertible to a goal word is restated in the goal's
   form, whatever alias it was elaborated at. *)
Ltac zesu_arith_goal_atoms :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?a] =>
      match goal with
      | H : context[@bv_unsigned ?m ?b] |- _ =>
          assert_fails (constr_eq a b);
          assert_fails (has_evar b);
          unify (@bv_unsigned m b) (@bv_unsigned n a);
          change (@bv_unsigned m b) with (@bv_unsigned n a) in H
      end
  end.

Ltac zesu_arith_unsigned_range n x :=
  assert_fails (has_evar x);
  lazymatch goal with
  | _ : (0 <= @bv_unsigned n x < _)%Z |- _ => fail
  | _ => pose proof (bv_unsigned_in_range n x)
  end.

Ltac zesu_arith_unsigned_ranges :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?x] => zesu_arith_unsigned_range n x
  | _ : context[@bv_unsigned ?n ?x] |- _ => zesu_arith_unsigned_range n x
  end.

(* A word read from list bytes (a callee's output) is an opaque atom to
   arithmetic: that it is positive holds only where a fact states it (a
   branch on the word; the decodeItem interface states no such bound, since a
   successful decode may return an empty payload). Such a premise comes from
   that fact or fails; it never reaches `lia`, which on a decodeParentHeader
   caller's context grew past 24 GiB on it. *)
Lemma zesu_arith_unsigned_pos_of_neq n (w : bv n) :
  bv_unsigned w <> 0%Z -> (0 < bv_unsigned w)%Z.
Proof. pose proof (bv_unsigned_in_range n w). lia. Qed.

Ltac zesu_arith_list_word_positive_goal :=
  lazymatch goal with
  | |- (0 < @bv_unsigned _ ?w)%Z =>
      lazymatch w with
      | bv_concat _ _ _ => idtac
      | Z_to_bv _ (little_endian_to_bv _ _) => idtac
      end
  end.

Ltac zesu_arith_positive_from_facts :=
  lazymatch goal with
  | |- (0 < @bv_unsigned ?n ?w)%Z =>
      first [assumption |
        match goal with
        | H : not (@eq Z (@bv_unsigned _ ?v) Z0) |- _ =>
            unify v w; exact (zesu_arith_unsigned_pos_of_neq n w H)
        | H : not (@eq Z Z0 (@bv_unsigned _ ?v)) |- _ =>
            unify v w; exact (zesu_arith_unsigned_pos_of_neq n w (not_eq_sym H))
        end]
  end.

(* A derived fact stated under premises: each premise the context shows,
   directly or by arithmetic, is discharged. A premise is tried once: a fact
   whose premise fails is dropped from this local proof, so a later success
   does not retry every failed premise. *)
Ltac zesu_arith_discharge_premises :=
  repeat match goal with
  | H : ?P -> ?Q |- _ =>
      lazymatch type of P with Prop => idtac end;
      first [
        let Hp := fresh "Hpremise" in
        assert (Hp : P) by (first [assumption |
          tryif zesu_arith_list_word_positive_goal
          then zesu_arith_positive_from_facts else zesu_lia]);
        specialize (H Hp); clear Hp
      | clear H ]
  end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac zesu_arith_moduli :=
  repeat match goal with
  | H : context[bv_modulus ?n] |- _ =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v in H
  | |- context[bv_modulus ?n] =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v
  end.

(* The unsigned value of a closed word (an offset the code adds) is its
   integer. *)
Ltac zesu_arith_literal_words :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?w] =>
      let value := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (@bv_unsigned n w) in
      change (@bv_unsigned n w) with value
  end.

(* The arithmetic on the facts in context: derived facts added, lengths of
   slices unfolded, sums and differences of words read without wrap where
   the facts bound them, the solver run within the pruned-context budget. *)
Ltac zesu_arith_bounds :=
  ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with
  | H : context[length (take _ _)] |- _ => rewrite length_take in H
  | H : context[length (drop _ _)] |- _ => rewrite length_drop in H
  end;
  rewrite ?length_take ?length_drop ?bv_add_unsigned ?bv_sub_unsigned; unfold bv_wrap;
  zesu_arith_unsigned_ranges;
  zesu_arith_alias_normalize;
  zesu_arith_moduli;
  zesu_arith_discharge_premises;
  zesu_arith_goal_atoms;
  zesu_arith_literal_words;
  repeat match goal with
  | |- context[(?a mod ?m)%Z] =>
      lazymatch a with context[Z.modulo] => fail | _ => idtac end;
      rewrite (Z.mod_small a m); [|zesu_lia]
  end;
  zesu_lia_pruned_context_within_budget;
  zesu_lia.

(* The context the arithmetic reads: (i) and (ii) above. *)
Ltac zesu_arith_context_prepare :=
  zesu_arith_open_names;
  zesu_arith_focus;
  zesu_arith_le_windows;
  zesu_arith_goal_ranges.

Ltac zesu_arith_context_solve :=
  zesu_arith_context_prepare;
  zesu_arith_bounds.

(* With the range facts of a word the goal need not mention (the base of
   the array a slice is lent from). *)
Ltac zesu_arith_context_solve_at base :=
  zesu_arith_context_prepare;
  try zesu_arith_root_ranges base;
  zesu_arith_bounds.
