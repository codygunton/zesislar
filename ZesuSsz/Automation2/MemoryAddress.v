Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.RangeFacts.
Require Import ZesuSsz.Automation2.SearchBudget.
From Ltac2 Require Import Ltac2 Ref List Int Array.
Local Open Scope Z_scope.
Set Default Proof Mode "Classic".

Ltac zesu_handoff_closed_term term :=
  tryif is_var term then fail 0 else
  tryif has_evar term then fail 0 else
  lazymatch term with
  | (fun _ => _) => fail 0
  | (forall _, _) => fail 0
  | (let _ := _ in _) => fail 0
  | ?function ?argument =>
      zesu_handoff_closed_term function; zesu_handoff_closed_term argument
  | _ => idtac
  end.

Ltac zesu_stack_closed_fallback recurse current :=
  let rec visit current :=
    tryif is_var current then
      let body := eval unfold current in current in
      recurse body
    else lazymatch current with
    | (fun _ => _) => fail 0
    | (forall _, _) => fail 0
    | ?function ?argument => visit function; visit argument
    | _ => idtac
    end
  in visit current.

Ltac2 rec zesu_stack_closed_visit (term : constr) (fallback : Ltac1.t) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      zesu_stack_closed_visit head fallback;
      Array.iter (fun argument => zesu_stack_closed_visit argument fallback) arguments
  | Constr.Unsafe.Constant _ _ => ()
  | Constr.Unsafe.Constructor _ _ => ()
  | Constr.Unsafe.Ind _ _ => ()
  | Constr.Unsafe.Sort _ => ()
  | _ => Ltac1.apply fallback [Ltac1.of_constr term] Ltac1.run
  end.

Ltac zesu_stack_closed_term term :=
  tryif has_evar term then fail 0 else
  let expanded := eval cbv beta zeta in term in
  let check := ltac2:(value fallback |-
    zesu_stack_closed_visit (Option.get (Ltac1.to_constr value)) fallback) in
  check expanded ltac:(fun current =>
    zesu_stack_closed_fallback zesu_stack_closed_term current).

Ltac2 rec zesu_stack_positive_literal_term (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => Constr.equal term constr:(BinNums.xH)
  | Constr.Unsafe.App head arguments =>
      if Bool.and (Constr.is_constructor head) (Int.equal (Array.length arguments) 1)
      then zesu_stack_positive_literal_term (Array.get arguments 0)
      else false
  | _ => false
  end.

Ltac2 zesu_stack_integer_literal_term (term : constr) :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Constructor _ _ => Constr.equal term constr:(BinNums.Z0)
  | Constr.Unsafe.App head arguments =>
      if Bool.and (Int.equal (Array.length arguments) 1)
          (Bool.or (Constr.equal head constr:(BinNums.Zpos))
                   (Constr.equal head constr:(BinNums.Zneg)))
      then zesu_stack_positive_literal_term (Array.get arguments 0)
      else false
  | _ => false
  end.

Ltac zesu_stack_integer_literal term :=
  let check := ltac2:(value |-
    if zesu_stack_integer_literal_term (Option.get (Ltac1.to_constr value))
    then () else Control.zero (Tactic_failure None)) in
  check term.

Ltac zesu_stack_normalize_hypothesis_steps hypothesis visits rewrites := once (
  repeat (
    let statement := type of hypothesis in
    match statement with
    | context[?term] =>
        let _ := visits constr:(tt) in
        lazymatch type of term with Z => progress (
          tryif zesu_stack_integer_literal term then fail 0 else idtac;
          zesu_stack_closed_term term;
          let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term in
          let _ := rewrites constr:(tt) in
          change_no_check term with reduced in * ) end
    end)).

Ltac2 zesu_stack_hypothesis_ident value :=
  match Ltac1.to_ident value with
  | Some name => name
  | None =>
      match Ltac1.to_constr value with
      | Some term =>
          match Constr.Unsafe.kind term with
          | Constr.Unsafe.Var name => name
          | _ => Control.zero (Tactic_failure None)
          end
      | None => Control.zero (Tactic_failure None)
      end
  end.

Ltac2 zesu_stack_normalize_hypothesis_bounded failed hypothesis :=
  Ltac1.apply
    (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_normalize_hypothesis_steps])
    [Ltac1.of_ident hypothesis;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 32768;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 64] Ltac1.run;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_check failed.

Ltac zesu_stack_normalize_hypothesis hypothesis :=
  let run := ltac2:(h |-
    zesu_stack_normalize_hypothesis_bounded (Ref.ref false)
      (zesu_stack_hypothesis_ident h)) in
  run hypothesis.

Ltac zesu_stack_split_pure_steps visits unfolds check :=
  repeat match goal with
  | H : ?T |- _ =>
      let _ := visits constr:(tt) in
      lazymatch type of T with Prop => idtac end;
      lazymatch T with
      | _ /\ _ => fail
      | _ =>
          let _ := unfolds constr:(tt) in
          let unfolded := eval hnf in T in
          lazymatch unfolded with
          | _ /\ _ =>
              let _ := visits constr:(tt) in
              change unfolded in H; destruct H
          end
      end
  end;
  let _ := check constr:(tt) in idtac.

Ltac2 zesu_stack_split_pure_bounded failed :=
  Ltac1.apply
    (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_split_pure_steps])
    [ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 2048;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 1024;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_checker failed] Ltac1.run.

Ltac zesu_stack_keep_atom atom hypothesis :=
  assert_fails ltac:(ZesuSsz.Automation2.VmClosed.zesu_vm_closed atom);
  let T := type of hypothesis in
  lazymatch type of T with Prop =>
    lazymatch T with context[atom] =>
      let selected := fresh "HrangeFact" in pose proof hypothesis as selected
    end
  end.

Ltac2 zesu_stack_composite_arithmetic term :=
  lazy_match! term with
  | Z.add _ _ => true | Z.sub _ _ => true | Z.mul _ _ => true
  | Z.opp _ => true | Z.div _ _ => true | Z.modulo _ _ => true
  | Z.land _ _ => true | Z.lor _ _ => true | Z.shiftl _ _ => true
  | Z.shiftr _ _ => true
  | _ => false
  end.

(* Select from the flattened arithmetic context. The second pass retains one
   layer of summand facts, matching the shared range collector. *)
Ltac2 zesu_stack_isolate_goal () :=
  let failed := Ref.ref false in
  let remaining := Ref.ref 1024 in
  let atoms := Ref.ref [] in
  let rec visit term :=
    ZesuSsz.Automation2.SearchBudget.zesu_budget_take failed remaining;
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Rel _ => ()
    | _ =>
        let typ := Constr.type term in
        if Bool.or (Constr.equal typ constr:(Z)) (Constr.equal typ constr:(nat)) then
          if zesu_stack_composite_arithmetic term then () else
          let closed := Control.plus (fun () =>
            Ltac1.apply
              (Ltac1.ref [@ZesuSsz; @Automation2; @VmClosed; @zesu_vm_closed])
              [Ltac1.of_constr term] Ltac1.run; true) (fun _ => false) in
          if closed then () else
            if List.exist (Constr.equal term) (Ref.get atoms) then ()
            else Ref.set atoms (term :: Ref.get atoms)
        else ()
    end;
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.App head args => visit head; Array.iter visit args
    | Constr.Unsafe.Cast value _ _ => visit value
    | Constr.Unsafe.Proj _ _ value => visit value
    | _ => ()
    end in
  visit (Control.goal ());
  let original := Control.hyps () in
  let visits := Ref.ref 16384 in
  let keep atom h :=
    ZesuSsz.Automation2.SearchBudget.zesu_budget_take failed visits;
    let (name, _, _) := h in
    Control.plus (fun () =>
      Ltac1.apply
        (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_keep_atom])
        [Ltac1.of_constr atom; Ltac1.of_constr (Control.hyp name)] Ltac1.run)
      (fun _ => ()) in
  List.iter (fun atom => List.iter (keep atom) original) (Ref.get atoms);
  let selected := Control.hyps () in
  List.iter (fun h =>
    let (name, _, typ) := h in
    if ZesuSsz.Automation2.RangeFacts.zesu_name_prefix (Ident.to_string name) "HrangeFact" 0 then
      List.iter (fun atom => List.iter (keep atom) original)
        (ZesuSsz.Automation2.RangeFacts.zesu_range_atoms typ)
    else ()) selected;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_check failed;
  ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ().

Ltac zesu_stack_arithmetic_steps outer split_pure prune_visits clears
    hyp_visits normalize_hyp check :=
  repeat (let _ := outer constr:(tt) in
    first [progress (let _ := split_pure constr:(tt) in idtac) |
      match goal with H : _ /\ _ |- _ => destruct H end];
    let _ := check constr:(tt) in idtac);
  let _ := check constr:(tt) in
  repeat match goal with
  | H : ?statement |- _ =>
      let _ := prune_visits constr:(tt) in
      lazymatch type of statement with Prop => idtac end;
      lazymatch statement with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | @eq Z _ _ => fail
      | _ => let _ := clears constr:(tt) in clear H
      end
  end;
  let _ := check constr:(tt) in
  once (repeat match goal with
  | H : ?statement |- _ =>
      let _ := hyp_visits constr:(tt) in
      lazymatch statement with
      | Z.le _ _ => idtac
      | Z.lt _ _ => idtac
      | @eq Z _ _ => idtac
      end;
      progress (let _ := normalize_hyp H in idtac)
  end);
  let _ := check constr:(tt) in
  ZesuSsz.Automation2.SearchBudget.zesu_normalize_closed_goal;
  ltac2:(zesu_stack_isolate_goal ());
  ZesuSsz.Automation2.SearchBudget.zesu_check_atomic_input;
  bv_solve.

Ltac2 zesu_stack_arithmetic_bounded () :=
  let failed := Ref.ref false in
  let split_tactic := Ltac1.lambda (fun _ =>
    zesu_stack_split_pure_bounded failed; Ltac1.of_constr constr:(tt)) in
  let normalize := Ltac1.lambda (fun h =>
    zesu_stack_normalize_hypothesis_bounded failed (zesu_stack_hypothesis_ident h);
    Ltac1.of_constr constr:(tt)) in
  Ltac1.apply
    (Ltac1.ref [@ZesuSsz; @Automation2; @MemoryAddress; @zesu_stack_arithmetic_steps])
    [ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 64;
     split_tactic;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 16384;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 128;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_tick failed 2048;
     normalize;
     ZesuSsz.Automation2.SearchBudget.zesu_budget_checker failed] Ltac1.run;
  ZesuSsz.Automation2.SearchBudget.zesu_budget_check failed.

Ltac zesu_stack_arithmetic := ltac2:(zesu_stack_arithmetic_bounded ()).

Ltac zesu_stack_integer_address pointer :=
  lazymatch pointer with
  | bv_add (bv_add (Z_to_bv 64 ?base) ?first) ?second =>
      let left := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_signed first) in
      let right := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_signed second) in
      constr:((base + left + right)%Z)
  | bv_add (Z_to_bv 64 ?base) ?offset =>
      let displacement := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_signed offset) in
      constr:((base + displacement)%Z)
  | bv_sub (Z_to_bv 64 ?base) ?offset =>
      let displacement := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_unsigned offset) in
      constr:((base - displacement)%Z)
  | Z_to_bv 64 ?base => constr:(base)
  end.

Ltac zesu_integer_pointer_root pointer continuation :=
  lazymatch pointer with
  | bv_add ?base ?offset =>
      zesu_handoff_closed_term offset; zesu_integer_pointer_root base continuation
  | bv_sub ?base ?offset =>
      zesu_handoff_closed_term offset; zesu_integer_pointer_root base continuation
  | Z_to_bv 64 ?base => continuation base
  end.

Ltac zesu_array_bound_integer_casts :=
  repeat match goal with
  | |- context[bv_unsigned (Z_to_bv 64 ?pointer)] =>
      let Hcast := fresh "HarrayBoundCast" in
      assert (Hcast : bv_unsigned (Z_to_bv 64 pointer) = pointer)
        by zesu_stack_arithmetic;
      rewrite Hcast; clear Hcast
  end.

Ltac zesu_integer_array_facts :=
  ZesuSsz.Automation2.PureFacts.zesu_integer_array_facts.

Ltac zesu_handoff_closed_Z term continuation :=
  tryif zesu_handoff_closed_term term then
    let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term in continuation reduced
  else lazymatch term with
  | Z.add ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.add left right) in continuation reduced))
  | Z.sub ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.sub left right) in continuation reduced))
  | Z.mul ?left ?right =>
      zesu_handoff_closed_Z left ltac:(fun left =>
        zesu_handoff_closed_Z right ltac:(fun right =>
          let reduced := constr:(Z.mul left right) in continuation reduced))
  | Z.opp ?value =>
      zesu_handoff_closed_Z value ltac:(fun value =>
        let reduced := constr:(Z.opp value) in continuation reduced)
  | _ => continuation term
  end.
