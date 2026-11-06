Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.VmClosed.
Require Import ZesuSsz.Automation.PureFacts.
From Ltac2 Require Import Ltac2.
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

Ltac zesu_stack_normalize_hypothesis hypothesis := once (
  repeat (
    let statement := type of hypothesis in
    match statement with
    | context[?term] =>
        lazymatch type of term with Z => progress (
          tryif zesu_stack_integer_literal term then fail 0 else idtac;
          zesu_stack_closed_term term;
          let reduced := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed term in
          change_no_check term with reduced in * ) end
    end)).

Ltac zesu_stack_arithmetic :=
  repeat first [progress zesu_split_folded_pure |
    match goal with H : _ /\ _ |- _ => destruct H end];
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      lazymatch statement with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | @eq Z _ _ => fail
      | _ => clear H
      end
  end;
  once (repeat match goal with
  | H : ?statement |- _ =>
      lazymatch statement with
      | Z.le _ _ => idtac
      | Z.lt _ _ => idtac
      | @eq Z _ _ => idtac
      end;
      progress (zesu_stack_normalize_hypothesis H)
  end);
  once (repeat match goal with
  | |- context[?term] =>
      lazymatch type of term with Z => progress (
        zesu_stack_closed_term term;
        let reduced := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed term in
        change_no_check term with reduced) end
  end);
  bv_solve.

Ltac zesu_stack_integer_address pointer :=
  lazymatch pointer with
  | bv_add (bv_add (Z_to_bv 64 ?base) ?first) ?second =>
      let left := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_signed first) in
      let right := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_signed second) in
      constr:((base + left + right)%Z)
  | bv_add (Z_to_bv 64 ?base) ?offset =>
      let displacement := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_signed offset) in
      constr:((base + displacement)%Z)
  | bv_sub (Z_to_bv 64 ?base) ?offset =>
      let displacement := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed (bv_unsigned offset) in
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
  ZesuSsz.Automation.PureFacts.zesu_integer_array_facts.

Ltac zesu_handoff_closed_Z term continuation :=
  tryif zesu_handoff_closed_term term then
    let reduced := ZesuSsz.Automation.VmClosed.zesu_vm_eval_closed term in continuation reduced
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
