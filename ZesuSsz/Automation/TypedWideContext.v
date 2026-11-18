Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Scratch candidate. No instance enables this switch by default. *)
Class ZesuStepTypedWideContext : Prop := {}.

Ltac2 Type zesu_wide_scan := [ WideAbsent | WidePresent | WideUnknown ].

(* Unknown dominates: a partially understood clause stays in the context. *)
Ltac2 zesu_wide_merge (first : zesu_wide_scan) (second : zesu_wide_scan) :=
  match first with
  | WideUnknown => WideUnknown
  | WideAbsent => second
  | WidePresent =>
      match second with
      | WideUnknown => WideUnknown
      | _ => WidePresent
      end
  end.

Ltac2 rec zesu_wide_positive_literal (term : constr) :=
  if Constr.equal term constr:(xH) then true else
  lazy_match! term with
  | xO ?tail => zesu_wide_positive_literal tail
  | xI ?tail => zesu_wide_positive_literal tail
  | _ => false
  end.

Ltac2 zesu_wide_width (width : constr) :=
  if Constr.equal width constr:(128%N) then WidePresent else
  if Constr.equal width constr:(0%N) then WideAbsent else
  lazy_match! width with
  | Npos ?value =>
      if zesu_wide_positive_literal value then WideAbsent else WideUnknown
  | _ => WideUnknown
  end.

(* Check the elaborated type. Never match a printed decimal token. *)
Ltac2 zesu_wide_node (term : constr) :=
  lazy_match! term with
  | bv ?width => zesu_wide_width width
  | _ =>
      let ty := Constr.type term in
      lazy_match! ty with
      | bv ?width => zesu_wide_width width
      | _ => WideAbsent
      end
  end.

(* Bound relatives, binders, eliminations, and unresolved terms refuse filtering.
   Inspect local definition bodies without unfolding arbitrary constants. *)
Ltac2 rec zesu_wide_visit (term : constr) :=
  if Constr.has_evar term then WideUnknown else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Var name =>
      let own := zesu_wide_node term in
      let alias := List.fold_left (fun found declaration =>
        let (other, body, _) := declaration in
        if Ident.equal name other then
          match body with
          | None => found
          | Some value => zesu_wide_merge found (zesu_wide_visit value)
          end
        else found) WideAbsent (Control.hyps ()) in
      zesu_wide_merge own alias
  | Constr.Unsafe.App head arguments =>
      let children := Array.fold_left (fun found argument =>
        zesu_wide_merge found (zesu_wide_visit argument))
        (zesu_wide_visit head) arguments in
      zesu_wide_merge (zesu_wide_node term) children
  | Constr.Unsafe.Cast body _ ty =>
      zesu_wide_merge (zesu_wide_visit body) (zesu_wide_visit ty)
  | Constr.Unsafe.Constant _ _ => zesu_wide_node term
  | Constr.Unsafe.Ind _ _ => zesu_wide_node term
  | Constr.Unsafe.Constructor _ _ => zesu_wide_node term
  | Constr.Unsafe.Sort _ => WideAbsent
  | Constr.Unsafe.Uint63 _ => WideAbsent
  | Constr.Unsafe.Float _ => WideAbsent
  | _ => WideUnknown
  end.

(* The candidate selects ordinary outer relations only. It does not inspect
   implication bodies, typeclass dictionaries, or spatial assertions. *)
Ltac2 zesu_wide_relation (ty : constr) :=
  lazy_match! ty with
  | @eq Z _ _ => true
  | @eq bool _ _ => true
  | @eq nat _ _ => true
  | @eq N _ _ => true
  | @eq (bv _) _ _ => true
  | Z.lt _ _ => true
  | Z.le _ _ => true
  | Nat.lt _ _ => true
  | Nat.le _ _ => true
  | N.lt _ _ => true
  | N.le _ _ => true
  | is_true _ => true
  | _ => false
  end.

Ltac2 zesu_wide_prune () :=
  match zesu_wide_visit (Control.goal ()) with
  | WideAbsent => ()
  | _ => Control.zero (Tactic_failure None)
  end;
  let cleared := { contents := false } in
  List.iter (fun declaration =>
    let (name, body, ty) := declaration in
    match body with
    | Some _ => ()
    | None =>
        if Constr.equal (Constr.type ty) constr:(Prop) then
          if zesu_wide_relation ty then
            match zesu_wide_visit ty with
            | WidePresent =>
                (* Kernel clear refuses a proof variable used by any declaration
                   or by the target. It never clears that dependent declaration. *)
                Control.plus (fun () => Std.clear [name]; cleared.(contents) := true)
                  (fun _ => ())
            | _ => ()
            end
          else ()
        else ()
    end) (List.rev (Control.hyps ()));
  if cleared.(contents) then () else Control.zero (Tactic_failure None).

Ltac zesu_typed_wide_prune := ltac2:(zesu_wide_prune ()).

(* solve requires complete closure. Backtracking restores all removed facts,
   evars, and goals before the original full-context closer runs. *)
Ltac zesu_typed_wide_filter closer :=
  tryif ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
      constr:(ZesuStepTypedWideContext)
  then first [solve [zesu_typed_wide_prune; closer] | closer]
  else closer.
