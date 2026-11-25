Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.ResidualExport.
From Coq Require Import ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* A match on an inductive other than `bool`/`sumbool` is written as
   `(match s as x return P with | @C _ a => t .. end)`: constructors by
   their full path, parameters as `_`, one branch per constructor. The
   printed text reparses to the same term, and the round-trip entry point
   (`zesu_export_roundtrip`, which tools/oblig/normalise.py and
   tools/block/residual_loop.py run on the reparsed statement) prints the
   same text again. A match the syntax cannot express is refused. *)

Inductive export_match_kind := export_match_ok | export_match_oom.

Inductive export_match_three :=
| export_match_none
| export_match_one (z : Z)
| export_match_two (z : Z) (b : bool).

Ltac2 export_text (term : constr) := Message.to_string (zesu_export_source term).

(* ORIGINAL prints as TEXT; REPARSED (TEXT read back as source) is the same
   term and prints as TEXT again. *)
Ltac2 expect_source (original : constr) (reparsed : constr) (text : string) :=
  let shown := export_text original in
  if String.equal shown text then () else
    (Message.print (Message.of_string shown); Control.throw (Tactic_failure None));
  if Constr.equal original reparsed then () else Control.throw (Tactic_failure None);
  if String.equal (export_text reparsed) text then () else Control.throw (Tactic_failure None).

Ltac2 expect_refused (term : constr) (why : string) :=
  match Control.case (fun () => export_text term) with
  | Val _ => Control.throw (Tactic_failure None)
  | Err (ZesuExportRefused reason) =>
      if String.equal reason why then () else
        (Message.print (Message.of_string reason); Control.throw (Tactic_failure None))
  | Err _ => Control.throw (Tactic_failure None)
  end.

(* (a) An enumeration: constructors without arguments. *)
Ltac2 Eval expect_source
  constr:(forall (k : export_match_kind) (x y : Z),
    match k with export_match_ok => x | export_match_oom => y end = x)
  constr:((forall (k : (@ZesuSsz.Proofs.Tests.ExportMatch.export_match_kind)), (forall (x : (@Coq.Numbers.BinNums.Z)), (forall (y : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (match k as k_1 return (@Coq.Numbers.BinNums.Z) with | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_ok => x | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_oom => y end) x)))))
  "(forall (k : (@ZesuSsz.Proofs.Tests.ExportMatch.export_match_kind)), (forall (x : (@Coq.Numbers.BinNums.Z)), (forall (y : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (match k as k_1 return (@Coq.Numbers.BinNums.Z) with | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_ok => x | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_oom => y end) x))))".

(* (b) `option Z`: the parameter is `_`; the argument keeps its name. *)
Ltac2 Eval expect_source
  constr:(forall o : option Z, 0 <= match o with Some v => v | None => 0 end)
  constr:((forall (o : (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z))), (@Coq.ZArith.BinInt.Z.le (0)%Z (match o as o_1 return (@Coq.Numbers.BinNums.Z) with | @Coq.Init.Datatypes.Some _ v => v | @Coq.Init.Datatypes.None _ => (0)%Z end))))
  "(forall (o : (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z))), (@Coq.ZArith.BinInt.Z.le (0)%Z (match o as o_1 return (@Coq.Numbers.BinNums.Z) with | @Coq.Init.Datatypes.Some _ v => v | @Coq.Init.Datatypes.None _ => (0)%Z end)))".

(* (c) Three constructors with zero, one and two arguments; a branch
   argument that an outer binder names gets a fresh name. *)
Ltac2 Eval expect_source
  constr:(forall (t : export_match_three) (z : Z),
    match t with
    | export_match_none => True
    | export_match_one z => z = 0
    | export_match_two w b => (if b then w else z) = 0
    end)
  constr:((forall (t : (@ZesuSsz.Proofs.Tests.ExportMatch.export_match_three)), (forall (z : (@Coq.Numbers.BinNums.Z)), (match t as t_1 return Prop with | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_none => (@Coq.Init.Logic.True) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_one z_1 => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) z_1 (0)%Z) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_two w b => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if b as b_1 return (@Coq.Numbers.BinNums.Z) then w else z) (0)%Z) end))))
  "(forall (t : (@ZesuSsz.Proofs.Tests.ExportMatch.export_match_three)), (forall (z : (@Coq.Numbers.BinNums.Z)), (match t as t_1 return Prop with | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_none => (@Coq.Init.Logic.True) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_one z_1 => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) z_1 (0)%Z) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_two w b => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if b as b_1 return (@Coq.Numbers.BinNums.Z) then w else z) (0)%Z) end)))".

(* A return predicate that uses the matched term is written with `as`; a
   branch whose body is a function keeps it (the None branch binds nothing). *)
Ltac2 Eval expect_source
  constr:(forall o : option Z,
    match o as p return p = o -> Prop with Some v => fun _ => v = 0 | None => fun _ => True end eq_refl)
  constr:((forall (o : (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z))), ((match o as p return ((@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) p o) -> Prop) with | @Coq.Init.Datatypes.Some _ v => (fun (x_1 : (@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) (@Coq.Init.Datatypes.Some (@Coq.Numbers.BinNums.Z) v) o)) => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) v (0)%Z)) | @Coq.Init.Datatypes.None _ => (fun (x_1 : (@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) (@Coq.Init.Datatypes.None (@Coq.Numbers.BinNums.Z)) o)) => (@Coq.Init.Logic.True)) end) (@Coq.Init.Logic.eq_refl (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) o))))
  "(forall (o : (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z))), ((match o as p return ((@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) p o) -> Prop) with | @Coq.Init.Datatypes.Some _ v => (fun (x_1 : (@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) (@Coq.Init.Datatypes.Some (@Coq.Numbers.BinNums.Z) v) o)) => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) v (0)%Z)) | @Coq.Init.Datatypes.None _ => (fun (x_1 : (@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) (@Coq.Init.Datatypes.None (@Coq.Numbers.BinNums.Z)) o)) => (@Coq.Init.Logic.True)) end) (@Coq.Init.Logic.eq_refl (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) o)))".

(* The round-trip entry point on a statement read back from printed source:
   it prints that source again (a wildcard argument is printed with the name
   elaboration gave its binder). *)
Goal (forall (t : (@ZesuSsz.Proofs.Tests.ExportMatch.export_match_three)), (forall (o : (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z))), (match t as t_1 return Prop with | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_none => (@Coq.Init.Logic.True) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_one z => (@Coq.Init.Logic.eq (@Coq.Init.Datatypes.option (@Coq.Numbers.BinNums.Z)) (@Coq.Init.Datatypes.Some (@Coq.Numbers.BinNums.Z) z) o) | @ZesuSsz.Proofs.Tests.ExportMatch.export_match_two z b => (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) z (0)%Z) end))).
Proof.
  ltac2:(
    let original := constr:(forall (t : export_match_three) (o : option Z),
      match t with
      | export_match_none => True
      | export_match_one z => Some z = o
      | export_match_two z _ => z = 0
      end) in
    let text := export_text original in
    if String.equal (export_text (Control.goal ())) text then () else Control.throw (Tactic_failure None);
    zesu_export_roundtrip ()).
Abort.

(* A pattern variable that would read as a constructor gets a fresh name. *)
Ltac2 Eval
  match Constr.Unsafe.kind constr:(fun (S : Z) (v : Z) => S) with
  | Constr.Unsafe.Lambda first inner =>
      if String.equal (zesu_export_pattern_name first []) "S_1" then () else Control.throw (Tactic_failure None);
      match Constr.Unsafe.kind inner with
      | Constr.Unsafe.Lambda second _ =>
          if String.equal (zesu_export_pattern_name second []) "v" then () else Control.throw (Tactic_failure None)
      | _ => Control.throw (Tactic_failure None)
      end
  | _ => Control.throw (Tactic_failure None)
  end.

(* (d) A match on an indexed family (an `in` clause; here the return
   predicate depends on the index) is refused. *)
Ltac2 Eval expect_refused
  constr:(forall (x y : Z) (e : x = y),
    match e in _ = w return w = x -> Prop with eq_refl => fun _ => True end (eq_sym e))
  "match".

(* A `bool` match keeps its `if` form (ResidualExport.v tests `sumbool`). *)
Ltac2 Eval expect_source
  constr:(forall b : bool, match b with true => True | false => False end)
  constr:((forall (b : (@Coq.Init.Datatypes.bool)), (if b as b_1 return Prop then (@Coq.Init.Logic.True) else (@Coq.Init.Logic.False))))
  "(forall (b : (@Coq.Init.Datatypes.bool)), (if b as b_1 return Prop then (@Coq.Init.Logic.True) else (@Coq.Init.Logic.False)))".
