Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Automation2.ResidualExportOn.
Require Import ZesuSsz.Automation2.ResidualExport.
From Coq Require Import ZArith.ZArith Lia.
Require Import stdpp.bitvector.definitions.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* The exporter writes source that reparses to the same term. Each case
   states the expected text twice: as a string (the printed source) and as
   source (the reparsed term must equal the original term). *)
Ltac2 export_text (term : constr) := Message.to_string (zesu_export_source term).

Ltac2 expect_source (original : constr) (reparsed : constr) (text : string) :=
  let shown := export_text original in
  if String.equal shown text then () else
    (Message.print (Message.of_string shown); Control.throw (Tactic_failure None));
  if Constr.equal original reparsed then () else Control.throw (Tactic_failure None).

(* Widths stay explicit: the default printer shows `bv_unsigned 4` here. *)
Ltac2 Eval expect_source
  constr:(forall x : bv 64, bv_unsigned (bv_zero_extend 128 x) < bv_unsigned (Z_to_bv 64 4))
  constr:((forall (x : (@stdpp.bitvector.definitions.bv (64)%N)), (@Coq.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (128)%N (@stdpp.bitvector.definitions.bv_zero_extend (64)%N (128)%N x)) (@stdpp.bitvector.definitions.bv_unsigned (64)%N (@stdpp.bitvector.definitions.Z_to_bv (64)%N (4)%Z)))))
  "(forall (x : (@stdpp.bitvector.definitions.bv (64)%N)), (@Coq.ZArith.BinInt.Z.lt (@stdpp.bitvector.definitions.bv_unsigned (128)%N (@stdpp.bitvector.definitions.bv_zero_extend (64)%N (128)%N x)) (@stdpp.bitvector.definitions.bv_unsigned (64)%N (@stdpp.bitvector.definitions.Z_to_bv (64)%N (4)%Z))))".

(* Literals: hexadecimal above 30 bits, negative Z through its constructor,
   nat numerals. *)
Ltac2 Eval expect_source
  constr:(18446744073709551600 + (-3) = Z.of_nat 40)
  constr:((@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (@Coq.ZArith.BinInt.Z.add (0xfffffffffffffff0)%Z (@Coq.Numbers.BinNums.Zneg (3)%positive)) (@Coq.ZArith.BinInt.Z.of_nat (40)%nat)))
  "(@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (@Coq.ZArith.BinInt.Z.add (0xfffffffffffffff0)%Z (@Coq.Numbers.BinNums.Zneg (3)%positive)) (@Coq.ZArith.BinInt.Z.of_nat (40)%nat))".

(* An inner binder that an outer binder already names gets a fresh name;
   an anonymous product whose body does not use its binder is an arrow. *)
Ltac2 Eval expect_source
  constr:(forall x : Z, (forall x : Z, x = x) -> x = x)
  constr:((forall (x : (@Coq.Numbers.BinNums.Z)), ((forall (x_1 : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x_1 x_1)) -> (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x x))))
  "(forall (x : (@Coq.Numbers.BinNums.Z)), ((forall (x_1 : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x_1 x_1)) -> (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x x)))".

(* The occurrence check that the arrow and the minimization use. *)
Ltac2 Eval
  let body (term : constr) := match Constr.Unsafe.kind term with
    | Constr.Unsafe.Lambda _ inner => inner
    | _ => Control.throw (Tactic_failure None)
    end in
  if zesu_export_occurs 1 (body constr:(fun x : nat => x)) then () else Control.throw (Tactic_failure None);
  if zesu_export_occurs 1 (body constr:(fun x : nat => 0)) then Control.throw (Tactic_failure None) else ().

(* An `if` on `bool` or on `sumbool` (`decide`) is printed as an `if` with
   its return predicate; the text reparses to the same match. *)
Ltac2 Eval expect_source
  constr:(forall b : bool, (if b then 1 else 0) = 0)
  constr:((forall (b : (@Coq.Init.Datatypes.bool)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if b as b_1 return (@Coq.Numbers.BinNums.Z) then (1)%Z else (0)%Z) (0)%Z)))
  "(forall (b : (@Coq.Init.Datatypes.bool)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if b as b_1 return (@Coq.Numbers.BinNums.Z) then (1)%Z else (0)%Z) (0)%Z))".
Ltac2 Eval expect_source
  constr:(forall x : Z, (if Z.eq_dec x 0 then 1 else x) = x)
  constr:((forall (x : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if (@stdpp.numbers.Z.eq_dec x (0)%Z) as x_1 return (@Coq.Numbers.BinNums.Z) then (1)%Z else x) x)))
  "(forall (x : (@Coq.Numbers.BinNums.Z)), (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) (if (@stdpp.numbers.Z.eq_dec x (0)%Z) as x_1 return (@Coq.Numbers.BinNums.Z) then (1)%Z else x) x))".
Ltac2 Eval expect_source
  constr:(forall b : bool, match b with true => True | false => False end)
  constr:((forall (b : (@Coq.Init.Datatypes.bool)), (if b as b_1 return Prop then (@Coq.Init.Logic.True) else (@Coq.Init.Logic.False))))
  "(forall (b : (@Coq.Init.Datatypes.bool)), (if b as b_1 return Prop then (@Coq.Init.Logic.True) else (@Coq.Init.Logic.False)))".

(* A `sumbool` branch that uses the constructor's argument, and a match on
   any other inductive, are printed as a `match` (ExportMatch.v). *)
Ltac2 Eval expect_source
  constr:(forall x : Z, match Z.eq_dec x 0 with left h => h = h | right _ => True end)
  constr:((forall (x : (@Coq.Numbers.BinNums.Z)), (match (@stdpp.numbers.Z.eq_dec x (0)%Z) as x_1 return Prop with | @Coq.Init.Specif.left _ _ h => (@Coq.Init.Logic.eq (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x (0)%Z) h h) | @Coq.Init.Specif.right _ _ n => (@Coq.Init.Logic.True) end)))
  "(forall (x : (@Coq.Numbers.BinNums.Z)), (match (@stdpp.numbers.Z.eq_dec x (0)%Z) as x_1 return Prop with | @Coq.Init.Specif.left _ _ h => (@Coq.Init.Logic.eq (@Coq.Init.Logic.eq (@Coq.Numbers.BinNums.Z) x (0)%Z) h h) | @Coq.Init.Specif.right _ _ n => (@Coq.Init.Logic.True) end))".
Ltac2 Eval expect_source
  constr:(forall n : nat, match n with O => True | S _ => False end)
  constr:((forall (n : (@Coq.Init.Datatypes.nat)), (match n as n_1 return Prop with | @Coq.Init.Datatypes.O => (@Coq.Init.Logic.True) | @Coq.Init.Datatypes.S n0 => (@Coq.Init.Logic.False) end)))
  "(forall (n : (@Coq.Init.Datatypes.nat)), (match n as n_1 return Prop with | @Coq.Init.Datatypes.O => (@Coq.Init.Logic.True) | @Coq.Init.Datatypes.S n0 => (@Coq.Init.Logic.False) end))".

(* The statement of a goal: the facts that the conclusion reaches (through
   shared local variables), the variables they mention, and local
   definitions unfolded. A fact about an unrelated variable, and a fact with
   no local variable, stay out. *)
Ltac2 rec same_names (found : ident list) (expected : ident list) :=
  match found with
  | [] => match expected with [] => true | _ => false end
  | x :: xs => match expected with [] => false | y :: ys => Bool.and (Ident.equal x y) (same_names xs ys) end
  end.

Lemma residual_export_statement (args y : Z) (w : bv 64) (Hdom : 0 <= args) (Hy : y = 3)
    (Hlink : args <= y + 10) (Hw : bv_unsigned w = 0) (Hmarker : True) :
  let L := args + 1 in 0 < L.
Proof.
  intros L.
  ltac2:(
    let (facts, _, _) := zesu_export_reach 2048 in
    if same_names facts [@Hdom; @Hy; @Hlink] then () else Control.throw (Tactic_failure None);
    let (statement, binders) := zesu_export_statement facts in
    if same_names binders [@args; @y; @Hdom; @Hy; @Hlink] then () else Control.throw (Tactic_failure None);
    if Constr.equal statement
      constr:(forall (args y : Z) (Hdom : 0 <= args) (Hy : y = 3) (Hlink : args <= y + 10), 0 < args + 1)
    then () else Control.throw (Tactic_failure None);
    if same_names (zesu_export_conclusion_definitions ()) [@L] then () else Control.throw (Tactic_failure None)).
  (* The exported statement closes the goal by `exact`. *)
  assert (Hstatement : forall (args y : Z) (Hdom : 0 <= args) (Hy : y = 3) (Hlink : args <= y + 10),
    0 < args + 1) by (intros; lia).
  exact (Hstatement args y Hdom Hy Hlink).
Qed.

(* A fact the conclusion reaches but above the node limit is reported as
   dropped (name, node count, head); a large fact over unrelated variables is
   not, and neither is a kept fact. *)
Lemma residual_export_dropped (x y z w : Z) (Hsmall : 0 <= x)
    (Hbig : x + y + z + x + y + z = z /\ y = z) (Hw : w + w + w + w + w + w = w) :
  x <= x + 1.
Proof.
  ltac2:(
    let (facts, _, _) := zesu_export_reach 10 in
    if same_names facts [@Hsmall] then () else Control.throw (Tactic_failure None);
    let dropped := zesu_export_dropped 10 facts in
    if same_names (List.map (fun entry => let (name, _, _) := entry in name) dropped) [@Hbig]
    then () else Control.throw (Tactic_failure None);
    List.iter (fun entry =>
      let (_, nodes, shown) := entry in
      if Int.lt 10 nodes then () else Control.throw (Tactic_failure None);
      if String.equal (Message.to_string shown) "(@Coq.Init.Logic.and)" then ()
      else (Message.print shown; Control.throw (Tactic_failure None))) dropped;
    (* Under the default limit nothing is dropped. *)
    let (all, _, _) := zesu_export_reach 2048 in
    if Int.equal (List.length (zesu_export_dropped 2048 all)) 0 then () else Control.throw (Tactic_failure None)).
  lia.
Qed.

(* A record fact (a head of its own) above the node limit. *)
Definition residual_export_record (a b : Z) : Prop := a = b + b.

(* Kept whole when the conclusion mentions its head: the conclusion restates
   the record. *)
Lemma residual_export_keep_whole (x y : Z)
    (Hrec : residual_export_record (x + y + x + y + x + y) y) :
  residual_export_record (x + y + x + y + x + y) y.
Proof.
  ltac2:(
    let (facts, _, _) := zesu_export_reach 10 in
    if same_names facts [@Hrec] then () else Control.throw (Tactic_failure None)).
  exact Hrec.
Qed.

(* Abstracted when the scope mentions its head and the conclusion does not:
   its large subterm (at least `zesu_export_abstract_nodes` nodes) becomes a
   variable in every fact, the record fits the limit and the statement
   keeps it. *)
Lemma residual_export_abstract (x y : Z)
    (Hrec : residual_export_record
      (x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x +
       y * y * y * y * y * y * y * y * y * y * y * y * y * y * y * y) y)
    (Hlow : 0 <=
      x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x +
      y * y * y * y * y * y * y * y * y * y * y * y * y * y * y * y) :
  0 <= y + y.
Proof.
  ltac2:(
    zesu_export_abstract 10 constr:(residual_export_record 0 0);
    let typ := Constr.type (Control.hyp @Hrec) in
    if ZesuSsz.Automation2.ContextCollection.zesu_select_small 10 typ then ()
    else Control.throw (Tactic_failure None);
    if zesu_export_mentions (Control.hyp @x) typ then Control.throw (Tactic_failure None) else ();
    if zesu_export_mentions (Control.hyp @x) (Constr.type (Control.hyp @Hlow))
    then Control.throw (Tactic_failure None) else ();
    let (facts, _, _) := zesu_export_reach 10 in
    if same_names facts [@Hrec; @Hlow] then () else Control.throw (Tactic_failure None)).
  unfold residual_export_record in Hrec. lia.
Qed.

(* Minimization keeps the facts whose binders the proof uses. *)
Definition residual_export_proof :
  forall (x y : Z) (Hx : 0 <= x) (Hy : 0 <= y), 0 <= x + 0 :=
  fun x y Hx Hy => eq_ind_r (fun v => 0 <= v) Hx (Z.add_0_r x).

Goal forall (x y : Z) (Hx : 0 <= x) (Hy : 0 <= y), 0 <= x + 0.
Proof.
  intros.
  ltac2:(
    let used := zesu_export_used_facts (Std.ConstRef (match Constr.Unsafe.kind constr:(@residual_export_proof) with
      | Constr.Unsafe.Constant c _ => c
      | _ => Control.throw (Tactic_failure None)
      end)) in
    if same_names used [@Hx] then () else Control.throw (Tactic_failure None);
    let (statement, _) := zesu_export_statement used in
    if Constr.equal statement constr:(forall (x : Z) (Hx : 0 <= x), 0 <= x + 0)
    then () else Control.throw (Tactic_failure None)).
  lia.
Qed.

(* With the switch on, the hooks print and never change the goal or the
   context; a spatial goal gets a skip line. *)
Ltac2 prop_count () :=
  List.length (List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => Constr.equal (Constr.type typ) constr:(Prop)
    | Some _ => false
    end) (Control.hyps ())).

Lemma residual_export_hooks (x : Z) (Hx : 0 <= x < 10) (Hy : 0 < 1) : x + 1 <= 11.
Proof.
  zesu_diag_export_on.
  zesu_diag_export_split;
  zesu_diag_export_final fail.
  match goal with |- x + 1 <= 11 => idtac end.
  ltac2:(if Int.equal (prop_count ()) 2 then () else Control.throw (Tactic_failure None)).
  lia.
Qed.
