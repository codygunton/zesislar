(** Named equations: values the generator gave a name to.

    A call boundary keeps a register's value under a name with
    [zesu_named_eq name value] (ZesuSsz.Contracts.NamedEquation). Lithium's
    [subst] cannot remove the name, so later facts mention the name and not
    the whole value. These steps use the value only where a goal needs it. *)
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Export ZesuSsz.Contracts.NamedEquation.
Require ZesuSsz.Automation2.ResourceGroups.
From lithium Require Import interpreter.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Section zesu_named_equation.
  Context {Σ : gFunctors}.
  Lemma zesu_tac_sep_named_eq Δ {A : Type} (name value : A) (Q : iProp Σ) :
    envs_entails Δ (⌜name = value⌝ ∗ Q) → envs_entails Δ (⌜zesu_named_eq name value⌝ ∗ Q).
  Proof.
    rewrite envs_entails_unseal => ->. iIntros "[%equality $]". iPureIntro.
    by apply zesu_named_eq_iff.
  Qed.

  Lemma zesu_tac_sep_exist_witness Δ {A : Type} (value : A) (P : A → iProp Σ) (Q : iProp Σ) :
    envs_entails Δ (P value ∗ Q) → envs_entails Δ ((∃ y, P y) ∗ Q).
  Proof. rewrite envs_entails_unseal => ->. iIntros "[? $]". by iExists value. Qed.

  Lemma zesu_tac_li_ex_sep_exist_witness Δ {A B C : Type} (value : C)
      (P : A *ₗ B → C → iProp Σ) (Q : A *ₗ B → iProp Σ) :
    envs_entails Δ (∃ₗ x, P x value ∗ Q x) → envs_entails Δ (∃ₗ x, (∃ y, P x y) ∗ Q x).
  Proof.
    rewrite envs_entails_unseal => ->. apply bi.exist_mono => x.
    iIntros "[? $]". by iExists value.
  Qed.
End zesu_named_equation.

(* A named equation the block must establish: a hypothesis with the same
   name and value closes it (instantiating the successor's binders with the
   block's names); otherwise it is an ordinary equation. *)
Ltac zesu_named_equation_goal :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (zesu_named_eq _ _)) _) =>
      first [notypeclasses refine (tac_sep_pure _ _ _ _ _); [solve [eassumption] |]
            | notypeclasses refine (zesu_tac_sep_named_eq _ _ _ _ _)]
  end.

(* A pure goal sees the values of the names it mentions, and of the names
   those values mention. *)
Ltac zesu_open_named_equations :=
  lazymatch goal with
  | |- envs_entails _ _ => idtac
  | |- _ =>
      repeat match goal with
      | named : zesu_named_eq ?name _ |- ?target =>
          first [lazymatch target with context [name] => idtac end
                | match goal with _ : _ = ?value |- _ => lazymatch value with context [name] => idtac end end];
          apply zesu_named_eq_iff in named
      end
  end.

(* A load whose address mentions a local alias: unfold the alias everywhere
   and drop it, as the finisher would, so the lookup sees the address. *)
Ltac zesu_unfold_let_mem_address :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      match goal with
      | alias := _ |- _ =>
          lazymatch address with context [alias] => idtac end;
          ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
          unfold alias in *; try clear alias
      end
  end.

(* A successor's binder named like a block variable of the same type takes
   that variable: the generator names a value once, so the successor's
   [call_after] is the block's [call_after]. Otherwise Lithium packs the
   binders into one tuple, and each later binder deepens the projections of
   all earlier ones.

   Once a binder without a namesake has opened Lithium's tuple, the later
   binders of a framed package arrive as [∃ₗ x, (∃ y, _) ∗ Q]; that shape is
   taken here, before liSep moves the binder out under its own name and the
   namesake is lost.

   Only names that hold across blocks qualify, and the generator gives such
   names only at a call boundary, where it also records named equations. A
   block with no named equation names its variables per block (the register
   values at its entry), so a successor's binder of the same name is a
   different value: taking it costs a pass per wrong witness (two decodeItem
   caller blocks ran past their CPU limit). Such a block keeps Lithium's
   instantiation. *)
Ltac2 zesu_no_namesake () := Control.zero (Tactic_failure None).

(* A name the generator used for more than one value: Rocq renamed the later
   ones by a digit suffix (`before`, `before0`), so the name is not one value
   across blocks (each call's facts reuse a callee binder's name). A name that
   itself ends in a digit gives no such evidence. *)
Ltac2 zesu_name_reused (name : ident) : bool :=
  let base := Ident.to_string name in
  let size := String.length base in
  let is_digit c := let code := Char.to_int c in Bool.and (Int.le 48 code) (Int.le code 57) in
  if Int.equal size 0 then false else
  if is_digit (String.get base (Int.sub size 1)) then false else
  List.exist (fun (hypothesis, _, _) =>
    let other := Ident.to_string hypothesis in
    let length := String.length other in
    let rec prefix i :=
      if Int.equal i size then true
      else if Char.equal (String.get other i) (String.get base i) then prefix (Int.add i 1)
      else false in
    let rec digits i :=
      if Int.equal i length then true
      else if is_digit (String.get other i) then digits (Int.add i 1) else false in
    if Int.le length size then false else Bool.and (prefix 0) (digits size))
    (Control.hyps ()).

(* A call's argument register binder (`call12_x13`): the value the register
   holds when that call is entered, which the call-site facts fix. A block
   variable of that name is the value from another path into the call, so it
   is never the witness (decodeParentHeader 0300 took it and left
   `call12_x13 = machine_x13` unprovable). *)
Ltac2 zesu_call_argument_name (name : ident) : bool :=
  let text := Ident.to_string name in
  let size := String.length text in
  let code_at i := if Int.lt i size then Char.to_int (String.get text i) else 0 in
  let at_char i code := Int.equal (code_at i) code in
  let is_digit i := let code := code_at i in Bool.and (Int.le 48 code) (Int.le code 57) in
  let rec digits i := if is_digit i then digits (Int.add i 1) else i in
  if Bool.and (at_char 0 99) (Bool.and (at_char 1 97) (Bool.and (at_char 2 108) (at_char 3 108))) then
    let layer_end := digits 4 in
    if Bool.and (at_char layer_end 95) (at_char (Int.add layer_end 1) 120) then
      let register := Int.add layer_end 2 in
      let register_end := digits register in
      Bool.and (Int.lt register register_end) (Int.equal register_end size)
    else false
  else false.

Ltac2 zesu_named_equation_in_context () :=
  List.exist (fun (_, _, hypothesis_type) =>
    match Constr.Unsafe.kind hypothesis_type with
    | Constr.Unsafe.App head _ => Constr.equal head '(@zesu_named_eq)
    | _ => false
    end) (Control.hyps ()).

Ltac2 zesu_binder_namesake (binder_type : constr) (body : constr) : constr :=
  match Constr.Unsafe.kind body with
  | Constr.Unsafe.Lambda binder _ =>
      match Constr.Binder.name binder with
      | Some name =>
          match List.find_opt (fun (hypothesis, _, _) => Ident.equal hypothesis name)
                  (Control.hyps ()) with
          | Some (_, _, hypothesis_type) =>
              if Bool.and (Constr.equal hypothesis_type binder_type)
                   (Bool.and (zesu_named_equation_in_context ())
                     (Bool.and (Bool.neg (zesu_name_reused name))
                       (Bool.neg (zesu_call_argument_name name))))
              then Control.hyp name else zesu_no_namesake ()
          | None => zesu_no_namesake ()
          end
      | None => zesu_no_namesake ()
      end
  | _ => zesu_no_namesake ()
  end.

(* Iris's connectives are primitive projections: an application's head is
   either the projection (the BI is then not among the arguments) or its
   constant, so a connective's own arguments are the last ones. *)
Ltac2 zesu_constant_head (term : constr) (reference : constr) : bool :=
  let constant_of term :=
    match Constr.Unsafe.kind term with
    | Constr.Unsafe.Constant constant _ => Some constant
    | Constr.Unsafe.Proj projection _ _ => Proj.to_constant projection
    | _ => None
    end in
  match constant_of term with
  | Some constant =>
      match constant_of reference with
      | Some expected => Constant.equal constant expected
      | None => false
      end
  | None => false
  end.

Ltac2 zesu_named_binder_witness () :=
  lazy_match! goal with
  | [ |- envs_entails _ (bi_sep (@bi_exist _ ?binder_type ?body) _) ] =>
      let value := zesu_binder_namesake binder_type body in
      ltac1:(value |- notypeclasses refine (zesu_tac_sep_exist_witness _ value _ _ _); red_li_prod)
        (Ltac1.of_constr value)
  | [ |- envs_entails _ (@bi_exist _ (li_prod _ _) ?outer) ] =>
      match Constr.Unsafe.kind outer with
      | Constr.Unsafe.Lambda _ inner =>
          match Constr.Unsafe.kind inner with
          | Constr.Unsafe.App head arguments =>
              let count := Array.length arguments in
              if Int.le 2 count then
                let package := Array.get arguments (Int.sub count 2) in
                let framed_package :=
                  if zesu_constant_head head '(@bi_sep) then
                    match Constr.Unsafe.kind package with
                    | Constr.Unsafe.App package_head package_arguments =>
                        let package_count := Array.length package_arguments in
                        if Bool.and (zesu_constant_head package_head '(@bi_exist))
                             (Int.le 2 package_count)
                        then Some (Array.get package_arguments (Int.sub package_count 2),
                                   Array.get package_arguments (Int.sub package_count 1))
                        else None
                    | _ => None
                    end
                  else None in
                match framed_package with
                | Some (binder_type, body) =>
                    let value := zesu_binder_namesake binder_type body in
                    ltac1:(value |- notypeclasses refine
                      (zesu_tac_li_ex_sep_exist_witness _ value _ _ _); red_li_prod)
                      (Ltac1.of_constr value)
                | None =>
                    let value := zesu_binder_namesake package
                      (Array.get arguments (Int.sub count 1)) in
                    ltac1:(value |- notypeclasses refine (tac_li_ex_ex_evar _ value _ _); red_li_prod)
                      (Ltac1.of_constr value)
                end
              else zesu_no_namesake ()
          | _ => zesu_no_namesake ()
          end
      | _ => zesu_no_namesake ()
      end
  | [ |- envs_entails _ (@bi_exist _ ?binder_type ?body) ] =>
      let value := zesu_binder_namesake binder_type body in
      ltac1:(value |- notypeclasses refine (tac_ex_evar _ value _ _); red_li_prod)
        (Ltac1.of_constr value)
  end.

Ltac zesu_named_binder_witness := ltac2:(zesu_named_binder_witness ()).

(* An existential whose conjuncts are hypotheses once its witnesses are set
   (a successor restating a call's facts over fresh names): each conjunct is
   closed by a hypothesis with the same head, which sets the witnesses. Only
   syntactic existentials and conjunctions are opened: `eexists` and `split`
   would also open definitions that unfold to an equation or a record. *)
Ltac zesu_finish_exists_from_hypotheses :=
  lazymatch goal with |- ex _ => idtac end;
  solve [repeat lazymatch goal with |- ex _ => eexists end;
    repeat lazymatch goal with |- _ /\ _ => split end;
    multimatch goal with |- ?conjunct =>
      let head := get_head conjunct in
      multimatch goal with
      | Hfact : ?fact |- _ =>
          let fact_head := get_head fact in
          constr_eq head fact_head;
          exact Hfact
      end
    end].
