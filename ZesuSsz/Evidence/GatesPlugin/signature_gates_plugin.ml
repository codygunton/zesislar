open Names
open Printer
open Ltac2_plugin

let rec constant_of_term sigma term =
  match EConstr.kind sigma term with
  | Constr.Const (constant, _) -> constant
  | Constr.App (head, _) -> constant_of_term sigma head
  | _ -> CErrors.user_err Pp.(str "The axiom gate requires a constant")

let check_axioms term allowed env sigma =
  let target = constant_of_term sigma term in
  let allowed = List.map (constant_of_term sigma) allowed in
  let state = Conv_oracle.get_transp_state (Environ.oracle env) in
  let reference = GlobRef.ConstRef target in
  let instance, _ = UnivGen.fresh_global_instance env reference in
  let assumptions =
    Assumptions.assumptions state reference instance
  in
  let actual =
    ContextObjectMap.fold
      (fun object_ _ acc ->
        match object_ with
        | Axiom (Constant constant, _) -> constant :: acc
        | Variable _ ->
            CErrors.user_err Pp.(str "Unexpected section variable")
        | Axiom _ ->
            CErrors.user_err Pp.(str "Unexpected non-constant axiom")
        | Opaque _ | Transparent _ -> acc)
      assumptions []
  in
  let same = Environ.QConstant.equal env in
  let missing = List.filter (fun c -> not (List.exists (same c) actual)) allowed in
  let extra = List.filter (fun c -> not (List.exists (same c) allowed)) actual in
  if missing <> [] || extra <> [] then
    CErrors.user_err
      Pp.(str "Axiom allow-list mismatch for " ++ Constant.print target
          ++ str "; missing: "
          ++ prlist_with_sep (fun () -> str ", ") Constant.print missing
          ++ str "; extra: "
          ++ prlist_with_sep (fun () -> str ", ") Constant.print extra)

let () =
  let open Tac2externals in
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin"; mltac_tactic = "exact_axioms" }
    (Tac2ffi.constr @-> Tac2ffi.list Tac2ffi.constr @-> eret Tac2ffi.unit)
    check_axioms

(* Keep the relaxed lookup mode private to this search. *)
let target_registration reference =
  Proofview.Goal.enter (fun goal ->
    let sigma = Proofview.Goal.sigma goal in
    let head = GlobRef.ConstRef (constant_of_term sigma reference) in
    let database = Hints.searchtable_map Class_tactics.typeclasses_db in
    let mode = [|Hints.ModeInput; Hints.ModeInput;
                 Hints.ModeOutput; Hints.ModeOutput|] in
    let database = Hints.Hint_db.add_modes
      (GlobRef.Map.singleton head [mode]) database in
    let modes = Hints.Hint_db.modes database in
    let transparency = Hints.Hint_db.transparent_state database in
    Class_tactics.Search.eauto_tac (modes, transparency)
      ~only_classes:true ~best_effort:false ~depth:(Some 12)
      ~dep:true [database])

let () =
  let open Tac2externals in
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin";
           mltac_tactic = "target_registration" }
    (Tac2ffi.constr @-> tac Tac2ffi.unit)
    target_registration

(* Reject only a proved absence of the native root. Preserve uncertain
   scans for the existing exact checks and registered proof application. *)
exception Unknown_occurrence
let constraint_root_occurrence local_env sigma wanted term =
  let count = ref 0 in
  let rec local_alias env fuel term =
    if fuel <= 0 then raise Unknown_occurrence;
    match EConstr.kind sigma term with
    | Constr.Var name ->
        begin match Context.Named.Declaration.get_value (EConstr.lookup_named name env) with
        | Some body -> local_alias env (fuel - 1) body
        | None -> term
        end
    | Constr.Rel index ->
        begin match Context.Rel.Declaration.get_value (EConstr.lookup_rel index env) with
        | Some body -> local_alias env (fuel - 1) (EConstr.Vars.lift index body)
        | None -> term
        end
    | _ -> term
  in
  try
    let wanted = local_alias local_env 32 wanted in
    let root = match EConstr.kind sigma wanted with
      | Constr.Evar (key, _) -> key
      | _ -> raise Unknown_occurrence in
    let rec scan env term =
      if !count >= 512 then raise Unknown_occurrence;
      incr count;
      let term = local_alias env 32 term in
      match EConstr.kind sigma term with
      | Constr.Evar (key, _) when Evar.equal key root -> true
      | Constr.Meta _ -> raise Unknown_occurrence
      | _ ->
          let found = ref false in
          EConstr.iter_with_full_binders env sigma
            (fun declaration child_env -> EConstr.push_rel declaration child_env)
            (fun child_env child -> if not !found then found := scan child_env child)
            env term;
          !found
    in
    let found = scan local_env term in
    (Some found, !count)
  with Unknown_occurrence -> (None, !count)
     | Not_found -> (None, !count)
(* A positive raw occurrence admits the pointer candidate. A negative or
   uncertain scan must use the unchanged reducing traversal. *)
let pointer_raw_occurrence pointer_env local_env sigma wanted term =
  let count = ref 0 in
  let rec local_alias env fuel term =
    if fuel <= 0 then raise Unknown_occurrence;
    match EConstr.kind sigma term with
    | Constr.Var name ->
        begin match Context.Named.Declaration.get_value (EConstr.lookup_named name env) with
        | Some body -> local_alias env (fuel - 1) body
        | None -> term
        end
    | Constr.Rel index ->
        begin match Context.Rel.Declaration.get_value (EConstr.lookup_rel index env) with
        | Some body -> local_alias env (fuel - 1) (EConstr.Vars.lift index body)
        | None -> term
        end
    | Constr.Meta _ -> raise Unknown_occurrence
    | _ -> term
  in
  try
    let expanded_wanted = local_alias pointer_env 32 wanted in
    let same depth candidate =
      EConstr.eq_constr sigma (EConstr.Vars.lift depth wanted) candidate ||
      EConstr.eq_constr sigma (EConstr.Vars.lift depth expanded_wanted) candidate
    in
    let rec scan env depth term =
      if !count >= 512 then raise Unknown_occurrence;
      incr count;
      if same depth term then true
      else
        let term = local_alias env 32 term in
        let found = ref (same depth term) in
        if not !found then
          EConstr.iter_with_full_binders env sigma
            (fun declaration (child_env, child_depth) ->
              (EConstr.push_rel declaration child_env, child_depth + 1))
            (fun (child_env, child_depth) child ->
              if not !found then found := scan child_env child_depth child)
            (env, depth) term;
        !found
    in
    (Some (scan local_env 0 term), !count)
  with Unknown_occurrence -> (None, !count)
     | Not_found -> (None, !count)
     | error when CErrors.noncritical error -> (None, !count)

(* Read only the native index's exact shelved equality at the owned pointer.
   The caller proves that equality through the existing fact registry. *)
let array_index_constraints pointer index sidecondition equality env sigma =
  let same left right = EConstr.eq_constr sigma left right in
  let rec contains local_env depth wanted term =
    let wanted = Reductionops.whd_all env sigma wanted in
    let term = Reductionops.whd_all local_env sigma term in
    let found = ref (same (EConstr.Vars.lift depth wanted) term) in
    if not !found then
      EConstr.iter_with_full_binders local_env sigma
        (fun declaration (child_env, child_depth) ->
          (EConstr.push_rel declaration child_env, child_depth + 1))
        (fun (child_env, child_depth) child ->
          if not !found then
            found := contains child_env child_depth wanted child)
        (local_env, depth) term;
    !found
  in
  List.filter (fun key ->
    let info = Evd.find_undefined sigma key in
    let local_env = Evd.evar_filtered_env env info in
    let conclusion = Evd.evar_concl info in
    match EConstr.kind sigma conclusion with
    | Constr.App (wrapper, [|fact|]) when same wrapper sidecondition ->
        begin match EConstr.kind sigma fact with
        | Constr.App (head, [|_type; _left; _right|]) when EConstr.eq_constr_nounivs sigma head equality ->
            let occurrence, _ = constraint_root_occurrence local_env sigma index fact in
            occurrence <> Some false &&
            contains local_env 0 index fact &&
            (let pointer_occurrence, _ =
               pointer_raw_occurrence env local_env sigma pointer fact in
             pointer_occurrence = Some true ||
             contains local_env 0 pointer fact)
        | _ -> false
        end
    | _ -> false) (Evd.shelf sigma)

let () =
  let open Tac2externals in
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin";
           mltac_tactic = "array_index_constraints" }
    (Tac2ffi.constr @-> Tac2ffi.constr @-> Tac2ffi.constr @->
     Tac2ffi.constr @-> gret (Tac2ffi.list Tac2ffi.evar))
    (fun pointer index sidecondition equality goal ->
      array_index_constraints pointer index sidecondition equality
        (Proofview.Goal.env goal) (Proofview.Goal.sigma goal))
