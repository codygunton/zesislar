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

(* Preserve the declared source-input mode and reject ambiguous facts. *)
let unique_entry_registration () =
  let database = Hints.searchtable_map Class_tactics.typeclasses_db in
  let modes = Hints.Hint_db.modes database in
  let transparency = Hints.Hint_db.transparent_state database in
  let search = Class_tactics.Search.eauto_tac (modes, transparency)
    ~unique:true ~only_classes:true ~best_effort:false ~depth:(Some 12)
    ~dep:true [database] in
  Proofview.tclOR search (fun (error, info) ->
    match error with
    | Proofview.MoreThanOneSuccess ->
        Tacticals.tclFAILn ~info 100
          Pp.(str "Ambiguous source-keyed entry registration")
    | _ -> Proofview.tclZERO ~info error)

let () =
  let open Tac2externals in
  define { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin";
           mltac_tactic = "unique_entry_registration" }
    (Tac2ffi.unit @-> tac Tac2ffi.unit)
    unique_entry_registration

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

(* Solver telemetry (ZesuSsz/Automation2/Telemetry.v). ZESU_TELEMETRY=1 in
   the environment switches it on; the variable is read once. Each effect
   runs when the tactic runs, not when it is defined. *)
let telemetry_on =
  lazy (match Sys.getenv_opt "ZESU_TELEMETRY" with Some "1" -> true | _ -> false)

let telemetry_now f = Proofview.tclLIFT (Proofview.NonLogical.make f)

let telemetry_clock_us () = int_of_float (Unix.gettimeofday () *. 1e6)

let telemetry_cpu_us () = int_of_float (Sys.time () *. 1e6)

(* Resident set in KiB: the second field of statm, in 4 KiB pages. *)
let telemetry_rss_kb () =
  try
    let channel = open_in "/proc/self/statm" in
    let line = Fun.protect ~finally:(fun () -> close_in channel)
      (fun () -> input_line channel) in
    Scanf.sscanf line "%d %d" (fun _ resident -> resident * 4)
  with _ -> -1

(* The innermost telemetry stage. *)
let telemetry_stage = ref "none"

type telemetry_sample = { wall : int; cpu : int; rss : int }

let telemetry_sample () =
  { wall = telemetry_clock_us (); cpu = telemetry_cpu_us (); rss = telemetry_rss_kb () }

(* Measurement only: a key of the focused goal for repeated-failure counts.
   [goal hash; pruned-context hash; pruned fact count; whole-context hash].
   The pruned context mirrors ContextCollection.zesu_context_relevance: the
   Prop facts that share a variable with the goal, transitively (closed facts
   always), with the declarations of the variables they use. All zero when
   the goal or a declaration has an undefined evar. *)
let telemetry_combine h x = (h * 65599 + x) land max_int

let telemetry_key goal =
  let env = Proofview.Goal.env goal and sigma = Proofview.Goal.sigma goal in
  let open Context.Named.Declaration in
  let declarations = EConstr.named_context env in
  let closed term = EConstr.to_constr_opt sigma term in
  let is_prop ty =
    try Retyping.get_sort_family_of env sigma ty = Sorts.InProp with _ -> false in
  let vars = Termops.collect_vars sigma in
  let info = List.map (fun declaration ->
    match declaration with
    | LocalAssum (_, ty) -> (declaration, is_prop ty, vars ty)
    | LocalDef (_, body, ty) -> (declaration, false, Id.Set.union (vars ty) (vars body)))
    declarations in
  let rec relevance found =
    let next = List.fold_left (fun found (declaration, fact, used) ->
      let id = get_id declaration in
      if Id.Set.mem id found
         || (fact && (Id.Set.is_empty used || not (Id.Set.disjoint used found)))
      then Id.Set.add id (Id.Set.union found used) else found) found info in
    if Id.Set.cardinal next = Id.Set.cardinal found then next else relevance next in
  let hash_declaration declaration =
    match declaration with
    | LocalAssum (id, ty) ->
        Option.map (fun ty -> telemetry_combine (Id.hash id.Context.binder_name) (Constr.hash ty))
          (closed ty)
    | LocalDef (id, body, ty) ->
        (match closed body, closed ty with
         | Some body, Some ty ->
             Some (telemetry_combine (Id.hash id.Context.binder_name)
                     (telemetry_combine (Constr.hash body) (Constr.hash ty)))
         | _ -> None) in
  match closed (Proofview.Goal.concl goal) with
  | None -> [0; 0; 0; 0]
  | Some concl ->
      let relevant = relevance (Termops.collect_vars sigma (Proofview.Goal.concl goal)) in
      let step (pruned, count, whole) (declaration, fact, _) =
        match hash_declaration declaration with
        | None -> raise Exit
        | Some h ->
            let kept = Id.Set.mem (get_id declaration) relevant in
            ((if kept then telemetry_combine pruned h else pruned),
             (if kept && fact then count + 1 else count),
             telemetry_combine whole h) in
      (try
         let pruned, count, whole = List.fold_left step (17, 0, 17) info in
         [Constr.hash concl; pruned; count; whole]
       with Exit -> [0; 0; 0; 0])

let telemetry_emit kind site facts nodes goal_nodes (start : telemetry_sample) key ok =
  let stop = telemetry_sample () in
  let key = match key with
    | [goal; pruned; count; whole] ->
        Printf.sprintf " gk=%d pk=%d pn=%d wk=%d" goal pruned count whole
    | _ -> "" in
  Printf.printf
    "@@T kind=%s site=%s stage=%s facts=%d nodes=%d goal_nodes=%d ms=%.3f ok=%d \
     cpu_ms=%.3f ts_us=%d rss0_kb=%d rss1_kb=%d%s\n%!"
    kind site !telemetry_stage facts nodes goal_nodes
    (float_of_int (stop.wall - start.wall) /. 1000.) (if ok then 1 else 0)
    (float_of_int (stop.cpu - start.cpu) /. 1000.) start.wall start.rss stop.rss key

let () =
  let open Tac2externals in
  let name tactic = { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin"; mltac_tactic = tactic } in
  define (name "telemetry_enabled") (Tac2ffi.unit @-> ret Tac2ffi.bool)
    (fun () -> Lazy.force telemetry_on);
  (* The sample is a (wall us, cpu us, rss KiB) triple of ints; a goal key
     (telemetry_key) may follow it. *)
  define (name "telemetry_sample") (Tac2ffi.unit @-> tac (Tac2ffi.list Tac2ffi.int))
    (fun () -> telemetry_now (fun () ->
      let s = telemetry_sample () in [s.wall; s.cpu; s.rss]));
  define (name "telemetry_key") (Tac2ffi.unit @-> gret (Tac2ffi.list Tac2ffi.int))
    (fun () goal -> telemetry_key goal);
  define (name "telemetry_emit")
    (Tac2ffi.string @-> Tac2ffi.string @-> Tac2ffi.int @-> Tac2ffi.int @-> Tac2ffi.int @->
     Tac2ffi.list Tac2ffi.int @-> Tac2ffi.bool @-> tac Tac2ffi.unit)
    (fun kind site facts nodes goal_nodes start ok -> telemetry_now (fun () ->
      match start with
      | wall :: cpu :: rss :: key ->
          telemetry_emit kind site facts nodes goal_nodes { wall; cpu; rss } key ok
      | _ -> ()));
  (* Sets the stage and returns the previous one. *)
  define (name "telemetry_stage_swap") (Tac2ffi.string @-> tac Tac2ffi.string)
    (fun stage -> telemetry_now (fun () ->
      let previous = !telemetry_stage in telemetry_stage := stage; previous))
