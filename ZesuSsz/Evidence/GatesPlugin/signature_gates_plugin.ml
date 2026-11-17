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
   the environment switches it on; ZESU_TELEMETRY_CALLERS=1 besides adds the
   Ltac caller of each call. The variables are read once. Each effect runs
   when the tactic runs, not when it is defined. *)
let telemetry_on =
  lazy (match Sys.getenv_opt "ZESU_TELEMETRY" with Some "1" -> true | _ -> false)

let telemetry_callers_on =
  lazy (Lazy.force telemetry_on &&
        match Sys.getenv_opt "ZESU_TELEMETRY_CALLERS" with Some "1" -> true | _ -> false)

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

(* The nodes of a term as LinearFirstLia's budget walk (zesu_linear_remaining)
   counts them: an application costs 2 for a constant, constructor, inductive
   or variable head and 1 plus its nodes for any other head; a product,
   abstraction, let or cast costs 1 plus its parts; every other term 1. In
   OCaml it costs about a hundredth of the Ltac2 walk, which ran on every call. *)
let rec telemetry_term_nodes sigma term =
  let nodes = telemetry_term_nodes sigma in
  match EConstr.kind sigma term with
  | Constr.App (head, arguments) ->
      let head_nodes = match EConstr.kind sigma head with
        | Constr.Const _ | Constr.Construct _ | Constr.Ind _ | Constr.Var _ -> 2
        | _ -> 1 + nodes head in
      Array.fold_left (fun sum argument -> sum + nodes argument) head_nodes arguments
  | Constr.Prod (_, typ, body) | Constr.Lambda (_, typ, body) -> 1 + nodes typ + nodes body
  | Constr.LetIn (_, value, typ, body) -> 1 + nodes typ + nodes value + nodes body
  | Constr.Cast (value, _, typ) -> 1 + nodes value + nodes typ
  | _ -> 1

let telemetry_is_prop env sigma typ =
  try Retyping.get_sort_family_of env sigma typ == Sorts.InProp
  with error when CErrors.noncritical error -> false

(* (facts, nodes, goal_nodes): the Prop hypotheses without a body, their nodes,
   and the goal's nodes. *)
let telemetry_goal_sizes goal =
  let env = Proofview.Goal.env goal and sigma = Proofview.Goal.sigma goal in
  let facts, nodes = List.fold_left (fun (facts, nodes) declaration ->
      match declaration with
      | Context.Named.Declaration.LocalAssum (_, typ) when telemetry_is_prop env sigma typ ->
          (facts + 1, nodes + telemetry_term_nodes sigma typ)
      | _ -> (facts, nodes)) (0, 0) (Proofview.Goal.hyps goal) in
  [facts; nodes; telemetry_term_nodes sigma (Proofview.Goal.concl goal)]

(* The Ltac call stack of a closure: its frames of named tactics and tactic
   notations, innermost first, each with the module and line it was called
   from, joined by `>` (calls of local tactic variables such as a wrapper's
   `run` or a `closer` argument are left out). Coq records the stack only
   under `Ltac Backtrace`, which caller mode switches on. *)
let telemetry_tacvalue_tag : Ltac_plugin.Taccoerce.tacvalue Geninterp.Val.typ =
  match Geninterp.val_tag (Genarg.topwit Ltac_plugin.Taccoerce.wit_tacvalue) with
  | Geninterp.Val.Base tag -> tag

let telemetry_stack value =
  match value with
  | Geninterp.Val.Dyn (tag, closure) ->
      begin match Geninterp.Val.eq tag telemetry_tacvalue_tag with
      | Some Util.Refl ->
          begin match closure with
          | Ltac_plugin.Taccoerce.VFun (_, (stack, _), _, _, _, _) -> stack
          | Ltac_plugin.Taccoerce.VRec _ -> []
          end
      | None -> []
      end

let telemetry_frame (loc, call) =
  let open Ltac_plugin.Tacexpr in
  let name = match call with
    | LtacNameCall kn | LtacNotationCall kn -> Some (Label.to_string (KerName.label kn))
    | LtacVarCall _ | LtacMLCall _ | LtacAtomCall _ | LtacConstrInterp _ -> None in
  let place = match loc with
    | Some { Loc.fname = Loc.InFile { dirpath; file }; line_nb; _ } ->
        let unit = match dirpath with
          | Some path -> List.hd (List.rev (String.split_on_char '.' path))
          | None -> Filename.remove_extension (Filename.basename file) in
        Printf.sprintf "@%s:%d" unit line_nb
    | _ -> "" in
  Option.map (fun name -> String.map (fun c -> if c = ' ' then '_' else c) (name ^ place)) name

let telemetry_caller_frames = 8

let telemetry_frames value =
  (match Goptions.get_option_value ["Ltac"; "Backtrace"] with
   | Some read when read () <> Goptions.BoolValue true ->
       Goptions.set_bool_option_value ["Ltac"; "Backtrace"] true
   | _ -> ());
  let frames = List.filter_map telemetry_frame (telemetry_stack value) in
  match List.filteri (fun index _ -> index < telemetry_caller_frames) frames with
  | [] -> "-"
  | frames -> String.concat ">" frames

(* A coarse class of a goal: its relation or connective by shortest name, an
   equality with its carrier's head, connectives with their parts, three
   levels deep. *)
let telemetry_global_name reference =
  try Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty reference)
  with Not_found -> "?"

let rec telemetry_shape env sigma depth term =
  if depth <= 0 then "_" else
  let shape = telemetry_shape env sigma (depth - 1) in
  match EConstr.kind sigma term with
  | Constr.Prod (_, _, body) -> "forall(" ^ shape body ^ ")"
  | Constr.App (head, arguments) ->
      begin match EConstr.kind sigma head with
      | Constr.Const (constant, _) ->
          let name = telemetry_global_name (GlobRef.ConstRef constant) in
          if name = "not" && Array.length arguments = 1 then "not(" ^ shape arguments.(0) ^ ")"
          else name
      | Constr.Ind (inductive, _) ->
          let name = telemetry_global_name (GlobRef.IndRef inductive) in
          let arity = Array.length arguments in
          if name = "eq" && arity = 3 then
            "eq:" ^ (match EConstr.kind sigma (fst (EConstr.decompose_app sigma arguments.(0))) with
                     | Constr.Const (constant, _) -> telemetry_global_name (GlobRef.ConstRef constant)
                     | Constr.Ind (inductive, _) -> telemetry_global_name (GlobRef.IndRef inductive)
                     | _ -> "?")
          else if List.mem name ["and"; "or"; "iff"] && arity = 2 then
            name ^ "(" ^ shape arguments.(0) ^ "," ^ shape arguments.(1) ^ ")"
          else name
      | Constr.Var _ -> "var"
      | _ -> "app"
      end
  | Constr.Const (constant, _) -> telemetry_global_name (GlobRef.ConstRef constant)
  | Constr.Ind (inductive, _) -> telemetry_global_name (GlobRef.IndRef inductive)
  | Constr.Var _ -> "var"
  | _ -> "other"

let telemetry_goal_shape goal =
  let shape = telemetry_shape (Proofview.Goal.env goal) (Proofview.Goal.sigma goal) 3
      (Proofview.Goal.concl goal) in
  String.map (fun c -> if c = ' ' then '_' else c) shape

let telemetry_emit kind site caller sizes (start : telemetry_sample) ok =
  let stop = telemetry_sample () in
  let facts, nodes, goal_nodes = match sizes with
    | [facts; nodes; goal_nodes] -> facts, nodes, goal_nodes
    | _ -> -1, -1, -1 in
  Printf.printf
    "@@T kind=%s site=%s stage=%s facts=%d nodes=%d goal_nodes=%d ms=%.3f ok=%d \
     cpu_ms=%.3f ts_us=%d rss0_kb=%d rss1_kb=%d%s\n%!"
    kind site !telemetry_stage facts nodes goal_nodes
    (float_of_int (stop.wall - start.wall) /. 1000.) (if ok then 1 else 0)
    (float_of_int (stop.cpu - start.cpu) /. 1000.) start.wall start.rss stop.rss
    (if Lazy.force telemetry_callers_on then " caller=" ^ caller else "")

let () =
  let open Tac2externals in
  let open Proofview.Notations in
  let name tactic = { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin"; mltac_tactic = tactic } in
  define (name "telemetry_enabled") (Tac2ffi.unit @-> ret Tac2ffi.bool)
    (fun () -> Lazy.force telemetry_on);
  (* The sample is a (wall us, cpu us, rss KiB) triple of ints. *)
  define (name "telemetry_sample") (Tac2ffi.unit @-> tac (Tac2ffi.list Tac2ffi.int))
    (fun () -> telemetry_now (fun () ->
      let s = telemetry_sample () in [s.wall; s.cpu; s.rss]));
  (* (facts, nodes, goal_nodes) of the single focused goal; -1 each off it. *)
  define (name "telemetry_sizes") (Tac2ffi.unit @-> tac (Tac2ffi.list Tac2ffi.int))
    (fun () -> Proofview.Goal.goals >>= function
      | [goal] -> goal >>= fun goal -> Proofview.tclUNIT (telemetry_goal_sizes goal)
      | _ -> Proofview.tclUNIT [-1; -1; -1]);
  (* Caller mode: the caller frames of an Ltac1 closure and the shape of the
     single focused goal, as `<frames> shape=<shape>`; `-` outside it. *)
  define (name "telemetry_caller") (Tac2ffi.repr_ext Tac2ffi.val_ltac1 @-> tac Tac2ffi.string)
    (fun value ->
      if not (Lazy.force telemetry_callers_on) then Proofview.tclUNIT "-" else
      (Proofview.Goal.goals >>= function
        | [goal] -> goal >>= fun goal -> Proofview.tclUNIT (telemetry_goal_shape goal)
        | _ -> Proofview.tclUNIT "-") >>= fun shape ->
      telemetry_now (fun () -> telemetry_frames value ^ " shape=" ^ shape));
  define (name "telemetry_emit")
    (Tac2ffi.string @-> Tac2ffi.string @-> Tac2ffi.string @-> Tac2ffi.list Tac2ffi.int @->
     Tac2ffi.list Tac2ffi.int @-> Tac2ffi.bool @-> tac Tac2ffi.unit)
    (fun kind site caller sizes start ok -> telemetry_now (fun () ->
      match start with
      | [wall; cpu; rss] -> telemetry_emit kind site caller sizes { wall; cpu; rss } ok
      | _ -> ()));
  (* Sets the stage and returns the previous one. *)
  define (name "telemetry_stage_swap") (Tac2ffi.string @-> tac Tac2ffi.string)
    (fun stage -> telemetry_now (fun () ->
      let previous = !telemetry_stage in telemetry_stage := stage; previous))

(* Solver failure memo (ZesuSsz/Automation2/FailureMemo.v). The solver sites
   are deterministic and their budgets count nodes, so a site that failed on a
   goal fails again on the same conclusion and the same context. The key hashes
   the site, the conclusion and every declaration of the context (name, type,
   body) through defined evars; an undefined evar leaves the goal without a
   key. Only failures are recorded. The memo belongs to one proof (its name and
   root goals) and is emptied when another proof uses it. *)
exception Failure_memo_unkeyed

let failure_memo_combine h x = (h * 65599 + x) land max_int

let rec failure_memo_hash sigma acc term =
  let open Constr in
  let combine = failure_memo_combine in
  let head = match EConstr.kind sigma term with
    | Rel n -> combine 1 n
    | Var id -> combine 2 (Id.hash id)
    | Meta _ | Evar _ -> raise Failure_memo_unkeyed
    | Sort s -> combine 3 (Sorts.hash (EConstr.ESorts.kind sigma s))
    | Cast _ -> 4
    | Prod _ -> 5
    | Lambda _ -> 6
    | LetIn _ -> 7
    | App (_, arguments) -> combine 8 (Array.length arguments)
    | Const (constant, _) -> combine 9 (Constant.CanOrd.hash constant)
    | Ind (ind, _) -> combine 10 (Ind.CanOrd.hash ind)
    | Construct ((ind, n), _) -> combine 11 (combine (Ind.CanOrd.hash ind) n)
    | Case (info, _, _, _, _, _, branches) ->
        combine 12 (combine (Ind.CanOrd.hash info.ci_ind) (Array.length branches))
    | Fix ((_, n), _) -> combine 13 n
    | CoFix (n, _) -> combine 14 n
    | Proj (projection, _, _) -> combine 15 (Projection.CanOrd.hash projection)
    | Int n -> combine 16 (Uint63.hash n)
    | Float f -> combine 17 (Float64.hash f)
    | Array (_, values, _, _) -> combine 18 (Array.length values) in
  EConstr.fold sigma (failure_memo_hash sigma) (combine acc head) term

(* [goal hash; context hash], or [] without a key. *)
let failure_memo_key site goal =
  let sigma = Proofview.Goal.sigma goal in
  let hash = failure_memo_hash sigma in
  let declaration h decl =
    let open Context.Named.Declaration in
    let h = failure_memo_combine h (Id.hash (get_id decl)) in
    match decl with
    | LocalAssum (_, ty) -> hash (failure_memo_combine h 1) ty
    | LocalDef (_, body, ty) -> hash (hash (failure_memo_combine h 2) body) ty in
  try
    let context = List.fold_left declaration 17
      (EConstr.named_context (Proofview.Goal.env goal)) in
    [hash (Hashtbl.hash site) (Proofview.Goal.concl goal); context]
  with Failure_memo_unkeyed -> []

let failure_memo_owner = ref None
let failure_memo_table : (int list, unit) Hashtbl.t = Hashtbl.create 1024

(* The current proof's name and root goal evars; None outside a proof. *)
let failure_memo_proof () =
  match (Vernacstate.Declare.give_me_the_proof_opt [@ocaml.alert "-deprecated"]) () with
  | None -> None
  | Some proof ->
      let data = Proof.data proof in
      let roots = List.map (fun (_, term, _) ->
        match Constr.kind (EConstr.Unsafe.to_constr term) with
        | Constr.Evar (evar, _) -> Evar.repr evar
        | _ -> -1) (Proofview.initial_goals data.Proof.entry) in
      Some (data.Proof.name, roots)
  | exception error when CErrors.noncritical error -> None

(* The table of the current proof, emptied when the proof changed. *)
let failure_memo_current () =
  match failure_memo_proof () with
  | None -> None
  | Some proof ->
      (match !failure_memo_owner with
       | Some (name, roots) when Id.equal name (fst proof) && roots = snd proof -> ()
       | _ -> Hashtbl.reset failure_memo_table; failure_memo_owner := Some proof);
      Some failure_memo_table

let () =
  let open Tac2externals in
  let name tactic = { Tac2expr.mltac_plugin = "zesu-signature-gates.plugin"; mltac_tactic = tactic } in
  let lift f = Proofview.tclLIFT (Proofview.NonLogical.make f) in
  define (name "failure_memo_key") (Tac2ffi.string @-> gret (Tac2ffi.list Tac2ffi.int))
    failure_memo_key;
  define (name "failure_memo_failed") (Tac2ffi.list Tac2ffi.int @-> tac Tac2ffi.bool)
    (fun key -> lift (fun () ->
      key <> [] && (match failure_memo_current () with
        | Some table -> Hashtbl.mem table key
        | None -> false)));
  define (name "failure_memo_record") (Tac2ffi.list Tac2ffi.int @-> tac Tac2ffi.unit)
    (fun key -> lift (fun () ->
      if key <> [] then match failure_memo_current () with
        | Some table -> Hashtbl.replace table key ()
        | None -> ()))
