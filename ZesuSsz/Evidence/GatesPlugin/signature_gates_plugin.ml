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
