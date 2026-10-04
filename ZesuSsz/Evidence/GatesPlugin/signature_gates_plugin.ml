open Names
open Printer
open Ltac2_plugin

let constant_of_term sigma term =
  match EConstr.kind sigma term with
  | Constr.Const (constant, _) -> constant
  | _ -> CErrors.user_err Pp.(str "The axiom gate requires a constant")

let check_axioms term allowed env sigma =
  let target = constant_of_term sigma term in
  let allowed = List.map (constant_of_term sigma) allowed in
  let state = Conv_oracle.get_transp_state (Environ.oracle env) in
  let assumptions =
    Assumptions.assumptions state (GlobRef.ConstRef target) (EConstr.to_constr sigma term)
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
