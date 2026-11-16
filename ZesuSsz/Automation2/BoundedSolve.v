From Coq Require Import ZArith.ZArith Strings.String micromega.Lia micromega.Zify.
From stdpp Require Import bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.ContextCollection.
Require Import ZesuSsz.Automation2.RecordFieldPruning.
Require Import ZesuSsz.Automation2.SearchBudget.
Require Import ZesuSsz.Automation2.LinearFirstLia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* The only caller of the solver engines: micromega (`xlia` through
   `LinearFirstLia`), the stdpp bit-vector preparation (`bv_simplify_arith`,
   `bv_saturate*`), a VM run on a goal, and the context saturations. A solver
   never runs on an unbounded context: every call first prunes the context to
   the facts that share a term with the goal, within a step bound, then checks
   the goal and the kept facts against a node budget (#287's integer walk,
   `LinearFirstLia.zesu_linear_context_within`), and fails when the budget is
   exceeded. `lia` and `bv_solve` reach these modes through their global
   overrides in Hooks.v, so frozen and library callers are bounded too. The
   proof hygiene check refuses the engines anywhere else in Automation2. *)

Inductive zesu_solver_kind : Set :=
| zesu_solver_lia
| zesu_solver_bv
| zesu_solver_saturation
| zesu_solver_vm.

(* Node budgets per kind: (pruned context, whole context), from the largest
   successful context of each arm on the 24 decodeItem blocks (scratch sweep
   bs-meas2 on the batch-3 bank, every arm logged), with margin. *)
Ltac2 zesu_bounded_budgets (kind : constr) : int * int :=
  if Constr.equal kind constr:(zesu_solver_lia) then
    (* Pruned closures reached 84937 nodes (32768 lost 5 blocks), while on
       decodeParentHeader 0300's final pure tail pruned contexts of 136615
       nodes and more grew past 8 GiB; whole-context closures reached 26708
       nodes (16384 lost a closure) and failing ones 212738. *)
    (98304, 32768)
  else if Constr.equal kind constr:(zesu_solver_bv) then
    (* Pruned closures reached 66611 nodes. No whole-context call closed a
       goal (2217 calls, up to 113294 nodes); the linked-facts path closed one
       of 27089 nodes. Unbudgeted, both arms reached 8 GiB on a 454-fact
       decodeParentHeader 0300 leaf. *)
    (98304, 32768)
  else if Constr.equal kind constr:(zesu_solver_saturation) then
    (* Saturations ran on contexts of up to 209156 nodes. *)
    (0, 262144)
  else (0, 4096).

(* Linking rounds of the pruned arm: closures needed at most 3. *)
Ltac2 zesu_bounded_prune_rounds () := 6.

Ltac2 zesu_bounded_kind (kind : Ltac1.t) : constr :=
  Option.get (Ltac1.to_constr kind).

Ltac2 zesu_bounded_within_whole (kind : constr) :=
  let (_, whole) := zesu_bounded_budgets kind in
  ZesuSsz.Automation2.LinearFirstLia.zesu_linear_context_within whole.

Ltac2 zesu_bounded_within_pruned (kind : constr) :=
  let (pruned, _) := zesu_bounded_budgets kind in
  ZesuSsz.Automation2.LinearFirstLia.zesu_linear_context_within pruned.

(* Clear the facts that share no term with the goal within the linking rounds
   (RecordFieldPruning.a3n_prune). *)
Ltac zesu_bounded_prune_goal :=
  ltac2:(ZesuSsz.Automation2.RecordFieldPruning.a3n_prune (zesu_bounded_prune_rounds ())).

Ltac zesu_bounded_whole kind :=
  let check := ltac2:(kind |- zesu_bounded_within_whole (zesu_bounded_kind kind)) in
  check kind.

Ltac zesu_bounded_pruned kind :=
  let check := ltac2:(kind |- zesu_bounded_within_pruned (zesu_bounded_kind kind)) in
  check kind.

(* The pruned arm, then the whole context, each within its budget. Without
   the whole-context arm decodeItem lost 8 closures; without the budgets the
   whole context reached 24 GiB and the pruned one 8 GiB on
   decodeParentHeader. *)
Ltac zesu_bounded_solve kind closer :=
  tryif zesu_switch_enabled constr:(ZesuStepFinisherOnce)
  then first [solve [zesu_bounded_prune_goal; zesu_bounded_pruned kind; closer]
             | (zesu_bounded_whole kind; closer)]
  else (zesu_bounded_whole kind; closer).

(* The facts that share an atom with the goal, at most 48 of at most 2048
   nodes each and two linking rounds (ContextCollection.zesu_select_goal_facts),
   within the solver context policy (SearchBudget.zesu_solve_selected). *)
Ltac zesu_bounded_selected site closer :=
  solve [once zesu_select_goal_facts;
    ZesuSsz.Automation2.SearchBudget.zesu_solve_selected site closer].

(* Linear arithmetic. *)
Ltac zesu_bounded_lia :=
  zesu_bounded_solve constr:(zesu_solver_lia) ltac:(zesu_lia_linear_first3).

Ltac zesu_bounded_lia_selected site :=
  zesu_bounded_selected site ltac:(zesu_lia_linear_first3).

(* The library solver on the facts linked to the goal by linear atoms, within
   two linking rounds and 16384 nodes (LinearFirstLia.zesu_linear_clear_unrelated). *)
Ltac zesu_lia_linked_facts :=
  once ltac2:(zesu_linear_clear_unrelated ()); Zify.zify; xlia Lia.zchecker.

(* The micromega engine on a context its caller has already cut down to the
   facts it reads, within the whole-context budget. *)
Ltac zesu_bounded_lia_on_context :=
  zesu_bounded_whole constr:(zesu_solver_lia); Zify.zify; xlia Lia.zchecker.

(* The arithmetic half of stdpp's `bv_solve`: unsigned ranges, unfolded
   moduli, then `solver`. `hook` runs after the saturation. *)
Ltac zesu_bv_arith hook solver :=
  bv_saturate_unsigned;
  hook;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl;
  solver.

(* stdpp's `bv_solve`, whose `lia` is the bounded override. *)
Ltac zesu_bv_engine :=
  bv_simplify_arith; zesu_bv_arith ltac:(bv_solve_unfold_tac) ltac:(lia).

(* `special` closes the goal outright or fails; otherwise the engine runs. *)
Ltac zesu_bounded_bv_with special :=
  zesu_bounded_solve constr:(zesu_solver_bv) ltac:(first [solve [special] | zesu_bv_engine]).

Ltac zesu_bounded_bv_selected site special :=
  zesu_bounded_selected site ltac:(first [solve [special] | zesu_bv_engine]).

(* The bit-vector steps, then the linked-facts solver, on a context within the
   bit-vector whole-context budget. *)
Ltac zesu_bounded_bv_linked_facts :=
  solve [zesu_bounded_whole constr:(zesu_solver_bv); bv_simplify_arith;
    zesu_bv_arith ltac:(bv_solve_unfold_tac) ltac:(zesu_lia_linked_facts)].

(* The arithmetic steps on a context its caller has already cut down to the
   facts it reads, after the caller's `prepare`. *)
Ltac zesu_bounded_bv_on_context prepare :=
  zesu_bounded_whole constr:(zesu_solver_bv); prepare; zesu_bv_arith idtac ltac:(lia).

(* A saturation adds facts that later goals read, so it never prunes. It runs
   only on a context within the saturation budget and is skipped otherwise. *)
Ltac zesu_bounded_saturate saturation :=
  tryif zesu_bounded_whole constr:(zesu_solver_saturation) then saturation else idtac.

Ltac zesu_bounded_bv_saturate :=
  zesu_bounded_saturate ltac:(bv_saturate).

(* A closer that saturates the context on its way (byte and word views):
   it runs only on a context within the saturation budget and fails otherwise,
   so its caller's next alternative runs. *)
Ltac zesu_bounded_views closer :=
  zesu_bounded_whole constr:(zesu_solver_saturation); closer.

(* A VM run on a goal reads no fact; the goal alone is within the VM budget. *)
Ltac2 zesu_bounded_goal_within (kind : constr) :=
  let (_, whole) := zesu_bounded_budgets kind in
  if Int.le (ZesuSsz.Automation2.LinearFirstLia.zesu_linear_remaining whole (Control.goal ())) 0
  then Control.zero (Tactic_failure None) else ().

Ltac zesu_vm_compute_goal :=
  ltac2:(Control.enter (fun () => zesu_bounded_goal_within constr:(zesu_solver_vm)));
  vm_compute.
