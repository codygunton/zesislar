(* Prototype, not for merge: a `zesu_block` that never raises.

   The replay of the benchmark set found 239 steps where the block
   automation raised, every one `iStartProof: not a BI assertion`, every
   one in a module that imports `AllLegacy`: the legacy `zesu_block` starts
   with `iStartProof` and has no path for a pure goal. Inside the search
   the same thing happens one level down: a pass that leaves a pure side
   goal the finisher cannot close fails the whole iteration, and the
   iteration is rolled back, so the search stops for the Iris goal too.

   Here a pure goal is handed to the finisher, and when no solver closes
   it, it is shelved as a residual and the search goes on with the rest.
   `unshelve` returns every shelved goal at the end, so nothing is lost:
   a probe prints it as a residual, never as closed.

   Two entries, one per automation, because a legacy module names the
   legacy tactics and a current module names the current ones; the probe
   picks the entry by what the module imports. Nothing here is exported
   by `All.v` or by a rule set. *)

Require Import isla.isla.
From iris.proofmode Require Import environments proofmode.
Require ZesuSsz.Automation.Finish.
Require ZesuSsz.Automation.Legacy.Finish.

(* A pure goal: closed by the finisher, or shelved as a residual. *)
Ltac zesu_nr_keep finish := first [solve [finish] | shelve].

Ltac zesu_nr_step pass finish solve_instances :=
  tryif assert_succeeds iStartProof
  then (pass; try solve_instances;
        tryif assert_succeeds iStartProof then finish
        else zesu_nr_keep finish)
  else zesu_nr_keep finish.

Ltac zesu_nr_run pass finish solve_instances :=
  unshelve (repeat progress (zesu_nr_step pass finish solve_instances));
  try solve_instances.

Ltac zesu_nr_intros :=
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".

(* The current automation, rule set v1 or v2 as the module's imports say. *)
Ltac zesu_block_nr :=
  tryif iStartProof then (
    ZesuSsz.Automation.Finish.zesu_expose_code_lists;
    repeat first [progress iIntros (?) | progress iIntros "#?" |
      progress iIntros "?"];
    ZesuSsz.Automation.Finish.zesu_reduce_introduced_code_lists;
    repeat iDestruct select (_ ∗ _)%I as "[? ?]";
    zesu_nr_run ltac:(ZesuSsz.Automation.Finish.zesu_run_pass)
                ltac:(ZesuSsz.Automation.Finish.zesu_finish)
                ltac:(ZesuSsz.Automation.Finish.zesu_solve_instances))
  else first [solve [ZesuSsz.Automation.Finish.zesu_finish] | idtac].

(* The legacy automation, for a module that imports `AllLegacy`. *)
Ltac zesu_block_nr_legacy :=
  tryif iStartProof then (
    simpl;
    zesu_nr_intros;
    zesu_nr_run ltac:(ZesuSsz.Automation.Legacy.Finish.zesu_run_pass)
                ltac:(ZesuSsz.Automation.Legacy.Finish.zesu_finish)
                ltac:(ZesuSsz.Automation.Legacy.Finish.zesu_solve_instances))
  else first [solve [ZesuSsz.Automation.Legacy.Finish.zesu_finish] | idtac].
