From Coq Require Import ZArith.ZArith Lia.

(* The project's linear arithmetic solver. Automation tactics and hints call
   `zesu_lia`, never `lia`; Hooks redefines `zesu_lia` with the project solver
   and points `Lia.lia` at it for the library tactics that call `lia`.
   Importing a module re-adds the original body of each tactic it defines, so
   a caller that imports Coq's Lia (directly, or through stdpp or iris) after
   ZesuSsz.Automation2.All gets the library `Lia.lia` back; `zesu_lia` keeps
   the project solver, so the automation's own calls run the same proof. *)
Ltac zesu_lia := lia.
