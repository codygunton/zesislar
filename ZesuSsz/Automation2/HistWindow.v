(** History step across two spellings of one loaded word (generic rule).

   A block that loads a word from a byte list holds it as the load window
   `Z_to_bv w (little_endian_to_bv 8 (take c (drop s l)))`, where the start
   [s] may be a frame-offset chain `Z.to_nat (bv_unsigned (sp + ..) - (..))`;
   when the load fills an entry binder, the window replaces that binder in the
   block's own history too. The successor's history asks for the same word by
   byte positions `bv_concat .. (nth (s+c-1) l 0) .. (nth s l 0)`. The edge
   instance relates the two histories over one binder, so its search fails on
   the two spellings. Here: on a history conjunct `⌜zesu_hist S⌝ ∗ Q` whose
   plain step failed, every window of the context history over a list that
   [S] reads by position is restated by byte positions (its start as a
   literal first) in every hypothesis that holds it (the history and the
   named equation that defines the word, which the edge's new facts need),
   then the plain step runs again. Rewrites by proved equations only. *)

From iris.proofmode Require Import proofmode environments.
From stdpp Require Import base list bitvector.definitions.
From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.Hist.
Require ZesuSsz.Automation2.WrappedWord.
Require ZesuSsz.Automation2.BytePositionEquations.

(* One window of [P] over a list [S] reads by position, restated in every
   hypothesis that holds it: a literal start by byte positions, a
   frame-offset start as its literal. *)
Ltac zesu_hist_window_respell_one P S :=
  match P with
  | context [Z_to_bv ?w (little_endian_to_bv 8 (take ?c (drop ?s ?l)))] =>
      lazymatch S with context [List.nth _ l _] => idtac end;
      let W := constr:(Z_to_bv w (little_endian_to_bv 8 (take c (drop s l)))) in
      first
      [ ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_equation w c s l
          ltac:(fun Hw => repeat match goal with Hx : context [W] |- _ => rewrite Hw in Hx end)
      | lazymatch s with
        | Z.to_nat ?e =>
            ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_literal e
              ltac:(fun Hi => repeat match goal with Hx : context [W] |- _ => rewrite Hi in Hx end)
        end ]
  end.

(* The history conjunct after the plain step failed: head test on the goal,
   a context history holding a window over a list the successor reads by
   position, the windows restated, the plain step again. *)
Ltac zesu_hist_step_respelled :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (zesu_hist ?S)) _) =>
      match goal with
      | Hh : zesu_hist ?P |- _ =>
          match P with
          | context [little_endian_to_bv 8 (take _ (drop _ ?l))] =>
              lazymatch S with context [List.nth _ l _] => idtac end
          end;
          progress (repeat (lazymatch type of Hh with
                            | zesu_hist ?P2 => zesu_hist_window_respell_one P2 S
                            end));
          zesu_hist_step
      end
  end.
