Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SealedCoverage.
From iris.proofmode Require Import environments.

(* A matching named bundle carries the words behind four witnesses. Open
   only a LithiumUnfold predicate that exposes all four requested slots. *)
Ltac zesu_open_four_word_scratch sp :=
  iMatchHyp ltac:(fun H source =>
    let head := get_head source in
    let _ := constr:(_ : LithiumUnfold head) in
    let expanded := eval cbv beta zeta delta [head] in source in
    lazymatch expanded with
    | context[((bv_unsigned sp + 1712) ↦ₘ _)%I] =>
      lazymatch expanded with
      | context[((bv_unsigned sp + 1720) ↦ₘ _)%I] =>
        lazymatch expanded with
        | context[((bv_unsigned sp + 1728) ↦ₘ _)%I] =>
          lazymatch expanded with
          | context[((bv_unsigned sp + 1736) ↦ₘ _)%I] =>
            let w0 := fresh "scratch0" in
            let w1 := fresh "scratch1" in
            let w2 := fresh "scratch2" in
            let w3 := fresh "scratch3" in
            iEval (unfold head) in H;
            iDestruct H as (w0 w1 w2 w3) "(? & ? & ? & ? & _)"
          end
        end
      end
    end).

(* Pack the four saved words of writeSuccessStorageKeysScratch. The goal
   shape and all four addresses must match before the witnesses are chosen. *)
Ltac zesu_pack_four_word_scratch :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _
      (li_prod (bv 64) (li_prod (bv 64) (li_prod (bv 64)
        (li_prod (bv 64) unit)))) ?body) =>
      lazymatch body with
      | context[((bv_unsigned ?sp + 1712) ↦ₘ _)%I] =>
        lazymatch body with context[((bv_unsigned sp + 1720) ↦ₘ _)%I] =>
        lazymatch body with context[((bv_unsigned sp + 1728) ↦ₘ _)%I] =>
        lazymatch body with context[((bv_unsigned sp + 1736) ↦ₘ _)%I] =>
          first [iSelect ((bv_unsigned sp + 1712) ↦ₘ _)%I
                   ltac:(fun _ => idtac)
                |zesu_open_four_word_scratch sp];
          iSelect ((bv_unsigned sp + 1712) ↦ₘ _)%I ltac:(fun _ => idtac);
          iSelect ((bv_unsigned sp + 1720) ↦ₘ _)%I ltac:(fun _ => idtac);
          iSelect ((bv_unsigned sp + 1728) ↦ₘ _)%I ltac:(fun _ => idtac);
          iSelect ((bv_unsigned sp + 1736) ↦ₘ _)%I ltac:(fun _ => idtac);
          iExists (_, _, _, _, tt)ₗ;
          red_li_prod; iFrame
        end end end
      end
  end.

Class ZesuStepFourWordScratch : Prop := zesu_step_four_word_scratch : True.

Ltac zesu_pack_four_word_scratch_if_enabled :=
  let _ := constr:(_ : ZesuStepFourWordScratch) in
  zesu_pack_four_word_scratch.
