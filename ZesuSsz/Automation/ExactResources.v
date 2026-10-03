Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ResourceGroups.

(* Match one owned resource at a time. Preserve all unmatched ownership. *)
Ltac zesu_frame_exact_head :=
lazymatch goal with
| |- environments.envs_entails _ (?requestedHead ∗ ?requestedRest)%I =>
  first [
    iMatchHyp ltac:(fun H owned =>
      unify owned requestedHead; iRename H into "Hselected"; iSplitL "Hselected"; [iExact "Hselected" | idtac])
  | lazymatch requestedHead with
    | ⌜?fact⌝%I => iSplitR; [iPureIntro; solve [assumption | reflexivity | lia] | idtac]
    | emp%I => iSplitR; [iEmpIntro | idtac]
    | True%I => iSplitR; [done | idtac]
    end]
| |- environments.envs_entails _ True%I => done
end.

Ltac zesu_frame_exact_resources := repeat zesu_frame_exact_head.
