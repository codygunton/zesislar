Require Import isla.riscv64.riscv64.
Require Import isla.automation.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
From iris.proofmode Require Import tactics.
From Coq Require Import Strings.String.

Definition zesu_source_register_post `{!islaG Sigma} `{!threadG}
    (key : string) (width : N) (continuation : base_val -> iProp Sigma)
    (value : base_val) : iProp Sigma :=
  match value with
  | Val_Bits bits =>
      match bvn_to_bv width bits with
      | Some word => ⌜ZesuSourceWitness key word⌝ -∗ continuation value
      | None => continuation value
      end
  | _ => continuation value
  end.

Section SourceRegisterResult.
Context `{!islaG Sigma} `{!threadG}.
Lemma zesu_wpaexp_source_register key width expression continuation :
  WPaexp expression {{ zesu_source_register_post key width continuation }}
  ⊢ WPaexp expression {{ continuation }}.
Proof.
  iIntros "Hread".
  iApply (wpae_wand with "Hread").
  iIntros (value) "Hcontinue".
  destruct value; simpl [zesu_source_register_post]; try iExact "Hcontinue".
  case_match; try iExact "Hcontinue".
  iApply "Hcontinue". iPureIntro. constructor.
Qed.
Print Assumptions zesu_wpaexp_source_register.
End SourceRegisterResult.
