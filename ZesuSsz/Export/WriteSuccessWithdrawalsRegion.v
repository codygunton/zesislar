Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Export.WriteSuccessControl.
Require Import ZesuSsz.Generated.Level1.
Require Import isla.opsem.

(** The withdrawal loop occupies one interval of the writeSuccess
    execution range, including its handoff at 0x156e8. *)
Definition WriteSuccessWithdrawalsControl (theta : seq_local_state) : Prop :=
  exists pc sp ra,
    (0x15694 <= pc <= 0x156e8)%Z /\
    seq_regs theta !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
    seq_regs theta !! "x2" = Some (RVal_Bits sp) /\
    seq_regs theta !! "x1" = Some (RVal_Bits ra).

Lemma writeSuccessWithdrawalsPcInExecutionRange pc :
  (0x15694 <= pc <= 0x156e8)%Z ->
  PcInRanges writeSuccessExecutionPcRanges pc.
Proof.
  intros Hpc. exists 0x14d30, 0x15a14.
  split; [simpl; auto|lia].
Qed.

Lemma writeSuccessWithdrawalsPcNotTerminal pc :
  (0x15694 <= pc <= 0x156e8)%Z ->
  ~ PcInList writeSuccessExitPcs pc.
Proof.
  intros Hpc Hexit.
  unfold PcInList, writeSuccessExitPcs in Hexit.
  simpl in Hexit. destruct Hexit as [Hexit|[]]. lia.
Qed.

Lemma writeSuccessWithdrawalsControlFacts theta :
  WriteSuccessWithdrawalsControl theta ->
  WriteSuccessControlFacts theta.
Proof.
  intros [pc [sp [ra [Hrange [Hpc [Hsp Hra]]]]]].
  exists pc, sp, ra. repeat split; auto.
  apply writeSuccessWithdrawalsPcInExecutionRange. exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsControlNotTerminal theta :
  WriteSuccessWithdrawalsControl theta ->
  exists pc,
    seq_regs theta !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
    ~ PcInList writeSuccessExitPcs pc.
Proof.
  intros [pc [sp [ra [Hrange [Hpc [Hsp Hra]]]]]].
  exists pc. split; [exact Hpc|].
  apply writeSuccessWithdrawalsPcNotTerminal. exact Hrange.
Qed.

Print Assumptions writeSuccessWithdrawalsPcInExecutionRange.
Print Assumptions writeSuccessWithdrawalsPcNotTerminal.
Print Assumptions writeSuccessWithdrawalsControlFacts.
Print Assumptions writeSuccessWithdrawalsControlNotTerminal.
