Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Compliance.DecodeItemCallSpec.

(* The two specs differ only in which identical machine_call they name. *)
Lemma decodeItemCallSpec2_eq `{!islaG Sigma} `{!threadG} :
  @decodeItemCallSpec2 Sigma _ _ = @decodeItemCallSpec Sigma _ _.
Proof. reflexivity. Qed.

Lemma decodeItemCallSpec2_correct `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ instr_body decodeItemEntry decodeItemCallSpec2.
Proof. rewrite decodeItemCallSpec2_eq. apply decodeItemCallSpec_correct. Qed.
