Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitWords.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
From iris.proofmode Require Import environments.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeCode
 WriteSuccessExactPrefixCalls WriteSuccessExactSuffixBytesPayloadSpec.
Open Scope Z_scope.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Lemma exact_suffix_bytes_15910_payload_at `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15920
    (exactSuffixBytesPayloadReturnAt (BV 64 0x15920) 968 976
      sp data size oldS0 oldS1 bytes tail P) -∗
  instr_body 0x15910
    (exactSuffixBytesPayloadEntryAt 968 976 sp data size oldS0 oldS1 bytes tail P).
Proof.
  iIntros "#Hnative Hnext".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#Hcopy & #Houtput & #Hint & #Hbytes)".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & HoutCode & HcopyCode & HboolCode & HoptCode & Hlists & HbytesCode & HintCode & Hu256 & Hu128)".
  iStartProof; simpl.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (∃ _ : li_prod (iProp Sigma) _, _)%I => idtac
    end).
  iExists (exactSuffixBytesPayloadFrame 968 976 sp data size bytes P,
    tail, bytes, BV 64 0x15920, sp, size, data, tt)ₗ.
  zesu_run.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions exact_suffix_bytes_15910_payload_at.
