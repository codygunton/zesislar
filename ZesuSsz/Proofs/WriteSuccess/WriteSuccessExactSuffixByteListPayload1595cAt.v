Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactPrefixCalls
  WriteSuccessByteLists WriteSuccessExactByteLists WriteSuccessExactByteListsSpec
  WriteSuccessObservation WriteSuccessOutputSemantic.
Import ListNotations.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixByteListPayloadAtSpec.
Lemma exact_suffix_1595c_payload_at `{!islaG Sigma} `{!threadG}
    (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) (Q : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15960
    (exactSuffixByteListReturnAt (BV 64 0x15960) sp pointer count items tail s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Q) -∗
  instr_body 0x1595c
    (exactSuffixByteListEntryAt (BV 64 0x15958) sp pointer count items tail s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Q).
Proof.
  iIntros "#Hnative #Hnext".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#Hcopy & #Houtput & #Hint & #Hbytes)".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & HoutCode & HcopyCode & HboolCode & HoptCode & Hlists & HbytesCode & HintCode & Hu256 & Hu128)".
  iAssert (□ instr_pre 0x15c10 encoderByteListsExactCallSpec)%I with "[]" as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (byte_lists_exact_correct with "Hlists Hint Hbytes"). }
  iStartProof; simpl.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (∃ _ : li_prod spec (li_prod (list ByteListItem) unit), _)%I => idtac
    end).
  iExists (tail, items, tt)ₗ.
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (instr_pre _ _) => idtac
    end).
  liShow.
  iApply (instr_pre_wand 0x15960 (bv_unsigned LET) true true with "Hnext");
    [done | subst LET; bv_solve |].
  iIntros "Hpost".
  rewrite /exactSuffixByteListReturnAt.
  iFrame "Hpost". iFrame.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions exact_suffix_1595c_payload_at.
