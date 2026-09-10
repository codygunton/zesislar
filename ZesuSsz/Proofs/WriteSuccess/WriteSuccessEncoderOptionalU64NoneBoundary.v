From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Spec.

Definition zesuEncoderOptionalU64NoneAtTail
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  zesuEncoderBooleanCallSpec.

Global Instance : LithiumUnfold (@zesuEncoderOptionalU64NoneAtTail) := I.

Lemma zesu_encoder_optional_u64_none_to_tail
    `{!islaG Sigma} `{!threadG} :
  zesuEncoderOptionalU64NoneCallSpec -∗
  zesuEncoderOptionalU64NoneAtTail.
Proof.
  iStartProof. iIntros "Hspec".
  unpack_zesu_encoder_optional_u64_call_spec
    zesuEncoderOptionalU64NoneCallSpec.
  simpl in Hdataalign, Hdatamin, Hdatamax.
  subst tag.
  iDestruct (mem_mapsto_uninit_split 16 with "Hstack") as
    "[Hlower Hupper]"; first lia.
  have Hupperaddress :
      bv_unsigned sp - 32 + 16 = bv_unsigned sp - 16 by lia.
  iEval (rewrite Hupperaddress) in "Hupper".
  iPoseProof (zesu_c_call_ret_16_to_32 with "Hret") as "Hret16".
  iPoseProof (zesu_c_call_ret_frame with "Hret16 Hlower") as "Hret16".
  iPoseProof (zesu_c_call_ret_frame with "Hret16 Hvalue") as "Hret16".
  iPoseProof (zesu_c_call_ret_frame with "Hret16 Htagmem") as "Hret16".
  rewrite /zesuEncoderOptionalU64NoneAtTail
    /zesuEncoderBooleanCallSpec /zesu_c_call.
  iExists sp, ret.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iEval (simpl) in "Hupper".
  iFrame "Hsys Htmp R10".
  iExists b10. iSplit; first done.
  iFrame "R11". iExists b11. iSplit; first done.
  iFrame "R12". iExists b12. iSplit; first done.
  iFrame "R13". iExists b13. iSplit; first done.
  iFrame "R14". iExists b14. iSplit; first done.
  iFrame "R15". iExists b15. iSplit; first done.
  iFrame "R16". iExists b16. iSplit; first done.
  iFrame "R17". iExists b17. iSplit; first done.
  iFrame "R8". iSplit; first done.
  iFrame "R9". iSplit; first done.
  iFrame "R18". iSplit; first done.
  iFrame "R19". iSplit; first done.
  iFrame "R20". iSplit; first done.
  iFrame "R21". iSplit; first done.
  iFrame "R22". iSplit; first done.
  iFrame "R23". iSplit; first done.
  iFrame "R24". iSplit; first done.
  iFrame "R25". iSplit; first done.
  iFrame "R26". iSplit; first done.
  iFrame "R27 R1 R2 Hupper".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  iExists tail. iFrame.
Qed.

Lemma zesu_encoder_optional_u64_none_tail_body_adapter
    `{!islaG Sigma} `{!threadG} :
  instr_body 0x15c04 zesuEncoderOptionalU64NoneAtTail -∗
  instr_body 0x15c04 zesuEncoderOptionalU64NoneCallSpec.
Proof.
  iStartProof. iIntros "Htail".
  iApply (instr_pre_wand 0x15c04 0x15c04 false false with "Htail");
    [done | done |].
  iApply zesu_encoder_optional_u64_none_to_tail.
Qed.
