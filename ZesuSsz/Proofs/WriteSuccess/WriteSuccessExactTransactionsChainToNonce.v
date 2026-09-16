Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsNonceCall WriteSuccessExactOptionalU64SomeBooleanResume
  WriteSuccessExactOptionalU64SomeJumpHandoff WriteSuccessExactOptionalU64NoneCallSpec
  WriteSuccessExactOptionalU64NoneEntry WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionChainNonceCaller `{!islaG Sigma} `{!threadG}
    (sp nonce : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 272) ↦ₘ nonce ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainNonceCaller) := I.

Definition transactionChainSomeNonceFrame `{!islaG Sigma} `{!threadG}
    (sp old8 : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗ "x8" ↦ᵣ RVal_Bits old8 ∗
   bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ bytes ∗ (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainSomeNonceFrame) := I.

Lemma transactions_chain_some_to_nonce `{!islaG Sigma} `{!threadG}
    (sp nonce old8 : bv 64) bytes tail (P : iProp Sigma) :
  optionalU64SomeExactPost sp (BV 64 0x150fc) old8
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce))) tail)
    (optionalU64SomeExactSourceFrame (sp + BV 64 1664)%bv bytes
      (transactionChainNonceCaller sp nonce P)) -∗
  instr_pre 0x15108 (transactionNoncePost sp nonce tail
    (transactionChainSomeNonceFrame sp old8 bytes P)) -∗
  transactionNonceEntry sp nonce (BV 64 0x150fc) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 8) tail
    (transactionChainSomeNonceFrame sp old8 bytes P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H6 & H8 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsource & Hcaller & _)".
  iDestruct "Hcaller" as "(Hnonce & %Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "Hregs".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionNonceEntry, transactionChainSomeNonceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_chain_some_to_nonce.

Definition transactionChainNoneNonceFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits (BV 64 0x15c08) ∗
   bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ bytes ∗ (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 280 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainNoneNonceFrame) := I.

Lemma transactions_chain_none_to_nonce `{!islaG Sigma} `{!threadG}
    (sp nonce : bv 64) bytes tail (P : iProp Sigma) :
  optionalU64NoneExactCallPost (sp + BV 64 1664)%bv sp (BV 64 0x150fc) bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce))) tail)
    (transactionChainNonceCaller sp nonce P) -∗
  instr_pre 0x15108 (transactionNoncePost sp nonce tail (transactionChainNoneNonceFrame sp bytes P)) -∗
  transactionNonceEntry sp nonce (BV 64 0x150fc) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 1) tail
    (transactionChainNoneNonceFrame sp bytes P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H6 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsource & Hcaller & _)".
  iDestruct "Hcaller" as "(Hnonce & %Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "Hregs".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionNonceEntry, transactionChainNoneNonceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_chain_none_to_nonce.

Lemma transactions_chain_some_nonce_continuation `{!islaG Sigma} `{!threadG}
    (sp nonce old8 : bv 64) bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_36.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15108 (transactionNoncePost sp nonce tail (transactionChainSomeNonceFrame sp old8 bytes P)) -∗
  □ instr_pre 0x150fc (optionalU64SomeExactPost sp (BV 64 0x150fc) old8
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce))) tail)
    (optionalU64SomeExactSourceFrame (sp + BV 64 1664)%bv bytes (transactionChainNonceCaller sp nonce P))).
Proof.
  iIntros "#Hcode #Hint #Houtput #Hnext".
  iPoseProof (transactions_nonce_call_correct sp nonce (BV 64 0x150fc)
    (BV 64 (mapIoContextAddress defaultMap)) (BV 64 8) tail (transactionChainSomeNonceFrame sp old8 bytes P)
    with "Hcode Hint Houtput") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_chain_some_to_nonce with "Hpost Hnext").
Qed.

Lemma transactions_chain_none_nonce_continuation `{!islaG Sigma} `{!threadG}
    (sp nonce : bv 64) bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_36.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15108 (transactionNoncePost sp nonce tail (transactionChainNoneNonceFrame sp bytes P)) -∗
  □ instr_pre 0x150fc (optionalU64NoneExactCallPost (sp + BV 64 1664)%bv sp (BV 64 0x150fc) bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce))) tail)
    (transactionChainNonceCaller sp nonce P)).
Proof.
  iIntros "#Hcode #Hint #Houtput #Hnext".
  iPoseProof (transactions_nonce_call_correct sp nonce (BV 64 0x150fc)
    (BV 64 (mapIoContextAddress defaultMap)) (BV 64 1) tail (transactionChainNoneNonceFrame sp bytes P)
    with "Hcode Hint Houtput") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_chain_none_to_nonce with "Hpost Hnext").
Qed.
Print Assumptions transactions_chain_some_nonce_continuation.
Print Assumptions transactions_chain_none_nonce_continuation.
