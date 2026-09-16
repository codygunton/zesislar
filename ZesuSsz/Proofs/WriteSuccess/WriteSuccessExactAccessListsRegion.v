Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactAccessListsInitialLoop WriteSuccessExactAccessListsLoopNative
  WriteSuccessExactAccessListsReturnContinuation WriteSuccessExactAccessListsReturnLoopEntry
  WriteSuccessExactAccessListsReturnCount WriteSuccessExactAccessListsSpec
  WriteSuccessExactAccessListsControl WriteSuccessExactAccessListsControlEntry
  WriteSuccessAccessListsSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma access_exact_initial_region_correct `{!islaG Sigma} `{!threadG}
    sp base entries bytes storedIndex x19 savedX22 data old11 x22 x27 tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (accessReturnCountPost sp savedX22 tail
    (accessReturnLoopFrame sp base entries bytes x19 P)) -∗
  instr_body 0x151d0 (accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries))) old11 data
    (accessControlFrame sp base entries [] entries bytes storedIndex x19 savedX22 data x22 x27
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
      (accessReturnRuntimeBounds sp P))).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert (□ instr_body 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
    x19 savedX22 (accessReturnRuntimeBounds sp P)))%I as "#Hreturn".
  { iModIntro. iApply (access_return_loop_continuation with "[] Hint Houtput Hnext").
    iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iAssert (□ instr_pre 0x151d4 (writeSuccessExactAccessListsState sp base entries [] entries bytes
    storedIndex x19 savedX22 data x22 x27
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
    (accessReturnRuntimeBounds sp P)))%I as "#Hloop".
  { iModIntro.
    iPoseProof (access_exact_loop_native_correct with
      "[] [] [] [] [] [] [] [] [] [] [] Hmemcpy Hint Houtput Hreturn") as "Hbody".
    all: try (iApply instr_lookup_collect; last iExact "Hlookup"; repeat constructor; reflexivity).
    iApply (instr_pre_wand 0x151d4 0x151d4 false true with "Hbody"); [done | done |]. iIntros "$". }
  iApply (access_initial_to_loop_correct with "[] Hloop").
  iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity.
Qed.
Print Assumptions access_exact_initial_region_correct.
