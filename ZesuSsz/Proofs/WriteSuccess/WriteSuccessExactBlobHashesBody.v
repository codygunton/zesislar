Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutput WriteSuccessExactBlobHashesLoads16
  WriteSuccessExactBlobHashesLoadHandoff WriteSuccessExactBlobHashesInitialLoads
  WriteSuccessExactBlobHashesByteAssembly WriteSuccessExactBlobHashesEmit
  WriteSuccessExactBlobHashesEmitHandoff WriteSuccessExactBlobHashesOutputComposition.

Lemma blob_body_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (old26 : bv 64) sp a b c d tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15558 (blobEmitPost sp (take 32 (drop index bytes)) tail
    (blobEmitCallerFrame row count base bytes index P)) -∗
  instr_body 0x153d4 (blobLoads16Entry row base bytes index
    (blobLoad20Frame bytes index (blobUpperLoadFrame count bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗
       reg_col [(KindReg "x25", BitsShape 64)] ∗
       ("x26" ↦ᵣ RVal_Bits old26 ∗ (blobOutputResources sp a b c d (take 32 (drop index bytes)) tail P) ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H66 #H67 #H68 #H69 #H70 #H01 Hnext".
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1680)%bv (BV 64 32)
    (BV 64 0x15558) (take 32 (drop index bytes)) tail
    (blobEmitFrame sp (take 32 (drop index bytes))
      (blobEmitCallerFrame row count base bytes index P))))%I with "[]" as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_output_trace_correct with "H01"). }
  iPoseProof (blob_output_composed_correct row count base bytes index sp a b c d tail P
    with "[] Houtput Hnext") as "Hcall".
  { rewrite big_sepL_app. iSplit; last iExact "H70".
    iApply (big_sepL_submseteq with "H69"). apply sublist_submseteq, sublist_drop. }
  iApply (blob_byte_assembly_correct row count base bytes index old26
    (blobOutputResources sp a b c d (take 32 (drop index bytes)) tail P) with "H66 H67 H68 [] Hcall").
  iApply (big_sepL_submseteq with "H69"). apply sublist_submseteq, sublist_take.
Qed.
Print Assumptions blob_body_correct.
