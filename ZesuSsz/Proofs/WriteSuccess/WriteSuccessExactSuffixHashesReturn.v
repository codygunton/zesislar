Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesEmit
  WriteSuccessExactSuffixHashesEmitHandoff WriteSuccessExactSuffixHashesModel.

Definition suffixReturnHeadShapes : list (reg_kind * valu_shape) :=
  [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)].
Definition suffixReturnRestShapes : list (reg_kind * valu_shape) :=
  (fun r => (KindReg r, BitsShape 64)) <$> ["x12";"x13";"x14";"x15";"x16"].

Definition suffixLoopCaller `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (source : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗ P ∗
   ⌜suffixLoopFacts sp pointer base total processed remaining source⌝ ∗
   instr_pre 0x158e0 (suffixLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@suffixLoopCaller) := I.

Lemma suffix_emit_to_tail `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base total processed remaining source tail (P : iProp Sigma) :
  suffixEmitPost sp (take 32 (drop (32 * processed) source))
    (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail)
    (suffixEmitCallerFrame sp pointer base source (32 * processed)
      (suffixLoopCaller sp pointer base total processed remaining source tail P)) -∗
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ suffixTailPayload sp pointer base total processed remaining source tail P ∗ True)%I.
Proof.
  unfold suffixEmitPost, suffixEmitFrame, suffixEmitCallerFrame, suffixLoopCaller.
  iIntros "(Hsys & Hra & H5 & H10 & H11 & Hrow & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & Hcaller & _)".
  iDestruct "Hcaller" as "(Hptr & Hregs & Hsource & %Hcursor & %Hbound & %Hbase & %Hend & %Halign & %Hlow & %Hhigh & Hloop & _)".
  iDestruct "Hloop" as "(H8 & HP & %Hfacts & Hexit & _)".
  have HrowLength : length (take 32 (drop (32 * processed) source)) = 32%nat by rewrite length_take length_drop; lia.
  have Haddress : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z by clear -Hlow Hhigh; bv_solve.
  iPoseProof (byte_array_forget with "Hrow") as "Hscratch".
  iEval (rewrite HrowLength Haddress) in "Hscratch".
  iDestruct (mem_mapsto_uninit_split 8 (bv_unsigned sp + 1744) (DfracOwn 1) 32 ltac:(lia) with "Hscratch") as "[H0 Hrest]".
  iDestruct (mem_mapsto_uninit_split 8 (bv_unsigned sp + 1744 + 8) (DfracOwn 1) 24 ltac:(lia) with "Hrest") as "[H1 Hrest]".
  iDestruct (mem_mapsto_uninit_split 8 (bv_unsigned sp + 1744 + 8 + 8) (DfracOwn 1) 16 ltac:(lia) with "Hrest") as "[H2 H3]".
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)]) with "[H10 H11]" as "Hhead".
  { iApply (reg_col_bv_list_shape [("x10", (sp + BV 64 1744)%bv); ("x11", BV 64 32)]). cbn. iFrame. }
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x10";"x11";"x12";"x13";"x14";"x15";"x16"])) with "[Hhead Hregs]" as "Hregs".
  { iApply (reg_col_mixed_collect [] suffixReturnHeadShapes suffixReturnRestShapes
      suffixWordRegisterShapes ltac:(vm_compute; reflexivity)). cbn. iFrame. }
  unfold suffixTailPayload, suffixLoopScratch.
  have -> : (bv_unsigned sp + 1744 + 8)%Z = (bv_unsigned sp + 1752)%Z by lia.
  have -> : (bv_unsigned sp + 1752 + 8)%Z = (bv_unsigned sp + 1760)%Z by lia.
  have -> : (bv_unsigned sp + 1760 + 8)%Z = (bv_unsigned sp + 1768)%Z by lia.
  iFrame. done.
Qed.
Print Assumptions suffix_emit_to_tail.
