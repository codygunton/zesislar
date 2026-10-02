Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputWhole.

Definition writeOutputContract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 0 (fun args sp RET => ∃ (bytes : list (bv 8)) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (args !!! 0%nat) (args !!! 1%nat) bytes tail) ∗
    ⌜bv_unsigned (args !!! 1%nat) = Z.of_nat (length bytes)⌝ ∗
    RET (fun _ => bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@writeOutputContract) := I.
#[local] Typeclasses Opaque writeOutputContract.

Definition writeOutputContractFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (regs : list valu) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp - 0) ↦ₘ? 0 ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tl tmp_registers) ∗
   reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"]))%I.
Global Instance : LithiumUnfold (@writeOutputContractFrame) := I.
Global Typeclasses Opaque writeOutputContractFrame.

Lemma write_output_contract_return `{!islaG Sigma} `{!threadG}
    (data size ret sp : bv 64) (bytes : list (bv 8))
    (tail : spec) (regs : list valu) :
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ writeOutputContractFrame sp regs ∗ True) -∗
  zesu_call_ret 0 regs ret sp (fun _ => bv_unsigned data ↦ₘ∗ bytes ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True).
Proof.
  iIntros "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & HF & _)".
  iEval (unfold writeOutputContractFrame) in "HF".
  iDestruct "HF" as "(H2 & Hstack & Htemps & Hsaved & Hargs)".
  iEval (unfold zesu_call_ret). iFrame "Hsys Hsaved".
  iEval (rewrite /tmp_registers /= !reg_col_cons reg_col_nil) in "Htemps".
  iDestruct "Htemps" as "(H6 & H7 & H28 & H29 & H30 & H31 & _)".
  iEval (rewrite /= !reg_col_cons reg_col_nil) in "Hargs".
  iDestruct "Hargs" as "(H12 & H13 & H14 & H15 & H16 & H17 & _)".
  rewrite /tmp_registers /= !reg_col_cons reg_col_nil.
  iFrame "H6 H7 H28 H29 H30 H31 H12 H13 H14 H15 H16 H17".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "H1 H2 H5 H10 H11 Hstack Hbytes Hmmio Htrace".
  iSplit. { repeat iSplit; iPureIntro; done. }
  iExists data. iSplit; [done |]. iExists size. done.
Qed.

Lemma write_output_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 writeOutputContract.
Proof.
  iIntros "Hcode". rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold writeOutputContract) in "Hentry".
  zesu_unpack_call "Hentry". subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (bytes tail) "(Hbytes & Hmmio & Htrace & %Hlength & Hreturn)".
  iEval (rewrite /tmp_registers /= reg_col_cons) in "Htmp".
  iDestruct "Htmp" as "[H5 Htemps]".
  iDestruct "H5" as (old5) "[%Hshape5 H5]".
  apply valu_has_bits_shape in Hshape5. destruct Hshape5 as [b5 ->].
  set (regs := [r8; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]).
  iAssert (writeOutputContractFrame sp regs)
    with "[R2 Hstack Htemps R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R12 R13 R14 R15 R16 R17]" as "HF".
  { rewrite /writeOutputContractFrame /regs. iFrame "R2 Hstack Htemps".
    rewrite /= !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iPoseProof (write_output_whole_correct b10 b11 ret (bv_unsigned b10) 0
    (length bytes) bytes tail (writeOutputContractFrame sp regs) with "Hcode") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply "Hbody".
  iEval (unfold writeOutputWholeSpec). iExists b5.
  rewrite drop_0 firstn_all. iFrame "Hsys R1 H5 R10 R11 Hbytes Hmmio Htrace HF".
  repeat iSplit; try (iPureIntro; first [done | lia]).
  { iPureIntro. rewrite Hlength -Z_nat_N Nat2Z.id; done. }
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hreturn"); [done | done |].
  iApply write_output_contract_return.
Qed.

Print Assumptions write_output_contract_correct.
