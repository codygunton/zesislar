Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Export ZesuSsz.Automation.OptionalU64CallFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderOptionalU64Call.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanResume.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeJumpHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Definition encoderOptionalU64Contract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 32 (fun args sp RET => ∃ (bytes : list (bv 8)) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
    ⌜encoderOptionalU64Valid (args !!! 0%nat) bytes⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned (args !!! 0%nat)⌝ ∗
    ⌜bv_unsigned (args !!! 0%nat) + Z.of_nat (length bytes) < machineRamEnd defaultMap⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (match encoderOptionalU64Outcome bytes with
      | Some value => writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
          (writeSuccessBooleanWordPayload (BV 64 1))
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
            (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
      | None => writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
          (writeSuccessBooleanWordPayload (BV 64 0)) tail
      end) ∗
    RET (fun _ => bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@encoderOptionalU64Contract) := I.
#[local] Typeclasses Opaque encoderOptionalU64Contract.

Definition encoderOptionalU64ContractFrame `{!islaG Sigma} `{!threadG}
    (regs : list valu) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    ["x7"; "x28"; "x29"; "x30"; "x31"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"]) ∗
   reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
    ["x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs))%I.
#[local] Instance : LithiumUnfold (@encoderOptionalU64ContractFrame) := I.

Lemma encoder_optional_u64_contract_frame `{!islaG Sigma} `{!threadG}
    (r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : valu)
    (b12 b13 b14 b15 b16 b17 : bv 64) :
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "x9" ↦ᵣ r9 ∗ "x18" ↦ᵣ r18 ∗ "x19" ↦ᵣ r19 ∗ "x20" ↦ᵣ r20 ∗
  "x21" ↦ᵣ r21 ∗ "x22" ↦ᵣ r22 ∗ "x23" ↦ᵣ r23 ∗ "x24" ↦ᵣ r24 ∗
  "x25" ↦ᵣ r25 ∗ "x26" ↦ᵣ r26 ∗ "x27" ↦ᵣ r27 ∗
  "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
  "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
  "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗ True -∗
  ∃ x5 x6 : bv 64, "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
    encoderOptionalU64ContractFrame [r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27].
Proof.
  iIntros "(Htmp & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R12 & R13 & R14 & R15 & R16 & R17 & _)".
  iEval (rewrite /tmp_registers /= !reg_col_cons reg_col_nil) in "Htmp".
  iDestruct "Htmp" as "(H5 & H6 & H7 & H28 & H29 & H30 & H31 & _)".
  iDestruct "H5" as (v5 Hv5) "H5". apply valu_has_bits_shape in Hv5. destruct Hv5 as [x5 ->].
  iDestruct "H6" as (v6 Hv6) "H6". apply valu_has_bits_shape in Hv6. destruct Hv6 as [x6 ->].
  iExists x5, x6. iFrame "H5 H6".
  iEval (unfold encoderOptionalU64ContractFrame). rewrite /= !reg_col_cons reg_col_nil.
  iFrame. repeat iSplit; iPureIntro; done.
Qed.
Print Assumptions encoder_optional_u64_contract_frame.

Lemma encoder_optional_u64_contract_some_return `{!islaG Sigma} `{!threadG}
    (pointer sp ret s0 : bv 64) (bytes : list (bv 8)) (tail : spec) (r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : valu) :
  optionalU64SomeExactPost sp ret s0 tail
    (optionalU64SomeExactSourceFrame pointer bytes (encoderOptionalU64ContractFrame [r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27])) -∗
  zesu_call_ret 32 [RVal_Bits s0; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27] ret sp
    (fun _ => bv_unsigned pointer ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True).
Proof.
  iEval (unfold optionalU64SomeExactPost, optionalU64SomeExactSourceFrame,
    encoderOptionalU64ContractFrame, zesu_call_ret). zesu_block.
Qed.
Print Assumptions encoder_optional_u64_contract_some_return.

Lemma encoder_optional_u64_contract_none_return `{!islaG Sigma} `{!threadG}
    (pointer sp ret s0 : bv 64) (bytes : list (bv 8)) (tail : spec) (r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : valu) :
  optionalU64NoneExactCallPost pointer sp ret bytes tail
    ("x8" ↦ᵣ RVal_Bits s0 ∗ encoderOptionalU64ContractFrame [r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]) -∗
  zesu_call_ret 32 [RVal_Bits s0; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27] ret sp
    (fun _ => bv_unsigned pointer ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True).
Proof.
  iEval (unfold optionalU64NoneExactCallPost, optionalU64NoneObjectFrame,
    encoderOptionalU64ContractFrame, zesu_call_ret). zesu_block.
Qed.
Print Assumptions encoder_optional_u64_contract_none_return.

Lemma encoder_optional_u64_contract_return `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (regs : list valu) (ret sp : bv 64)
    (Q : list (bv 64) -> iProp Sigma) (post : iProp Sigma) :
  (post -∗ zesu_call_ret stackSize regs ret sp Q) -∗
  instr_pre'_def true (bv_unsigned ret) (zesu_call_ret stackSize regs ret sp Q) -∗
  instr_pre (bv_unsigned ret) post.
Proof.
  iIntros "Hpost Hreturn". iEval (rewrite -instr_pre'_eq) in "Hreturn".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hreturn"); [done | done |]. iExact "Hpost".
Qed.

Lemma encoder_optional_u64_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 encoderOptionalU64Contract.
Proof.
  iIntros "#Hoptional #Hboolean #Hint #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold encoderOptionalU64Contract) in "Hentry". zesu_unpack_call "Hentry".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (bytes tail)
    "(Hsource & %Hvalid & %Hlower & %Hupper & Hmmio & Htrace & Hreturn)".
  apply valu_has_bits_shape in Hr8. destruct Hr8 as [s0 ->].
  iDestruct (encoder_optional_u64_contract_frame r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
    b12 b13 b14 b15 b16 b17 with
    "[$Htmp $R9 $R18 $R19 $R20 $R21 $R22 $R23 $R24 $R25 $R26 $R27 $R12 $R13 $R14 $R15 $R16 $R17]")
    as (x5 x6) "(H5 & H6 & HF)".
  set (regs := [r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]).
  destruct (bytes !! 8%nat) as [tag|] eqn:Htag.
  - rewrite /encoderOptionalU64Valid Htag in Hvalid.
    iEval (rewrite /encoderOptionalU64Outcome Htag /=) in "Htrace".
    destruct (decide (tag = BV 8 0)) as [Hzero|Hnonzero].
    + subst tag.
      iPoseProof (optional_u64_none_exact_call_correct b10 sp ret x5 x6 b11 bytes tail
        ("x8" ↦ᵣ RVal_Bits s0 ∗ encoderOptionalU64ContractFrame regs)%I
        with "Hoptional Hboolean Houtput") as "Hbody".
      rewrite instr_pre'_eq. iApply "Hbody".
      iEval (unfold optionalU64NoneExactCallEntry).
      iFrame "Hsys R1 R2 H5 H6 R10 R11 Hstack Hsource Hmmio Htrace R8 HF".
      repeat iSplit; try (iPureIntro; naive_solver).
      all: try (iPureIntro; bv_solve).
      iApply (encoder_optional_u64_contract_return with "[] Hreturn").
      rewrite /regs. iApply encoder_optional_u64_contract_none_return.
    + destruct Hvalid as [Hlength Hpointer].
      set (value := Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))).
      iPoseProof (optional_u64_some_exact_call_correct b10 value sp ret x5 x6 s0 b11
        tag bytes tail (encoderOptionalU64ContractFrame regs)
        with "Hoptional Hboolean Hint Houtput") as "Hbody".
      rewrite instr_pre'_eq. iApply "Hbody".
      iEval (unfold optionalU64SomeExactCallEntry, optionalU64SomeExactCallContext).
      iFrame "Hsys R1 R2 H5 H6 R8 R10 R11 Hstack Hsource Hmmio Htrace HF".
      repeat iSplit; try (iPureIntro; naive_solver).
      all: try (iPureIntro; bv_solve).
      iApply (encoder_optional_u64_contract_return with "[] Hreturn").
      rewrite /regs. iApply encoder_optional_u64_contract_some_return.
  - rewrite /encoderOptionalU64Valid Htag in Hvalid. contradiction.
Qed.
Print Assumptions encoder_optional_u64_contract_correct.
