Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_02 Require Import instrs.
From IslaTraces.write_success_09 Require Import a14d7c_spec.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadBlockAdapter.

Import ListNotations.

Local Instance : LithiumUnfold (@writeSuccessLoadBlockAdapterSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadRegisterResources) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadMemoryResources) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadTerminal) := I.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessCallerOutputEvents
    (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

Definition writeSuccessCallerOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessCallerOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessCallerOtherRegisters.

Lemma Z_to_nat_add_sub_base (base offset : Z) :
  Z.to_nat (base + offset - base) = Z.to_nat offset.
Proof. f_equal. lia. Qed.

Lemma Z_to_nat_offset_sub (base high low : Z) :
  Z.to_nat (base + high - (base + low)) = Z.to_nat (high - low).
Proof. f_equal. lia. Qed.

#[local] Hint Rewrite Z_to_nat_add_sub_base Z_to_nat_offset_sub :
  write_success_offsets.


Lemma write_success_to_load_block `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (decodedBytes : list (bv 8)) (tail : spec) (P : iProp Sigma)
    (Hdecoded : bv_unsigned decoded = (bv_unsigned sp + 0x20)%Z)
    (Hspalign : bv_extract 0 4 sp = BV 4 0)
    (Hspmin : (0x20000880 <= bv_unsigned sp)%Z)
    (Hspmax : (bv_unsigned sp + 0x7d0 < 0x40000000)%Z) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_pre 0x14e00
    (writeSuccessLoadTerminal (sp - 2000) (sp + 32)
      (u64s_of_bytes 16 (take 128 (drop 720 decodedBytes)))
      [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
       RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
       RVal_Bits s9; RVal_Bits s10; RVal_Bits s11]) -∗
  instr_body 0x14d7c
    (write_success_prologue_exit sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11
       ((bv_unsigned sp - 0x7d0) ↦ₘ? 1896 ∗
        bv_unsigned decoded ↦ₘ∗ decodedBytes ∗
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (writeSuccessCallerOutputEvents (BV 64 0x179c5) (BV 64 6) tail) ∗
        P ∗
        ⌜length decodedBytes = 848%nat⌝ ∗
        ⌜(0x20000000 <= bv_unsigned decoded)%Z⌝ ∗
        ⌜(bv_unsigned decoded + 848 < 0x40000000)%Z⌝ ∗
        instr_pre 0x14d10 True ∗ True)%I).
Proof.
  move => *.
  iStartProof.
  iIntros
    "_ #Hlookup #HspecCode #HmemcpyCode #HoutputCode #Hmemcpy #Houtput Hcontinue".
  assert (Hdecoded_bv : decoded = (sp + BV 64 32)%bv).
  { apply bv_eq. rewrite bv_add_unsigned bv_wrap_small.
    - exact Hdecoded.
    - pose proof (bv_unsigned_in_range 64 sp).
      change (0 <= bv_unsigned sp + 32 < 18446744073709551616)%Z.
      lia. }
  subst decoded.
  assert (Hdecoded720 :
    Z.to_nat (bv_unsigned (sp + 32) + 720 - bv_unsigned (sp + 32)) =
      720%nat).
  { replace (bv_unsigned (sp + 32) + 720 - bv_unsigned (sp + 32))%Z
      with 720%Z by lia. reflexivity. }
  have HspSub2000 :
      bv_unsigned (sp - 2000) = (bv_unsigned sp - 2000)%Z.
  { rewrite bv_sub_unsigned bv_wrap_small.
    - reflexivity.
    - pose proof (bv_unsigned_in_range 64 sp).
      change (0 <= bv_unsigned sp - 2000 < 18446744073709551616)%Z.
      lia. }
  iPoseProof "Hlookup" as "Hdirect".
  iEval (rewrite /instr_lookup_resources) in "Hdirect".
  iPoseProof ("Hdirect" $! 0x14d7c with "[]") as "#Hinstr14d7c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a14d7c. done. }
  iPoseProof (IslaTraces.write_success_09.a14d7c_spec.a14d7c_spec
    0x14d7c with "Hinstr14d7c") as "Hjalr".
  iClear "Hdirect".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hmemcpy Houtput Hcontinue".
  iDestruct "Hentry" as
    "(Hsys & Hother & H1 & H2 & H8 & H9 & H18 & H19 & H20 & H21 &
      H22 & H23 & H24 & H25 & H26 & H27 & H10 & H11 & H12 & Hsaved & Hpre & _)".
  iDestruct "Hpre" as
    "(Hstack & HdecodedMemory & Hmmio & Htrace & HP & %Hlength & %HsrcMin & %HsrcMax & Hreturn & _)".
  have HdecodedRegionBound : (720 + 16 * 8 <= length decodedBytes)%nat by lia.
  iDestruct (zesu_byte_array_word_region (bv_unsigned (sp + 32))
    (DfracOwn 1) decodedBytes 720 16 HdecodedRegionBound
    with "HdecodedMemory") as "(HdecodedPrefix & HdecodedWords & HdecodedSuffix)".
  set (decodedTail := take 128 (drop 720 decodedBytes)).
  set (decodedWords := u64s_of_bytes 16 decodedTail).
  iAssert (□ instr_pre 0x14d80 writeSuccessLoadBlockAdapterSpec)%I as
    "#HloadBlock".
  { iApply write_success_load_block_adapter_pre. iExact "HspecCode". }
  iClear "HspecCode".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0xfd78). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget : bv_unsigned
    (bv_or (bv_and ((BV 64 0xfd78) + BV 64 1116)%bv
      (BV 64 18446744073709551614)) (BV 64 0)) = 0x101d4 by bv_solve.
  rewrite Htarget.
  iApply (instr_pre_wand 0x101d4 0x101d4 true true with "Hmemcpy"); [done | done |].
  iIntros "Hcallee".
  iDestruct "Hcallee" as "(Hsys & H1 & _)".
  iEval (unfold zesuMemcpyCallSpec, zesu_c_call).
  zesu_run_until ltac:(fun _ => lazymatch goal with
    |- envs_entails _ (∃ x : list valu *ₗ list (bv 64) *ₗ
      bv 64 *ₗ bv 64 *ₗ bv 64 *ₗ bv 64 *ₗ (), _) => idtac
  end).
  liInst (fun x =>
    x.1ₗ = [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
      RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
      RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] /\
    x.2ₗ = decodedWords /\ x.5ₗ = (sp + 32)%bv /\ x.6ₗ = (sp - 2000)%bv).
  zesu_run.
  Unshelve. all: try zesu_handoff.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try zesu_frame_handoff.
  Unshelve. all: try zesu_finish.
  Unshelve.
  all: try (apply bv_add_32_mod_8_zero; assumption).
  all: try (apply bv_sub_2000_mod_8_zero; assumption).
  all: try (cbn; rewrite length_take; lia).
  all: try (rewrite HspSub2000;
    bv_simplify_arith Hspalign; unfold bv_wrap, bv_modulus in Hspalign;
    cbn in Hspalign; rewrite Zminus_mod Hspalign; vm_compute).
  all: try reflexivity.
  all: try (change (720 <= Z.of_nat (length (take 720 decodedBytes)))%Z;
    rewrite length_take Hlength; lia).
Qed.
Print Assumptions write_success_to_load_block.
