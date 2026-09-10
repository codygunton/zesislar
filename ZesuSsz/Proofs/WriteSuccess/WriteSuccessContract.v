From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_02 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockAdapter.

Import ListNotations.

Local Instance : LithiumUnfold (@writeSuccessLoadBlockAdapterSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadRegisterResources) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadMemoryResources) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadTerminal) := I.

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

Ltac run_write_success_until_load_block :=
  lazymatch goal with
  | |- instr_body 0x14d80 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | liAStep ];
      run_write_success_until_load_block
  end.

Ltac expose_write_success_decoded_memory decoded decodedBytes :=
  first
    [ iRename select (bv_unsigned decoded ↦ₘ∗ decodedBytes)%I
        into "HdecodedMemory"
    | liAStep;
      expose_write_success_decoded_memory decoded decodedBytes ].

Ltac expose_write_success_decoded_length decodedBytes :=
  lazymatch goal with
  | _ : length decodedBytes = _ |- _ => idtac
  | _ => liAStep; expose_write_success_decoded_length decodedBytes
  end.

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
  expose_write_success_decoded_memory (sp + 32)%bv decodedBytes.
  expose_write_success_decoded_length decodedBytes.
  have HdecodedRegionBound : (720 + 128 <= length decodedBytes)%nat by lia.
  unfold IPM_JANNO, LET_GOAL.
  pose proof (mem_mapsto_array_region 8%N (bv_unsigned (sp + 32))
    (DfracOwn 1) decodedBytes 720 128 HdecodedRegionBound) as HsplitLemma.
  iAssert (
    bv_unsigned (sp + 32) ↦ₘ∗ take 720 decodedBytes ∗
    (bv_unsigned (sp + 32) + 720) ↦ₘ∗
      take 128 (drop 720 decodedBytes) ∗
    (bv_unsigned (sp + 32) + 848) ↦ₘ∗ drop 848 decodedBytes)%I
    with "[HdecodedMemory]" as "Hsplit".
  { iApply HsplitLemma. iExact "HdecodedMemory". }
  iDestruct "Hsplit" as
    "[HdecodedPrefix [HdecodedTail HdecodedSuffix]]".
  set (decodedTail := take 128 (drop 720 decodedBytes)).
  set (decodedWords := u64s_of_bytes 16 decodedTail).
  have HdecodedTailLength : length decodedTail = 128%nat.
  { rewrite /decodedTail length_take length_drop. lia. }
  have HdecodedWordsBytes : bytes_of_u64s decodedWords = decodedTail.
  { apply bytes_of_u64s_of_bytes. exact HdecodedTailLength. }
  iEval (rewrite -HdecodedWordsBytes) in "HdecodedTail".
  iDestruct (mem_mapsto_bytes_to_u64_array with "HdecodedTail") as
    "HdecodedWords".
  iEval (cbn) in "HdecodedWords".
  iAssert (□ instr_pre 0x14d80 writeSuccessLoadBlockAdapterSpec)%I as
    "#HloadBlock".
  { iApply write_success_load_block_adapter_pre. iExact "HspecCode". }
  iClear "HspecCode".
  repeat first
    [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
    | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
    | liAStep
    | progress prepare_sidecond
    | bv_solve
    | lia ].
  Unshelve.
  all: try (iExists
    ([RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
      RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
      RVal_Bits s9; RVal_Bits s10; RVal_Bits s11],
     decodedWords, b11, b10, (sp + 32)%bv, (sp - 2000)%bv, tt)ₗ).
  all: try iSplit.
  all: try (iEval (unfold writeSuccessLoadRegisterResources); iFrame).
  all: try (iEval (unfold writeSuccessLoadMemoryResources;
    rewrite HspSub2000); iFrame).
  all: try (repeat iSplit; try iPureIntro).
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try (rewrite bv_sub_unsigned bv_wrap_small;
    [ unfold bv_wrap, bv_modulus in Hspalign; cbn in Hspalign;
      rewrite Zminus_mod Hspalign; vm_compute
    | pose proof (bv_unsigned_in_range 64 sp); lia ]).
  all: try (bv_simplify Hspalign; bv_solve).
  all: try bv_solve.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try (bv_simplify Hspalign; bv_solve).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try rewrite Hdecoded720.
  all: try (autorewrite with write_success_offsets; cbn;
    rewrite !length_drop; lia).
  Unshelve.
  all: try rewrite Hdecoded720.
  all: try (autorewrite with write_success_offsets; cbn;
    rewrite !length_drop; lia).
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try (apply bv_add_32_mod_8_zero; assumption).
  all: try (rewrite <- HspSub2000;
    apply bv_sub_2000_mod_8_zero; assumption).
  all: try (change (720 <= length (take 720 decodedBytes))%nat;
    rewrite length_take; lia).
  all: try (change (720 <= Z.of_nat (length (take 720 decodedBytes)))%Z;
    rewrite length_take; lia).
  all: iExact "Hcontinue".
Qed.
