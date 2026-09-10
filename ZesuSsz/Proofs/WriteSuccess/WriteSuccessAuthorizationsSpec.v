From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopMemory.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Fixpoint writeSuccessAuthorizationsEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
            (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
                (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
                  (writeSuccessAuthorizationsEvents sp count tail))))))
  end.

Inductive writeSuccessAuthorizationsPhase :=
  | AuthorizationsFirstU256
  | AuthorizationsOutput
  | AuthorizationsFirstInt
  | AuthorizationsSecondInt
  | AuthorizationsSecondU256
  | AuthorizationsThirdU256
  | AuthorizationsTail.

Definition writeSuccessAuthorizationsPhaseEvents
    (phase : writeSuccessAuthorizationsPhase) (sp : bv 64)
    (remaining : nat) (tail : spec) : spec :=
  match phase with
  | AuthorizationsFirstU256 =>
      writeSuccessAuthorizationsEvents sp (S remaining) tail
  | AuthorizationsOutput =>
      writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
            (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
                (writeSuccessAuthorizationsEvents sp remaining tail)))))
  | AuthorizationsFirstInt =>
      writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
            (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
              (writeSuccessAuthorizationsEvents sp remaining tail))))
  | AuthorizationsSecondInt =>
      writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
            (writeSuccessAuthorizationsEvents sp remaining tail)))
  | AuthorizationsSecondU256 =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
          (writeSuccessAuthorizationsEvents sp remaining tail))
  | AuthorizationsThirdU256 =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
        (writeSuccessAuthorizationsEvents sp remaining tail)
  | AuthorizationsTail => writeSuccessAuthorizationsEvents sp remaining tail
  end.

Definition writeSuccessAuthorizationsOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
   "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessAuthorizationsOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessAuthorizationsOtherRegisters.

Definition writeSuccessAuthorizationsScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsScratch) := I.

Definition writeSuccessAuthorizationsCopiedScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ current : list (bv 8),
    (bv_unsigned sp + 1744) ↦ₘ∗ current ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    ⌜length current = 144%nat⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsCopiedScratch) := I.

Definition writeSuccessAuthorizationsInvariant `{!islaG Sigma}
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix : list (bv 8)) : iProp Sigma :=
  (⌜total = (processed + S remaining)%nat⌝ ∗
   ⌜length bytes = (144 * total)%nat⌝ ∗
   ⌜bytes = prefix ++ suffix⌝ ∗
   ⌜length prefix = (144 * processed)%nat⌝ ∗
   ⌜length suffix = (144 * S remaining)%nat⌝ ∗
   ⌜bv_unsigned pointer = (base + 144 * Z.of_nat processed)%Z⌝ ∗
   ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsInvariant) := I.

Definition writeSuccessAuthorizationsLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAuthorizationsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessAuthorizationsScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 144 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsLoopExit) := I.

Definition writeSuccessAuthorizationsLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAuthorizationsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessAuthorizationsScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessAuthorizationsEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessAuthorizationsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x15620
      (writeSuccessAuthorizationsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsLoopSpec) := I.

Definition writeSuccessAuthorizationsCopiedSpec `{!islaG Sigma} `{!threadG}
    (phase : writeSuccessAuthorizationsPhase) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAuthorizationsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessAuthorizationsCopiedScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessAuthorizationsPhaseEvents phase sp remaining tail) ∗ P ∗
    writeSuccessAuthorizationsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x15620
      (writeSuccessAuthorizationsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsCopiedSpec) := I.

Definition writeSuccessAuthorizationsTailSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessAuthorizationsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessAuthorizationsScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessAuthorizationsEvents sp remaining tail) ∗ P ∗
    writeSuccessAuthorizationsInvariant
      sp pointer base total processed remaining bytes prefix suffix ∗
    instr_pre 0x15620
      (writeSuccessAuthorizationsLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessAuthorizationsTailSpec) := I.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_write_success_authorizations_chunk boundary :=
  lazymatch goal with
  | |- instr_body boundary _ => idtac
  | |- environments.envs_entails _ (⌜_⌝)%I =>
      prepare_sidecond;
      run_write_success_authorizations_chunk boundary
  | _ =>
      first
        [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderIntCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderU256CallSpec, zesu_c_call)
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | progress unfold LET_ID
        | progress unfold TRACE_LET
        | progress unLET
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | apply bv_eq; rewrite bv_and_unsigned; assumption
        | bv_solve
        | lia ];
      run_write_success_authorizations_chunk boundary
  end.

Ltac run_write_success_authorizations_return boundary :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : (), _)%I =>
      iExists tt;
      iSplit; [|done];
      run_write_success_authorizations_chunk boundary;
      run_write_success_authorizations_return boundary
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done];
      liARun;
      run_write_success_authorizations_return boundary
  | |- environments.envs_entails _
      (subsume
        (instr ?address
          (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_write_success_authorizations_return boundary
  | _ => idtac
  end.

Definition writeSuccessAuthorizationsHeld `{!islaG Sigma}
    (P : iProp Sigma) : iProp Sigma := P.

Lemma write_success_prepend_loaded_u64 `{!islaG Sigma}
    (wordAddress suffixAddress : Z) (bytes suffix : list (bv 8)) :
  wordAddress ↦ₘ
    Z_to_bv 64 (little_endian_to_bv 8 bytes) -∗
  suffixAddress ↦ₘ∗ suffix -∗
  ⌜suffixAddress = (wordAddress + 8)%Z⌝ -∗
  ⌜length bytes = 8%nat⌝ -∗
  wordAddress ↦ₘ∗ (bytes ++ suffix).
Proof.
  iIntros "Hword Hsuffix" (Haddress Hlength).
  iDestruct (mem_mapsto_mapsto_to_byte_array with "Hword") as "Hbytes".
  iEval (rewrite (u64_bytes_roundtrip _ Hlength)) in "Hbytes".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N wordAddress
    (DfracOwn 1) bytes suffix 8 Hlength with "Hbytes") as "Hcombine".
  have HsuffixAddress :
      (wordAddress + Z.of_N (8 `div` 8) * 8)%Z =
      (wordAddress + 8)%Z.
  { change (wordAddress + 1 * 8 = wordAddress + 8)%Z. lia. }
  iEval (rewrite HsuffixAddress) in "Hcombine".
  iEval (rewrite Haddress) in "Hsuffix".
  iApply ("Hcombine" with "Hsuffix").
Qed.

Lemma write_success_combine_byte_arrays `{!islaG Sigma}
    (leftAddress rightAddress : Z) (left right : list (bv 8)) :
  leftAddress ↦ₘ∗ left -∗
  rightAddress ↦ₘ∗ right -∗
  ⌜rightAddress = (leftAddress + Z.of_nat (length left))%Z⌝ -∗
  leftAddress ↦ₘ∗ (left ++ right).
Proof.
  iIntros "Hleft Hright" (Haddress).
  iPoseProof (mem_mapsto_array_app_combine 8%N leftAddress
    (DfracOwn 1) left right with "Hleft") as "Hcombine".
  have HrightAddress :
      (leftAddress + Z.of_N (8 `div` 8) * length left)%Z =
      (leftAddress + Z.of_nat (length left))%Z.
  { change (leftAddress + 1 * Z.of_nat (length left) =
      leftAddress + Z.of_nat (length left))%Z. lia. }
  iEval (rewrite HrightAddress) in "Hcombine".
  iEval (rewrite Haddress) in "Hright".
  iApply ("Hcombine" with "Hright").
Qed.

Ltac recombine_write_success_authorizations_u256
    address0 address1 address2 address3 start0 baseAddress sp current :=
  let HscratchStart0 := fresh "HscratchStart0" in
  have HscratchStart0 :
      Z.to_nat
        (bv_unsigned sp + address0 - (bv_unsigned sp + baseAddress)) = start0;
  [ replace
      (bv_unsigned sp + address0 - (bv_unsigned sp + baseAddress))%Z
      with (Z.of_nat start0) by lia;
    rewrite Nat2Z.id
  | ];
  let HscratchStart1 := fresh "HscratchStart1" in
  have HscratchStart1 :
      Z.to_nat
        (bv_unsigned sp + address1 -
         (bv_unsigned sp + baseAddress + (start0 + 8)%nat)) = 0%nat;
  [ replace
      (bv_unsigned sp + address1 -
       (bv_unsigned sp + baseAddress + (start0 + 8)%nat))%Z with 0%Z by lia;
    reflexivity
  | ];
  let HscratchStart2 := fresh "HscratchStart2" in
  have HscratchStart2 :
      Z.to_nat
        (bv_unsigned sp + address2 -
         (bv_unsigned sp + baseAddress + (start0 + 8)%nat + (0 + 8)%nat)) =
      0%nat;
  [ replace
      (bv_unsigned sp + address2 -
       (bv_unsigned sp + baseAddress + (start0 + 8)%nat + (0 + 8)%nat))%Z
      with 0%Z by lia;
    reflexivity
  | ];
  let HscratchStart3 := fresh "HscratchStart3" in
  have HscratchStart3 :
      Z.to_nat
        (bv_unsigned sp + address3 -
         (bv_unsigned sp + baseAddress + (start0 + 8)%nat + (0 + 8)%nat +
          (0 + 8)%nat)) = 0%nat;
  [ replace
      (bv_unsigned sp + address3 -
       (bv_unsigned sp + baseAddress + (start0 + 8)%nat + (0 + 8)%nat +
        (0 + 8)%nat))%Z with 0%Z by lia;
    reflexivity
  | ];
  iRename select
    (_ ↦ₘ∗ take _ (drop _ (drop _ (drop _ current))))%I
    into "HscratchPrefix3";
  iRename select
    (_ ↦ₘ∗ drop _ (drop _ (drop _ (drop _ current))))%I
    into "HscratchSuffix4";
  iRename select ((bv_unsigned sp + address3) ↦ₘ _)%I
    into "HscratchWord3";
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchPrefix3";
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchSuffix4";
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchWord3";
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix3 HscratchSuffix4 HscratchWord3 [] [] []")
    as "HscratchRest3";
  [ iPureIntro; cbn; lia
  | iPureIntro; cbn; lia
  | iPureIntro; cbn; rewrite ?length_take ?length_drop; lia
  | ];
  iRename select
    (_ ↦ₘ∗ take _ (drop _ (drop _ current)))%I
    into "HscratchPrefix2";
  iRename select ((bv_unsigned sp + address2) ↦ₘ _)%I
    into "HscratchWord2";
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2)
    in "HscratchPrefix2";
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2)
    in "HscratchWord2";
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix2 HscratchRest3 HscratchWord2 [] [] []")
    as "HscratchRest2";
  [ iPureIntro; cbn; lia
  | iPureIntro; cbn; lia
  | iPureIntro; cbn; rewrite ?length_take ?length_drop; lia
  | ];
  iRename select
    (_ ↦ₘ∗ take _ (drop _ current))%I into "HscratchPrefix1";
  iRename select ((bv_unsigned sp + address1) ↦ₘ _)%I
    into "HscratchWord1";
  iEval (rewrite HscratchStart0 HscratchStart1) in "HscratchPrefix1";
  iEval (rewrite HscratchStart0 HscratchStart1) in "HscratchWord1";
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix1 HscratchRest2 HscratchWord1 [] [] []")
    as "HscratchRest1";
  [ iPureIntro; cbn; lia
  | iPureIntro; cbn; lia
  | iPureIntro; cbn; rewrite ?length_take ?length_drop; lia
  | ];
  iRename select (_ ↦ₘ∗ take _ current)%I into "HscratchPrefix0";
  rewrite /subsume;
  iIntros "HscratchWord0";
  iEval (rewrite HscratchStart0) in "HscratchPrefix0";
  iEval (rewrite HscratchStart0) in "HscratchWord0";
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix0 HscratchRest1 HscratchWord0 [] [] []")
    as "Hcurrent";
  [ iPureIntro; cbn; lia
  | iPureIntro; cbn; lia
  | iPureIntro; cbn; rewrite ?length_take ?length_drop; lia
  | ].
