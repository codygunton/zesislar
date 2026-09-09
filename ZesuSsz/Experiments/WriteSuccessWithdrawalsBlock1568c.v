From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1568cCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessPreheaderLookupOther regs sp total register :
  register <> "PC" ->
  register <> "x18" ->
  writeSuccess15690FinalRegs (Z_to_bv 64 (Z.of_nat total))
    (writeSuccess1568cRegs regs sp) !! register = regs !! register.
Proof.
  intros Hpc Hx18.
  rewrite writeSuccess15690RegsLookupOther; last exact Hpc.
  apply writeSuccess1568cRegsLookupOther; assumption.
Qed.

Lemma writeSuccessForallTwo {A} (P Q R : A -> Prop) items :
  Forall P items ->
  Forall Q items ->
  (forall item, P item -> Q item -> R item) ->
  Forall R items.
Proof.
  intros HP HQ Himp. induction HP; inversion HQ; subst; constructor; eauto.
Qed.

Lemma writeSuccessPreheaderSystemKeys :
  Forall (fun entry =>
    match entry.1 with
    | KindReg register => register <> "PC" /\ register <> "x18"
    | KindField register _ => register <> "PC" /\ register <> "x18"
    end) zesu_ram_sys_regs.
Proof. repeat constructor; discriminate. Qed.

Lemma writeSuccessPreheaderRegisterFacts regs sp total :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccess15690FinalRegs (Z_to_bv 64 (Z.of_nat total))
      (writeSuccess1568cRegs regs sp)).
Proof.
  intros (Hmstatus & Hsys & Hgeneral).
  split.
  - unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus |- *.
    cbn in Hmstatus |- *.
    rewrite writeSuccessPreheaderLookupOther; try discriminate.
    exact Hmstatus.
  - split.
    + eapply writeSuccessForallTwo;
        [exact Hsys|apply writeSuccessPreheaderSystemKeys|].
      intros [kind shape] Hshape Hkeys. destruct kind as [register|register field].
      * unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
        cbn in Hkeys.
        destruct Hshape as (value & Hlookup & Hshape).
        exists value. split; last exact Hshape.
        rewrite writeSuccessPreheaderLookupOther; first exact Hlookup; tauto.
      * unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
        cbn in Hkeys.
        destruct Hshape as (root & value & Hroot & Hread & Hshape).
        exists root, value. repeat split; try assumption.
        rewrite writeSuccessPreheaderLookupOther; first exact Hroot; tauto.
    + intros register Hin.
      destruct (Hgeneral register Hin) as (value & Hlookup).
      exists value. rewrite writeSuccessPreheaderLookupOther; first exact Hlookup.
      all: cbn in Hin; naive_solver.
Qed.

Lemma writeSuccessPreheaderRegisterFrame regs frame sp total :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame
    (writeSuccess15690FinalRegs (Z_to_bv 64 (Z.of_nat total))
      (writeSuccess1568cRegs regs sp)) frame.
Proof.
  unfold writeSuccessWithdrawalsRegisterFrame.
  rewrite !Forall_forall. intros Hframe register Hin.
  rewrite writeSuccessPreheaderLookupOther.
  - apply Hframe. exact Hin.
  - intros ->. set_solver.
  - intros ->. set_solver.
Qed.

Lemma writeSuccessPreheaderBaseUnsigned base (allBytes : list (bv 8)) :
  0x20000000 <= base ->
  base + Z.of_nat (length allBytes) < 0x40000000 ->
  bv_unsigned (Z_to_bv 64 base) = base.
Proof.
  intros Hlower Hupper. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma block_1568c : block_1568c_guard_statement.
Proof.
  unfold block_1568c_guard_statement.
  intros args sp base total allBytes scratch encoderScratch registerFrame
    memoryFrame priorLog [[[trace regs pcRegister nb] global] log] Hinv.
  cbn in Hinv |- *.
  have Hboundary : IslaInstructionBoundary
      ({| seq_trace := trace; seq_regs := regs; seq_pc_reg := pcRegister;
          seq_nb_state := nb |}, global) by
    (unfold Inv_1568c in Hinv; tauto).
  have HpcRegister : pcRegister = "PC" by
    (unfold Inv_1568c in Hinv; tauto).
  subst pcRegister.
  have HconcretePc :
      match regs !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x1568c by
    (unfold Inv_1568c, writeSuccessWithdrawalsConcretePc in Hinv; cbn in Hinv;
      tauto).
  destruct Hboundary as (Hnb & pc & source & Hpc & Hsource & Htrace).
  cbn in Hpc, Hsource, Htrace.
  rewrite Hpc in HconcretePc. inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x1568c) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x1568c.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_1568c in Hinv; tauto).
  have Hcode1568c : global.(seq_instrs) !! Z_to_bv 64 0x1568c =
      Some IslaTraces.write_success_89.a1568c.a1568c.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  rewrite Hcode1568c in Hsource. inversion Hsource. subst source.
  subst trace. destruct nb; first discriminate Hnb. clear Hnb.
  have Hsp : regs !! "x2" = Some (RVal_Bits sp) by
    (unfold Inv_1568c in Hinv; tauto).
  have Hx9 : regs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))) by
    (unfold Inv_1568c in Hinv; tauto).
  have Hfacts : writeSuccessWithdrawalsOperationalRegisterFacts regs by
    (unfold Inv_1568c in Hinv; tauto).
  have HmemoryFrame : writeSuccessWithdrawalsMemoryFrame sp global.(seq_mem)
      memoryFrame by (unfold Inv_1568c in Hinv; tauto).
  have Hmstatus : eval_a_exp regs writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold writeSuccessWithdrawalsOperationalRegisterFacts in Hfacts.
    unfold writeSuccessWithdrawalsOperationalMstatus in Hfacts.
    exact (proj1 Hfacts). }
  have Hcode15690 : global.(seq_instrs) !! Z_to_bv 64 0x15690 =
      Some IslaTraces.write_success_89.a15690.a15690.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode15694 : global.(seq_instrs) !! Z_to_bv 64 0x15694 =
      Some IslaTraces.write_success_90.a15694.a15694.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  have Hcode156e8 : global.(seq_instrs) !! Z_to_bv 64 0x156e8 =
      Some IslaTraces.write_success_96.a156e8.a156e8.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  destruct Hfacts as (Hmstatus' & Hsys & Hgeneral).
  have Hx18Owned : exists oldX18, regs !! "x18" = Some oldX18 by
    (unfold Inv_1568c in Hinv; tauto).
  destruct Hx18Owned as (oldX18 & Hx18).
  destruct (segment_1568c regs global sp oldX18
    Hpc Hsp Hx18 Hcode1568c Hcode15690 Hmstatus) as (Hfirst & _).
  set (middleRegs := writeSuccess1568cRegs regs sp).
  have HmiddlePc : middleRegs !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15690)).
  { unfold middleRegs, writeSuccess1568cRegs. rewrite lookup_insert.
    rewrite writeSuccess1568cNextPcExact. reflexivity. }
  have HmiddleX9 : middleRegs !! "x9" =
      Some (RVal_Bits (Z_to_bv 64 (Z.of_nat total))).
  { unfold middleRegs. rewrite writeSuccess1568cRegsLookupOther; congruence. }
  have HmiddleMstatus : eval_a_exp middleRegs writeSuccess15694Mstatus =
      Some (Val_Bool true).
  { unfold middleRegs, writeSuccess15694Mstatus in Hmstatus |- *. cbn in Hmstatus |- *.
    rewrite writeSuccess1568cRegsLookupOther.
    - exact Hmstatus.
    - discriminate.
    - discriminate. }
  have Hsecond := segment_15690 middleRegs global
    (Z_to_bv 64 (Z.of_nat total)) HmiddlePc HmiddleX9 Hcode15690 Hcode15694
    Hcode156e8 HmiddleMstatus.
  set (finalMachine := writeSuccess15690After
    (Z_to_bv 64 (Z.of_nat total)) middleRegs global).
  set (after := (finalMachine, priorLog)).
  exists [writeSuccess1568cObservations regs global sp;
    writeSuccess15690Observations (Z_to_bv 64 (Z.of_nat total)) middleRegs global],
    after.
  split.
  - subst after finalMachine. cbn. econstructor; first exact Hfirst.
    econstructor; first exact Hsecond. constructor.
  - split; first reflexivity.
    destruct total as [|remaining].
    + unfold Inv_156e8, after, finalMachine. cbn.
      unfold writeSuccess15690After, middleRegs.
      destruct decide as [Hzero|Hzero]; last (exfalso; apply Hzero;
        apply bv_eq; cbn; reflexivity).
      have HtakenFacts : writeSuccessWithdrawalsOperationalRegisterFacts
          (writeSuccess15690TakenRegs (writeSuccess1568cRegs regs sp)).
      { have HnewFacts := writeSuccessPreheaderRegisterFacts regs sp 0.
        apply HnewFacts. split; first exact Hmstatus'. split; assumption. }
      have HboundaryAfter : IslaInstructionBoundary
          (writeSuccess15690TakenAfter (writeSuccess1568cRegs regs sp) global).
      { pose proof (@instructionSegmentEnd _ _ _ Hsecond) as Hend.
        destruct Hend as [Hend|Htrap].
        { unfold writeSuccess15690After in Hend.
          destruct (decide (Z_to_bv 64 (Z.of_nat 0) = (BV 64 0)))
            as [Heq|Hneq] in Hend.
          - exact Hend.
          - exfalso. apply Hneq. exact Hzero. }
        unfold IslaInstructionTrap, writeSuccess15690After in Htrap.
        destruct (decide (Z_to_bv 64 (Z.of_nat 0) = (BV 64 0)))
          as [Heq|Hneq] in Htrap.
        - cbn in Htrap. discriminate Htrap.
        - exfalso. apply Hneq. exact Hzero. }
      split; first exact HboundaryAfter.
      split; first reflexivity.
      split.
      * unfold writeSuccessWithdrawalsConcretePc,
          writeSuccess15690TakenAfter, writeSuccess15690TakenRegs,
          writeSuccess15694Local. cbn. rewrite lookup_insert.
        destruct writeSuccess15690PcValues as (_ & ->). reflexivity.
      * split.
        -- unfold writeSuccess15690TakenAfter, writeSuccess15690TakenRegs.
           rewrite lookup_insert_ne; last discriminate.
           unfold middleRegs. rewrite writeSuccess1568cRegsLookupOther;
             try discriminate. exact Hsp.
        -- split.
           ++ unfold writeSuccess15690TakenAfter, writeSuccess15690TakenRegs.
              rewrite lookup_insert_ne; last discriminate.
              unfold middleRegs. rewrite writeSuccess1568cRegsLookupOther;
                try discriminate. unfold Inv_1568c in Hinv. tauto.
           ++ split.
              ** unfold writeSuccess15690TakenAfter, writeSuccess15690TakenRegs.
                 rewrite lookup_insert_ne; last discriminate.
                 unfold middleRegs. rewrite writeSuccess1568cRegsLookupOther;
                   try discriminate. rewrite <- Hzero. exact Hx9.
              ** split.
                 --- replace (base + 48 * Z.of_nat 0) with base by lia.
                     apply (writeSuccessPreheaderBaseUnsigned base allBytes);
                       unfold Inv_1568c in Hinv; tauto.
                 --- split.
                     +++ change (writeSuccessWithdrawalsRegisterFrame
                           (writeSuccess15690TakenRegs
                             (writeSuccess1568cRegs regs sp)) registerFrame).
                         have Hframe := writeSuccessPreheaderRegisterFrame regs
                           registerFrame sp 0
                           ltac:(unfold Inv_1568c in Hinv; tauto).
                         unfold writeSuccess15690FinalRegs in Hframe.
                         destruct decide as [Heq|Hneq]; first exact Hframe.
                         exfalso. apply Hneq. exact Hzero.
                     +++ split; first exact HmemoryFrame.
                         split; first exact Htable.
                         split; first exact HtakenFacts.
                         split.
                         *** unfold Inv_1568c in Hinv. tauto.
                         *** split.
                             ---- unfold Inv_1568c in Hinv. tauto.
                             ---- split.
                                  ++++ unfold Inv_1568c in Hinv. tauto.
                                  ++++ reflexivity.
    + have HlengthWithdrawals : length (observationWithdrawals
          (successDecoded WriteSuccessObservation args)) = S remaining by
        (unfold Inv_1568c in Hinv; lia).
      destruct (observationWithdrawals
        (successDecoded WriteSuccessObservation args)) as [|withdrawal withdrawals]
        eqn:Hwithdrawals; cbn in HlengthWithdrawals; first discriminate.
      injection HlengthWithdrawals as HtailLength.
      have HlengthAll : length allBytes = (48 + 48 * remaining)%nat by
        (unfold Inv_1568c in Hinv; lia).
      have HreadAll : read_mem_list global.(seq_mem) base
          (N.of_nat (48 + 48 * remaining)) = Some allBytes.
      { replace (48 + 48 * remaining)%nat with (length allBytes) by lia.
        unfold Inv_1568c in Hinv. tauto. }
      destruct (read_mem_list_split global.(seq_mem) base 48 (48 * remaining)
        allBytes HreadAll) as
        (current & suffix & HallBytes & HcurrentLength & HsuffixLength &
         HcurrentRead & HsuffixRead).
      exists withdrawal, current, suffix.
      split; first reflexivity.
      split; first exact HallBytes.
      split; first exact HcurrentLength.
      unfold Inv_15694, after, finalMachine. cbn.
      unfold writeSuccess15690After, middleRegs.
      destruct decide as [Hzero|Hzero].
      { exfalso.
        have HbaseLower : 0x20000000 <= base by
          (unfold Inv_1568c in Hinv; tauto).
        have HbaseUpper : base + Z.of_nat (length allBytes) < 0x40000000 by
          (unfold Inv_1568c in Hinv; tauto).
        have HlengthZ := f_equal Z.of_nat HlengthAll.
        rewrite Nat2Z.inj_add in HlengthZ.
        rewrite Nat2Z.inj_mul in HlengthZ. cbn in HlengthZ.
        have Hrange : 0 <= Z.of_nat (S remaining) < bv_modulus 64.
        { split; first lia. unfold bv_modulus. cbn. lia. }
        have HunsignedEq := f_equal bv_unsigned Hzero.
        change (bv_wrap 64 (Z.of_nat (S remaining)) = 0) in HunsignedEq.
        rewrite (bv_wrap_small 64 (Z.of_nat (S remaining)) Hrange)
          in HunsignedEq. lia. }
      have HboundaryAfter : IslaInstructionBoundary
          (writeSuccess15690FallthroughAfter
            (writeSuccess1568cRegs regs sp) global).
      { pose proof (@instructionSegmentEnd _ _ _ Hsecond) as Hend.
        destruct Hend as [Hend|Htrap].
        { unfold writeSuccess15690After in Hend.
          destruct (decide (Z_to_bv 64 (Z.of_nat (S remaining)) = (BV 64 0)))
            as [Heq|Hneq] in Hend.
          - exfalso. apply Hzero. exact Heq.
          - exact Hend. }
        unfold IslaInstructionTrap, writeSuccess15690After in Htrap.
        destruct (decide (Z_to_bv 64 (Z.of_nat (S remaining)) = (BV 64 0)))
          as [Heq|Hneq] in Htrap.
        - exfalso. apply Hzero. exact Heq.
        - cbn in Htrap. discriminate Htrap. }
      have HfinalIsFallthrough :
          writeSuccess15690FinalRegs (Z_to_bv 64 (Z.of_nat (S remaining)))
            (writeSuccess1568cRegs regs sp) =
          writeSuccess15690FallthroughRegs (writeSuccess1568cRegs regs sp).
      { unfold writeSuccess15690FinalRegs. destruct decide; congruence. }
      have HoutOther register : register <> "PC" -> register <> "x18" ->
          writeSuccess15690FallthroughRegs (writeSuccess1568cRegs regs sp) !!
            register = regs !! register.
      { intros HnotPc HnotX18. rewrite <- HfinalIsFallthrough.
        apply writeSuccessPreheaderLookupOther; assumption. }
      have HfallthroughFrame : writeSuccessWithdrawalsRegisterFrame
          (writeSuccess15690FallthroughRegs (writeSuccess1568cRegs regs sp))
          registerFrame.
      { rewrite <- HfinalIsFallthrough.
        apply writeSuccessPreheaderRegisterFrame.
        unfold Inv_1568c in Hinv. tauto. }
      have HfallthroughFacts : writeSuccessWithdrawalsOperationalRegisterFacts
          (writeSuccess15690FallthroughRegs (writeSuccess1568cRegs regs sp)).
      { rewrite <- HfinalIsFallthrough.
        apply writeSuccessPreheaderRegisterFacts.
        split; first exact Hmstatus'. split; assumption. }
      split; first exact HboundaryAfter.
      split; first reflexivity.
      split.
      * unfold writeSuccessWithdrawalsConcretePc,
          writeSuccess15690FallthroughAfter,
          writeSuccess15690FallthroughRegs, writeSuccess15694Local.
        cbn. rewrite lookup_insert.
        destruct writeSuccess15690PcValues as (-> & _). reflexivity.
      * split.
        -- destruct (Hgeneral "x1" ltac:(cbn; tauto)) as (value & Hvalue).
           exists (RVal_Bits value). rewrite HoutOther; try discriminate.
           exact Hvalue.
        -- split.
           ++ rewrite HoutOther; try discriminate. exact Hsp.
           ++ split.
              ** destruct (Hgeneral "x10" ltac:(cbn; tauto)) as (value & Hvalue).
                 exists (RVal_Bits value). rewrite HoutOther; try discriminate.
                 exact Hvalue.
              ** split.
                 --- destruct (Hgeneral "x11" ltac:(cbn; tauto))
                       as (value & Hvalue).
                     exists (RVal_Bits value). rewrite HoutOther;
                       try discriminate. exact Hvalue.
                 --- split.
                     +++ destruct (Hgeneral "x12" ltac:(cbn; tauto))
                           as (value & Hvalue).
                         exists (RVal_Bits value). rewrite HoutOther;
                           try discriminate. exact Hvalue.
                     +++ split.
                         *** destruct (Hgeneral "x15" ltac:(cbn; tauto))
                               as (value & Hvalue).
                             exists (RVal_Bits value). rewrite HoutOther;
                               try discriminate. exact Hvalue.
                         *** split.
                             ---- rewrite HoutOther; try discriminate.
                                  unfold Inv_1568c in Hinv. tauto.
                             ---- split.
                                  ++++ rewrite HoutOther; try discriminate.
                                       exact Hx9.
                                  ++++ split.
                                       { unfold writeSuccess15690FallthroughAfter,
                                           writeSuccess15694Local,
                                           writeSuccess15690FallthroughRegs,
                                           writeSuccess1568cRegs.
                                         rewrite lookup_insert_ne;
                                           last discriminate.
                                         rewrite lookup_insert_ne;
                                           last discriminate.
                                         rewrite lookup_insert. reflexivity. }
                                       split; first exact HfallthroughFrame.
                                       split; first exact HmemoryFrame.
                                       split; first exact Htable.
                                       split; first exact HfallthroughFacts.
                                       split.
                                       { unfold Inv_1568c in Hinv. tauto. }
                                       split.
                                       { unfold Inv_1568c in Hinv. tauto. }
                                       split.
                                       { unfold Inv_1568c in Hinv. tauto. }
                                       split; first reflexivity.
                                       split; first (rewrite Hwithdrawals; reflexivity).
                                       split; first exact HallBytes.
                                       split; first reflexivity.
                                       split; first exact HcurrentLength.
                                       split; first (cbn; exact HsuffixLength).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split.
                                       { replace (base + 48 * Z.of_nat 0) with base by lia.
                                         apply (writeSuccessPreheaderBaseUnsigned
                                           base allBytes);
                                           unfold Inv_1568c in Hinv; tauto. }
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split.
                                       { rewrite (writeSuccessPreheaderBaseUnsigned
                                           base allBytes).
                                         - exact HcurrentRead.
                                         - unfold Inv_1568c in Hinv. tauto.
                                         - unfold Inv_1568c in Hinv. tauto. }
                                       split.
                                       { have Hitems : writeSuccessWithdrawalItemsAt
                                           global.(seq_mem) base
                                           (observationWithdrawals
                                             (successDecoded WriteSuccessObservation args))
                                           by (unfold Inv_1568c in Hinv; tauto).
                                         unfold writeSuccessWithdrawalItemsAt in Hitems.
                                         rewrite (writeSuccessPreheaderBaseUnsigned
                                           base allBytes).
                                         - change (writeSuccessWithdrawalMemory
                                             global.(seq_mem) base withdrawal).
                                           replace base with
                                             (base + 48 * Z.of_nat 0) by lia.
                                           eapply Hitems with (index := 0%nat).
                                           rewrite Hwithdrawals. reflexivity.
                                         - unfold Inv_1568c in Hinv. tauto.
                                         - unfold Inv_1568c in Hinv. tauto. }
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split.
                                       { rewrite (writeSuccessPreheaderBaseUnsigned
                                           base allBytes).
                                         - have Hdisjoint : islaMemoryRangesDisjoint
                                             base (length allBytes)
                                             (bv_unsigned sp + 1744) 48 by
                                             (unfold Inv_1568c in Hinv; tauto).
                                           unfold islaMemoryRangesDisjoint in Hdisjoint |- *.
                                           rewrite HlengthAll in Hdisjoint. cbn in Hdisjoint.
                                           lia.
                                         - unfold Inv_1568c in Hinv. tauto.
                                         - unfold Inv_1568c in Hinv. tauto. }
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       split; first (unfold Inv_1568c in Hinv; tauto).
                                       reflexivity.
Qed.

Print Assumptions writeSuccessPreheaderLookupOther.
Print Assumptions writeSuccessPreheaderRegisterFacts.
Print Assumptions writeSuccessPreheaderRegisterFrame.
Print Assumptions writeSuccessPreheaderBaseUnsigned.
Print Assumptions block_1568c.
