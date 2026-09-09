From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import IslaTraces.write_success_07.a15d30.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d2cAligned : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x2" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d2cLower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess15d2cUpper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess15d2cSysRegs (regs : reg_map) : Prop :=
  regs !! "rv_enable_pmp" = Some (RVal_Bool false) /\
  regs !! "rv_enable_misaligned_access" = Some (RVal_Bool false) /\
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) /\
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) /\
  regs !! "rv_rom_base" = Some (RVal_Bits (BV 64 0x1000)) /\
  regs !! "rv_rom_size" = Some (RVal_Bits (BV 64 0x100)) /\
  regs !! "rv_clint_base" = Some (RVal_Bits (BV 64 0x2000000)) /\
  regs !! "rv_clint_size" = Some (RVal_Bits (BV 64 0xc0000)) /\
  regs !! "rv_htif_tohost" = Some (RVal_Bits (BV 64 0x40001000)) /\
  regs !! "cur_privilege" = Some (RVal_Enum "Machine").

Definition writeSuccess15d2cNextPc : bv 64 :=
  (Z_to_bv 64 0x15d2c + BV 64 4)%bv.
Definition writeSuccess15d2cAddress (sp : bv 64) : bv 64 :=
  (sp + BV 64 8)%bv.
Definition writeSuccess15d2cTrace1 := writeSuccessTraceTail a15d2c.
Definition writeSuccess15d2cTrace2 := writeSuccessTraceTail writeSuccess15d2cTrace1.
Definition writeSuccess15d2cTrace3 := writeSuccessTraceTail writeSuccess15d2cTrace2.
Definition writeSuccess15d2cTrace4 := writeSuccessTraceTail writeSuccess15d2cTrace3.
Definition writeSuccess15d2cTrace5 := writeSuccessTraceTail writeSuccess15d2cTrace4.
Definition writeSuccess15d2cTrace6 := writeSuccessTraceTail writeSuccess15d2cTrace5.
Definition writeSuccess15d2cTrace7 := writeSuccessTraceTail writeSuccess15d2cTrace6.
Definition writeSuccess15d2cTrace8 := writeSuccessTraceTail writeSuccess15d2cTrace7.
Definition writeSuccess15d2cTrace9 := writeSuccessTraceTail writeSuccess15d2cTrace8.
Definition writeSuccess15d2cTrace10 := writeSuccessTraceTail writeSuccess15d2cTrace9.
Definition writeSuccess15d2cTrace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess15d2cTrace10).
Definition writeSuccess15d2cTrace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace11 mstatusBits).
Definition writeSuccess15d2cTrace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess15d2cTrace12 mstatusBits)).
Definition writeSuccess15d2cTrace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace13 mstatusBits address).
Definition writeSuccess15d2cTrace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace14 mstatusBits address).
Definition writeSuccess15d2cTraceUpper (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace15 mstatusBits address).
Definition writeSuccess15d2cTrace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d2c)) 4
    (writeSuccessTraceTail (writeSuccess15d2cTraceUpper mstatusBits address)).
Definition writeSuccess15d2cTrace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace16 mstatusBits address).
Definition writeSuccess15d2cTrace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess15d2cNextPc) 5
    (writeSuccessTraceTail (writeSuccess15d2cTrace17 mstatusBits address)).
Definition writeSuccess15d2cTrace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace18 mstatusBits address).
Definition writeSuccess15d2cTrace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (writeSuccess15d2cAddress address)) 6
    (writeSuccessTraceTail (writeSuccess15d2cTrace19 mstatusBits address)).
Definition writeSuccess15d2cTrace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace20 mstatusBits address).
Definition writeSuccess15d2cTrace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess15d2cTrace21 mstatusBits address)).
Definition writeSuccess15d2cTrace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace22 mstatusBits address satp).
Definition writeSuccess15d2cTrace24 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d2cAddress address))) 26
    (writeSuccessTraceTail (writeSuccess15d2cTrace23 mstatusBits address satp)).
Definition writeSuccess15d2cTrace25 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d2cAddress address))) 32
    (writeSuccessTraceTail (writeSuccess15d2cTrace24 mstatusBits address satp)).
Definition writeSuccess15d2cTrace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 36
    (writeSuccessTraceTail (writeSuccess15d2cTrace25 mstatusBits address satp)).
Definition writeSuccess15d2cTrace27 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace26 mstatusBits address satp value).
Definition writeSuccess15d2cTrace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 37
    (writeSuccessTraceTail (writeSuccess15d2cTrace27 mstatusBits address satp value)).
Definition writeSuccess15d2cTrace29 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace28 mstatusBits address satp value).
Definition writeSuccess15d2cTrace30 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d2cTrace29 mstatusBits address satp value).

Definition writeSuccess15d2cRegs (regs : reg_map) (value : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d2cNextPc]>
    (<["x1" := RVal_Bits value]> regs).
Definition writeSuccess15d2cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d2c regs, global).
Definition writeSuccess15d2cAfter (regs : reg_map)
    (global : seq_global_state) (value : bv 64) : IslaState :=
  (writeSuccess15694Local a15d30 (writeSuccess15d2cRegs regs value), global).

Definition writeSuccess15d2cPreReadObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d2cTrace1; writeSuccess15d2cTrace2;
     writeSuccess15d2cTrace3; writeSuccess15d2cTrace4;
     writeSuccess15d2cTrace5; writeSuccess15d2cTrace6;
     writeSuccess15d2cTrace7; writeSuccess15d2cTrace8;
     writeSuccess15d2cTrace9; writeSuccess15d2cTrace10;
     writeSuccess15d2cTrace11 mstatusBits;
     writeSuccess15d2cTrace12 mstatusBits;
     writeSuccess15d2cTrace13 mstatusBits address;
     writeSuccess15d2cTrace14 mstatusBits address;
     writeSuccess15d2cTrace15 mstatusBits address;
     writeSuccess15d2cTraceUpper mstatusBits address;
     writeSuccess15d2cTrace16 mstatusBits address;
     writeSuccess15d2cTrace17 mstatusBits address;
     writeSuccess15d2cTrace18 mstatusBits address;
     writeSuccess15d2cTrace19 mstatusBits address;
     writeSuccess15d2cTrace20 mstatusBits address;
     writeSuccess15d2cTrace21 mstatusBits address;
     writeSuccess15d2cTrace22 mstatusBits address satp;
     writeSuccess15d2cTrace23 mstatusBits address satp;
     writeSuccess15d2cTrace24 mstatusBits address satp;
     writeSuccess15d2cTrace25 mstatusBits address satp;
     writeSuccess15d2cTrace26 mstatusBits address satp value].

Definition writeSuccess15d2cPostReadPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d2cTrace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d2cTrace29 mstatusBits address satp value)
       (<["x1" := RVal_Bits value]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d2cTrace30 mstatusBits address satp value)
       (writeSuccess15d2cRegs regs value)) global].

Definition writeSuccess15d2cExecutionPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (readLabels : list seq_label) :=
  writeSuccess15d2cPreReadObservations regs global mstatusBits address satp value ++
  ({| microLabels := readLabels; microAfter := (writeSuccess15694Local
      (writeSuccess15d2cTrace27 mstatusBits address satp value) regs, global) |} ::
   writeSuccess15d2cPostReadPrefix regs global mstatusBits address satp value).

Definition writeSuccess15d2cObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess15d2cExecutionPrefix regs global mstatusBits address satp value [] ++
  [writeSuccess15694Observation (writeSuccess15d2cAfter regs global value).1 global].

Definition writeSuccess15d2cMmioObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess15d2cExecutionPrefix regs global mstatusBits address satp value
    [SReadMem (writeSuccess15d2cAddress address) (bv_to_bvn value)] ++
  [writeSuccess15694Observation (writeSuccess15d2cAfter regs global value).1 global].

Definition writeSuccess15d2cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (_ : bool) :=
  writeSuccess15d2cExecutionPrefix regs global mstatusBits address satp value [].

Lemma writeSuccess15d2cNextPcExact :
  writeSuccess15d2cNextPc = Z_to_bv 64 0x15d30.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess15d2cSignExtendIdentity (value : bv 64) :
  bv_sign_extend 64 value = value.
Proof. bv_solve. Qed.

Lemma writeSuccess15d2cRegsLookupOther regs value reg :
  reg <> "PC" -> reg <> "x1" ->
  writeSuccess15d2cRegs regs value !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess15d2cRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess15d2cRegsDom regs base value :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x1" = Some (RVal_Bits base) ->
  dom (writeSuccess15d2cRegs regs value) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hdest.
  unfold writeSuccess15d2cRegs. rewrite !dom_insert_L. set_solver. Qed.

Ltac writeSuccess15d2cTraceCbn :=
  cbn [writeSuccess15d2cTrace1 writeSuccess15d2cTrace2
    writeSuccess15d2cTrace3 writeSuccess15d2cTrace4
    writeSuccess15d2cTrace5 writeSuccess15d2cTrace6
    writeSuccess15d2cTrace7 writeSuccess15d2cTrace8
    writeSuccess15d2cTrace9 writeSuccess15d2cTrace10
    writeSuccess15d2cTrace11 writeSuccess15d2cTrace12
    writeSuccess15d2cTrace13 writeSuccess15d2cTrace14
    writeSuccess15d2cTrace15 writeSuccess15d2cTraceUpper
    writeSuccess15d2cTrace16 writeSuccess15d2cTrace17
    writeSuccess15d2cTrace18 writeSuccess15d2cTrace19
    writeSuccess15d2cTrace20 writeSuccess15d2cTrace21
    writeSuccess15d2cTrace22 writeSuccess15d2cTrace23
    writeSuccess15d2cTrace24 writeSuccess15d2cTrace25
    writeSuccess15d2cTrace26 writeSuccess15d2cTrace27
    writeSuccess15d2cTrace28 writeSuccess15d2cTrace29
    writeSuccess15d2cTrace30 writeSuccess15d2cNextPc
    writeSuccess15d2cAddress writeSuccessTraceTail a15d2c].

Lemma segment_15d2c_core (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64)
    (readLabels : list seq_label) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  writeSuccess15d2cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  ((readLabels = [] /\ read_mem global.(seq_mem)
      (bv_unsigned (writeSuccess15d2cAddress address)) 8 = Some (bv_to_bvn value)) \/
   (readLabels = [SReadMem (writeSuccess15d2cAddress address) (bv_to_bvn value)] /\
    read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 = None /\
    (bv_unsigned (writeSuccess15d2cAddress address) + 8 <= 2 ^ 64)%Z /\
    set_Forall (fun item => ~ (bv_unsigned (writeSuccess15d2cAddress address) <=
      bv_unsigned item < bv_unsigned (writeSuccess15d2cAddress address) + 8)%Z)
      (dom global.(seq_mem)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionSegment (writeSuccess15d2cBefore regs global)
    (writeSuccess15d2cExecutionPrefix regs global mstatusBits address satp value
       readLabels ++
     [writeSuccess15694Observation (writeSuccess15d2cAfter regs global value).1 global])
    (writeSuccess15d2cAfter regs global value).
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hread Hcode Hnext.
  destruct Hsys as (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
    Hclintbase & Hclintsize & Htohost & Hpriv).
  unfold writeSuccess15d2cExecutionPrefix,
    writeSuccess15d2cPreReadObservations,
    writeSuccess15d2cPostReadPrefix.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d2cRegs regs value), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d2c), a15d2c.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess15d2cTraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d2c). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x15d2c))
        (value := RVal_Bits (Z_to_bv 64 0x15d2c));
        [reflexivity|writeSuccess15d2cTraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d2cNextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address) (value := RVal_Bits address);
        [reflexivity|writeSuccess15d2cTraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply DefineConstS with (v := Val_Bits (writeSuccess15d2cAddress address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn. reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess15d2cTraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp) (value := RVal_Bits satp);
        [reflexivity|writeSuccess15d2cTraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess15d2cAddress address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess15d2cAddress address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { destruct Hread as [(-> & Hmem)|(-> & Hmem & Hrange & Houtside)].
      - eapply writeSuccessSeqReadMemBacked with
          (address := writeSuccess15d2cAddress address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess15d2cTraceCbn; constructor|lia|exact Hmem].
      - eapply writeSuccessSeqReadMemMmio with
          (address := writeSuccess15d2cAddress address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess15d2cTraceCbn; constructor|lia|exact Hmem|exact Hrange|exact Houtside]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d2cTraceCbn.
      eapply DefineConstS with (v := Val_Bits value).
      cbn. rewrite writeSuccess15d2cSignExtendIdentity. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits oldDest)
        (value := RVal_Bits value) (updated := RVal_Bits value);
        [reflexivity|writeSuccess15d2cTraceCbn; constructor|exact Hdest|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x15d2c))
        (value := RVal_Bits writeSuccess15d2cNextPc)
        (updated := RVal_Bits writeSuccess15d2cNextPc).
      - reflexivity. - writeSuccess15d2cTraceCbn. constructor.
      - unfold writeSuccess15d2cRegs. rewrite lookup_insert_ne; last congruence. exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d30) (trace := a15d30).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15d30). unfold writeSuccess15d2cRegs.
      rewrite lookup_insert writeSuccess15d2cNextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d30), a15d30.
    cbn. unfold writeSuccess15d2cRegs. rewrite lookup_insert.
    rewrite writeSuccess15d2cNextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_15d2c (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  writeSuccess15d2cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 = Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionSegment (writeSuccess15d2cBefore regs global)
    (writeSuccess15d2cObservations regs global mstatusBits address satp value)
    (writeSuccess15d2cAfter regs global value) /\
  (writeSuccess15d2cAfter regs global value).2.(seq_mem) = global.(seq_mem).
Proof.
  intros. split; last reflexivity.
  unfold writeSuccess15d2cObservations.
  eapply segment_15d2c_core; try eassumption. left. split; eassumption || reflexivity.
Qed.

Lemma segment_15d2c_mmio (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  writeSuccess15d2cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 = None ->
  (bv_unsigned (writeSuccess15d2cAddress address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item => ~ (bv_unsigned (writeSuccess15d2cAddress address) <=
    bv_unsigned item < bv_unsigned (writeSuccess15d2cAddress address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionSegment (writeSuccess15d2cBefore regs global)
    (writeSuccess15d2cMmioObservations regs global mstatusBits address satp value)
    (writeSuccess15d2cAfter regs global value) /\
  (writeSuccess15d2cAfter regs global value).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d2cMmioObservations regs global
    mstatusBits address satp value)) =
    [SReadMem (writeSuccess15d2cAddress address) (bv_to_bvn value)].
Proof.
  intros. repeat split; try reflexivity.
  unfold writeSuccess15d2cMmioObservations.
  eapply segment_15d2c_core; try eassumption.
  right. repeat split; eassumption || reflexivity.
Qed.

Print Assumptions writeSuccess15d2cNextPcExact.
Print Assumptions writeSuccess15d2cSignExtendIdentity.
Print Assumptions writeSuccess15d2cRegsLookupOther.
Print Assumptions writeSuccess15d2cRegsDom.
Print Assumptions segment_15d2c.
Print Assumptions segment_15d2c_mmio.
