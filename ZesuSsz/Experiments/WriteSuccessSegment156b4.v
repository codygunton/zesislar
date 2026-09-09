From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b4.
Require Import IslaTraces.write_success_92.a156b8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156b4Aligned : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x2" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 1752)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess156b4Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 1752)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess156b4Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 1752)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess156b4SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess156b4NextPc : bv 64 :=
  (Z_to_bv 64 0x156b4 + BV 64 4)%bv.
Definition writeSuccess156b4Address (sp : bv 64) : bv 64 :=
  (sp + BV 64 1752)%bv.
Definition writeSuccess156b4Trace1 := writeSuccessTraceTail a156b4.
Definition writeSuccess156b4Trace2 := writeSuccessTraceTail writeSuccess156b4Trace1.
Definition writeSuccess156b4Trace3 := writeSuccessTraceTail writeSuccess156b4Trace2.
Definition writeSuccess156b4Trace4 := writeSuccessTraceTail writeSuccess156b4Trace3.
Definition writeSuccess156b4Trace5 := writeSuccessTraceTail writeSuccess156b4Trace4.
Definition writeSuccess156b4Trace6 := writeSuccessTraceTail writeSuccess156b4Trace5.
Definition writeSuccess156b4Trace7 := writeSuccessTraceTail writeSuccess156b4Trace6.
Definition writeSuccess156b4Trace8 := writeSuccessTraceTail writeSuccess156b4Trace7.
Definition writeSuccess156b4Trace9 := writeSuccessTraceTail writeSuccess156b4Trace8.
Definition writeSuccess156b4Trace10 := writeSuccessTraceTail writeSuccess156b4Trace9.
Definition writeSuccess156b4Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess156b4Trace10).
Definition writeSuccess156b4Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace11 mstatusBits).
Definition writeSuccess156b4Trace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess156b4Trace12 mstatusBits)).
Definition writeSuccess156b4Trace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace13 mstatusBits address).
Definition writeSuccess156b4Trace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace14 mstatusBits address).
Definition writeSuccess156b4TraceUpper (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace15 mstatusBits address).
Definition writeSuccess156b4Trace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156b4)) 4
    (writeSuccessTraceTail (writeSuccess156b4TraceUpper mstatusBits address)).
Definition writeSuccess156b4Trace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace16 mstatusBits address).
Definition writeSuccess156b4Trace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess156b4NextPc) 5
    (writeSuccessTraceTail (writeSuccess156b4Trace17 mstatusBits address)).
Definition writeSuccess156b4Trace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace18 mstatusBits address).
Definition writeSuccess156b4Trace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (writeSuccess156b4Address address)) 6
    (writeSuccessTraceTail (writeSuccess156b4Trace19 mstatusBits address)).
Definition writeSuccess156b4Trace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace20 mstatusBits address).
Definition writeSuccess156b4Trace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess156b4Trace21 mstatusBits address)).
Definition writeSuccess156b4Trace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace22 mstatusBits address satp).
Definition writeSuccess156b4Trace24 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess156b4Address address))) 26
    (writeSuccessTraceTail (writeSuccess156b4Trace23 mstatusBits address satp)).
Definition writeSuccess156b4Trace25 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess156b4Address address))) 32
    (writeSuccessTraceTail (writeSuccess156b4Trace24 mstatusBits address satp)).
Definition writeSuccess156b4Trace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 36
    (writeSuccessTraceTail (writeSuccess156b4Trace25 mstatusBits address satp)).
Definition writeSuccess156b4Trace27 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace26 mstatusBits address satp value).
Definition writeSuccess156b4Trace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 37
    (writeSuccessTraceTail (writeSuccess156b4Trace27 mstatusBits address satp value)).
Definition writeSuccess156b4Trace29 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace28 mstatusBits address satp value).
Definition writeSuccess156b4Trace30 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156b4Trace29 mstatusBits address satp value).

Definition writeSuccess156b4Regs (regs : reg_map) (value : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156b4NextPc]>
    (<["x10" := RVal_Bits value]> regs).
Definition writeSuccess156b4Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156b4 regs, global).
Definition writeSuccess156b4After (regs : reg_map)
    (global : seq_global_state) (value : bv 64) : IslaState :=
  (writeSuccess15694Local a156b8 (writeSuccess156b4Regs regs value), global).

Definition writeSuccess156b4PreReadObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess156b4Trace1; writeSuccess156b4Trace2;
     writeSuccess156b4Trace3; writeSuccess156b4Trace4;
     writeSuccess156b4Trace5; writeSuccess156b4Trace6;
     writeSuccess156b4Trace7; writeSuccess156b4Trace8;
     writeSuccess156b4Trace9; writeSuccess156b4Trace10;
     writeSuccess156b4Trace11 mstatusBits;
     writeSuccess156b4Trace12 mstatusBits;
     writeSuccess156b4Trace13 mstatusBits address;
     writeSuccess156b4Trace14 mstatusBits address;
     writeSuccess156b4Trace15 mstatusBits address;
     writeSuccess156b4TraceUpper mstatusBits address;
     writeSuccess156b4Trace16 mstatusBits address;
     writeSuccess156b4Trace17 mstatusBits address;
     writeSuccess156b4Trace18 mstatusBits address;
     writeSuccess156b4Trace19 mstatusBits address;
     writeSuccess156b4Trace20 mstatusBits address;
     writeSuccess156b4Trace21 mstatusBits address;
     writeSuccess156b4Trace22 mstatusBits address satp;
     writeSuccess156b4Trace23 mstatusBits address satp;
     writeSuccess156b4Trace24 mstatusBits address satp;
     writeSuccess156b4Trace25 mstatusBits address satp;
     writeSuccess156b4Trace26 mstatusBits address satp value].

Definition writeSuccess156b4PostReadPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156b4Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156b4Trace29 mstatusBits address satp value)
       (<["x10" := RVal_Bits value]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156b4Trace30 mstatusBits address satp value)
       (writeSuccess156b4Regs regs value)) global].

Definition writeSuccess156b4ExecutionPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (readLabels : list seq_label) :=
  writeSuccess156b4PreReadObservations regs global mstatusBits address satp value ++
  ({| microLabels := readLabels; microAfter := (writeSuccess15694Local
      (writeSuccess156b4Trace27 mstatusBits address satp value) regs, global) |} ::
   writeSuccess156b4PostReadPrefix regs global mstatusBits address satp value).

Definition writeSuccess156b4Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess156b4ExecutionPrefix regs global mstatusBits address satp value [] ++
  [writeSuccess15694Observation (writeSuccess156b4After regs global value).1 global].

Definition writeSuccess156b4MmioObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess156b4ExecutionPrefix regs global mstatusBits address satp value
    [SReadMem (writeSuccess156b4Address address) (bv_to_bvn value)] ++
  [writeSuccess15694Observation (writeSuccess156b4After regs global value).1 global].

Definition writeSuccess156b4PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (_ : bool) :=
  writeSuccess156b4ExecutionPrefix regs global mstatusBits address satp value [].

Lemma writeSuccess156b4NextPcExact :
  writeSuccess156b4NextPc = Z_to_bv 64 0x156b8.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess156b4SignExtendIdentity (value : bv 64) :
  bv_sign_extend 64 value = value.
Proof. bv_solve. Qed.

Lemma writeSuccess156b4RegsLookupOther regs value reg :
  reg <> "PC" -> reg <> "x10" ->
  writeSuccess156b4Regs regs value !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess156b4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess156b4RegsDom regs base value :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x10" = Some (RVal_Bits base) ->
  dom (writeSuccess156b4Regs regs value) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hdest.
  unfold writeSuccess156b4Regs. rewrite !dom_insert_L. set_solver. Qed.

Ltac writeSuccess156b4TraceCbn :=
  cbn [writeSuccess156b4Trace1 writeSuccess156b4Trace2
    writeSuccess156b4Trace3 writeSuccess156b4Trace4
    writeSuccess156b4Trace5 writeSuccess156b4Trace6
    writeSuccess156b4Trace7 writeSuccess156b4Trace8
    writeSuccess156b4Trace9 writeSuccess156b4Trace10
    writeSuccess156b4Trace11 writeSuccess156b4Trace12
    writeSuccess156b4Trace13 writeSuccess156b4Trace14
    writeSuccess156b4Trace15 writeSuccess156b4TraceUpper
    writeSuccess156b4Trace16 writeSuccess156b4Trace17
    writeSuccess156b4Trace18 writeSuccess156b4Trace19
    writeSuccess156b4Trace20 writeSuccess156b4Trace21
    writeSuccess156b4Trace22 writeSuccess156b4Trace23
    writeSuccess156b4Trace24 writeSuccess156b4Trace25
    writeSuccess156b4Trace26 writeSuccess156b4Trace27
    writeSuccess156b4Trace28 writeSuccess156b4Trace29
    writeSuccess156b4Trace30 writeSuccess156b4NextPc
    writeSuccess156b4Address writeSuccessTraceTail a156b4].

Lemma segment_156b4_core (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64)
    (readLabels : list seq_label) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156b4SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true) ->
  ((readLabels = [] /\ read_mem global.(seq_mem)
      (bv_unsigned (writeSuccess156b4Address address)) 8 = Some (bv_to_bvn value)) \/
   (readLabels = [SReadMem (writeSuccess156b4Address address) (bv_to_bvn value)] /\
    read_mem global.(seq_mem) (bv_unsigned (writeSuccess156b4Address address)) 8 = None /\
    (bv_unsigned (writeSuccess156b4Address address) + 8 <= 2 ^ 64)%Z /\
    set_Forall (fun item => ~ (bv_unsigned (writeSuccess156b4Address address) <=
      bv_unsigned item < bv_unsigned (writeSuccess156b4Address address) + 8)%Z)
      (dom global.(seq_mem)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some a156b4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  IslaInstructionSegment (writeSuccess156b4Before regs global)
    (writeSuccess156b4ExecutionPrefix regs global mstatusBits address satp value
       readLabels ++
     [writeSuccess15694Observation (writeSuccess156b4After regs global value).1 global])
    (writeSuccess156b4After regs global value).
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hread Hcode Hnext.
  destruct Hsys as (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
    Hclintbase & Hclintsize & Htohost & Hpriv).
  unfold writeSuccess156b4ExecutionPrefix,
    writeSuccess156b4PreReadObservations,
    writeSuccess156b4PostReadPrefix.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156b4Regs regs value), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156b4), a156b4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess156b4TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156b4TraceCbn.
      eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156b4TraceCbn.
      eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156b4TraceCbn.
      eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156b4TraceCbn.
      eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156b4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156b4))
        (value := RVal_Bits (Z_to_bv 64 0x156b4));
        [reflexivity|writeSuccess156b4TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156b4NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address) (value := RVal_Bits address);
        [reflexivity|writeSuccess156b4TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      eapply DefineConstS with (v := Val_Bits (writeSuccess156b4Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn. reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess156b4TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp) (value := RVal_Bits satp);
        [reflexivity|writeSuccess156b4TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess156b4Address address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess156b4Address address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { destruct Hread as [(-> & Hmem)|(-> & Hmem & Hrange & Houtside)].
      - eapply writeSuccessSeqReadMemBacked with
          (address := writeSuccess156b4Address address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess156b4TraceCbn; constructor|lia|exact Hmem].
      - eapply writeSuccessSeqReadMemMmio with
          (address := writeSuccess156b4Address address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess156b4TraceCbn; constructor|lia|exact Hmem|exact Hrange|exact Houtside]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156b4TraceCbn.
      eapply DefineConstS with (v := Val_Bits value).
      cbn. rewrite writeSuccess156b4SignExtendIdentity. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits oldDest)
        (value := RVal_Bits value) (updated := RVal_Bits value);
        [reflexivity|writeSuccess156b4TraceCbn; constructor|exact Hdest|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156b4))
        (value := RVal_Bits writeSuccess156b4NextPc)
        (updated := RVal_Bits writeSuccess156b4NextPc).
      - reflexivity. - writeSuccess156b4TraceCbn. constructor.
      - unfold writeSuccess156b4Regs. rewrite lookup_insert_ne; last congruence. exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156b8) (trace := a156b8).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x156b8). unfold writeSuccess156b4Regs.
      rewrite lookup_insert writeSuccess156b4NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156b8), a156b8.
    cbn. unfold writeSuccess156b4Regs. rewrite lookup_insert.
    rewrite writeSuccess156b4NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_156b4 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156b4SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156b4Address address)) 8 = Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some a156b4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  IslaInstructionSegment (writeSuccess156b4Before regs global)
    (writeSuccess156b4Observations regs global mstatusBits address satp value)
    (writeSuccess156b4After regs global value) /\
  (writeSuccess156b4After regs global value).2.(seq_mem) = global.(seq_mem).
Proof.
  intros. split; last reflexivity.
  unfold writeSuccess156b4Observations.
  eapply segment_156b4_core; try eassumption. left. split; eassumption || reflexivity.
Qed.

Lemma segment_156b4_mmio (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156b4SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156b4Address address)) 8 = None ->
  (bv_unsigned (writeSuccess156b4Address address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item => ~ (bv_unsigned (writeSuccess156b4Address address) <=
    bv_unsigned item < bv_unsigned (writeSuccess156b4Address address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b4 = Some a156b4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  IslaInstructionSegment (writeSuccess156b4Before regs global)
    (writeSuccess156b4MmioObservations regs global mstatusBits address satp value)
    (writeSuccess156b4After regs global value) /\
  (writeSuccess156b4After regs global value).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156b4MmioObservations regs global
    mstatusBits address satp value)) =
    [SReadMem (writeSuccess156b4Address address) (bv_to_bvn value)].
Proof.
  intros. repeat split; try reflexivity.
  unfold writeSuccess156b4MmioObservations.
  eapply segment_156b4_core; try eassumption.
  right. repeat split; eassumption || reflexivity.
Qed.

Print Assumptions writeSuccess156b4NextPcExact.
Print Assumptions writeSuccess156b4SignExtendIdentity.
Print Assumptions writeSuccess156b4RegsLookupOther.
Print Assumptions writeSuccess156b4RegsDom.
Print Assumptions segment_156b4.
Print Assumptions segment_156b4_mmio.
