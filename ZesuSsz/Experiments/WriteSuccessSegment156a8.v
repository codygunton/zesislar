From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import IslaTraces.write_success_91.a156ac.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156a8Aligned : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x2" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 1744)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess156a8Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 1744)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess156a8Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 1744)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess156a8SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess156a8NextPc : bv 64 :=
  (Z_to_bv 64 0x156a8 + BV 64 4)%bv.
Definition writeSuccess156a8Address (sp : bv 64) : bv 64 :=
  (sp + BV 64 1744)%bv.
Definition writeSuccess156a8Trace1 := writeSuccessTraceTail a156a8.
Definition writeSuccess156a8Trace2 := writeSuccessTraceTail writeSuccess156a8Trace1.
Definition writeSuccess156a8Trace3 := writeSuccessTraceTail writeSuccess156a8Trace2.
Definition writeSuccess156a8Trace4 := writeSuccessTraceTail writeSuccess156a8Trace3.
Definition writeSuccess156a8Trace5 := writeSuccessTraceTail writeSuccess156a8Trace4.
Definition writeSuccess156a8Trace6 := writeSuccessTraceTail writeSuccess156a8Trace5.
Definition writeSuccess156a8Trace7 := writeSuccessTraceTail writeSuccess156a8Trace6.
Definition writeSuccess156a8Trace8 := writeSuccessTraceTail writeSuccess156a8Trace7.
Definition writeSuccess156a8Trace9 := writeSuccessTraceTail writeSuccess156a8Trace8.
Definition writeSuccess156a8Trace10 := writeSuccessTraceTail writeSuccess156a8Trace9.
Definition writeSuccess156a8Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess156a8Trace10).
Definition writeSuccess156a8Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace11 mstatusBits).
Definition writeSuccess156a8Trace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess156a8Trace12 mstatusBits)).
Definition writeSuccess156a8Trace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace13 mstatusBits address).
Definition writeSuccess156a8Trace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace14 mstatusBits address).
Definition writeSuccess156a8TraceUpper (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace15 mstatusBits address).
Definition writeSuccess156a8Trace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156a8)) 4
    (writeSuccessTraceTail (writeSuccess156a8TraceUpper mstatusBits address)).
Definition writeSuccess156a8Trace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace16 mstatusBits address).
Definition writeSuccess156a8Trace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess156a8NextPc) 5
    (writeSuccessTraceTail (writeSuccess156a8Trace17 mstatusBits address)).
Definition writeSuccess156a8Trace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace18 mstatusBits address).
Definition writeSuccess156a8Trace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (writeSuccess156a8Address address)) 6
    (writeSuccessTraceTail (writeSuccess156a8Trace19 mstatusBits address)).
Definition writeSuccess156a8Trace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace20 mstatusBits address).
Definition writeSuccess156a8Trace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess156a8Trace21 mstatusBits address)).
Definition writeSuccess156a8Trace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace22 mstatusBits address satp).
Definition writeSuccess156a8Trace24 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess156a8Address address))) 26
    (writeSuccessTraceTail (writeSuccess156a8Trace23 mstatusBits address satp)).
Definition writeSuccess156a8Trace25 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess156a8Address address))) 32
    (writeSuccessTraceTail (writeSuccess156a8Trace24 mstatusBits address satp)).
Definition writeSuccess156a8Trace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 36
    (writeSuccessTraceTail (writeSuccess156a8Trace25 mstatusBits address satp)).
Definition writeSuccess156a8Trace27 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace26 mstatusBits address satp value).
Definition writeSuccess156a8Trace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 37
    (writeSuccessTraceTail (writeSuccess156a8Trace27 mstatusBits address satp value)).
Definition writeSuccess156a8Trace29 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace28 mstatusBits address satp value).
Definition writeSuccess156a8Trace30 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156a8Trace29 mstatusBits address satp value).

Definition writeSuccess156a8Regs (regs : reg_map) (value : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156a8NextPc]>
    (<["x10" := RVal_Bits value]> regs).
Definition writeSuccess156a8Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156a8 regs, global).
Definition writeSuccess156a8After (regs : reg_map)
    (global : seq_global_state) (value : bv 64) : IslaState :=
  (writeSuccess15694Local a156ac (writeSuccess156a8Regs regs value), global).

Definition writeSuccess156a8PreReadObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess156a8Trace1; writeSuccess156a8Trace2;
     writeSuccess156a8Trace3; writeSuccess156a8Trace4;
     writeSuccess156a8Trace5; writeSuccess156a8Trace6;
     writeSuccess156a8Trace7; writeSuccess156a8Trace8;
     writeSuccess156a8Trace9; writeSuccess156a8Trace10;
     writeSuccess156a8Trace11 mstatusBits;
     writeSuccess156a8Trace12 mstatusBits;
     writeSuccess156a8Trace13 mstatusBits address;
     writeSuccess156a8Trace14 mstatusBits address;
     writeSuccess156a8Trace15 mstatusBits address;
     writeSuccess156a8TraceUpper mstatusBits address;
     writeSuccess156a8Trace16 mstatusBits address;
     writeSuccess156a8Trace17 mstatusBits address;
     writeSuccess156a8Trace18 mstatusBits address;
     writeSuccess156a8Trace19 mstatusBits address;
     writeSuccess156a8Trace20 mstatusBits address;
     writeSuccess156a8Trace21 mstatusBits address;
     writeSuccess156a8Trace22 mstatusBits address satp;
     writeSuccess156a8Trace23 mstatusBits address satp;
     writeSuccess156a8Trace24 mstatusBits address satp;
     writeSuccess156a8Trace25 mstatusBits address satp;
     writeSuccess156a8Trace26 mstatusBits address satp value].

Definition writeSuccess156a8PostReadPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156a8Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156a8Trace29 mstatusBits address satp value)
       (<["x10" := RVal_Bits value]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess156a8Trace30 mstatusBits address satp value)
       (writeSuccess156a8Regs regs value)) global].

Definition writeSuccess156a8ExecutionPrefix (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (readLabels : list seq_label) :=
  writeSuccess156a8PreReadObservations regs global mstatusBits address satp value ++
  ({| microLabels := readLabels; microAfter := (writeSuccess15694Local
      (writeSuccess156a8Trace27 mstatusBits address satp value) regs, global) |} ::
   writeSuccess156a8PostReadPrefix regs global mstatusBits address satp value).

Definition writeSuccess156a8Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess156a8ExecutionPrefix regs global mstatusBits address satp value [] ++
  [writeSuccess15694Observation (writeSuccess156a8After regs global value).1 global].

Definition writeSuccess156a8MmioObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64) :=
  writeSuccess156a8ExecutionPrefix regs global mstatusBits address satp value
    [SReadMem (writeSuccess156a8Address address) (bv_to_bvn value)] ++
  [writeSuccess15694Observation (writeSuccess156a8After regs global value).1 global].

Definition writeSuccess156a8PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (_ : bool) :=
  writeSuccess156a8ExecutionPrefix regs global mstatusBits address satp value [].

Lemma writeSuccess156a8NextPcExact :
  writeSuccess156a8NextPc = Z_to_bv 64 0x156ac.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess156a8SignExtendIdentity (value : bv 64) :
  bv_sign_extend 64 value = value.
Proof. bv_solve. Qed.

Lemma writeSuccess156a8RegsLookupOther regs value reg :
  reg <> "PC" -> reg <> "x10" ->
  writeSuccess156a8Regs regs value !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess156a8Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess156a8RegsDom regs base value :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x10" = Some (RVal_Bits base) ->
  dom (writeSuccess156a8Regs regs value) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hdest.
  unfold writeSuccess156a8Regs. rewrite !dom_insert_L. set_solver. Qed.

Ltac writeSuccess156a8TraceCbn :=
  cbn [writeSuccess156a8Trace1 writeSuccess156a8Trace2
    writeSuccess156a8Trace3 writeSuccess156a8Trace4
    writeSuccess156a8Trace5 writeSuccess156a8Trace6
    writeSuccess156a8Trace7 writeSuccess156a8Trace8
    writeSuccess156a8Trace9 writeSuccess156a8Trace10
    writeSuccess156a8Trace11 writeSuccess156a8Trace12
    writeSuccess156a8Trace13 writeSuccess156a8Trace14
    writeSuccess156a8Trace15 writeSuccess156a8TraceUpper
    writeSuccess156a8Trace16 writeSuccess156a8Trace17
    writeSuccess156a8Trace18 writeSuccess156a8Trace19
    writeSuccess156a8Trace20 writeSuccess156a8Trace21
    writeSuccess156a8Trace22 writeSuccess156a8Trace23
    writeSuccess156a8Trace24 writeSuccess156a8Trace25
    writeSuccess156a8Trace26 writeSuccess156a8Trace27
    writeSuccess156a8Trace28 writeSuccess156a8Trace29
    writeSuccess156a8Trace30 writeSuccess156a8NextPc
    writeSuccess156a8Address writeSuccessTraceTail a156a8].

Lemma segment_156a8_core (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64)
    (readLabels : list seq_label) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true) ->
  ((readLabels = [] /\ read_mem global.(seq_mem)
      (bv_unsigned (writeSuccess156a8Address address)) 8 = Some (bv_to_bvn value)) \/
   (readLabels = [SReadMem (writeSuccess156a8Address address) (bv_to_bvn value)] /\
    read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 = None /\
    (bv_unsigned (writeSuccess156a8Address address) + 8 <= 2 ^ 64)%Z /\
    set_Forall (fun item => ~ (bv_unsigned (writeSuccess156a8Address address) <=
      bv_unsigned item < bv_unsigned (writeSuccess156a8Address address) + 8)%Z)
      (dom global.(seq_mem)))) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionSegment (writeSuccess156a8Before regs global)
    (writeSuccess156a8ExecutionPrefix regs global mstatusBits address satp value
       readLabels ++
     [writeSuccess15694Observation (writeSuccess156a8After regs global value).1 global])
    (writeSuccess156a8After regs global value).
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hread Hcode Hnext.
  destruct Hsys as (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
    Hclintbase & Hclintsize & Htohost & Hpriv).
  unfold writeSuccess156a8ExecutionPrefix,
    writeSuccess156a8PreReadObservations,
    writeSuccess156a8PostReadPrefix.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156a8Regs regs value), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156a8), a156a8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess156a8TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156a8TraceCbn.
      eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156a8TraceCbn.
      eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156a8TraceCbn.
      eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity. writeSuccess156a8TraceCbn.
      eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156a8). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits (Z_to_bv 64 0x156a8))
        (value := RVal_Bits (Z_to_bv 64 0x156a8));
        [reflexivity|writeSuccess156a8TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess156a8NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address) (value := RVal_Bits address);
        [reflexivity|writeSuccess156a8TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      eapply DefineConstS with (v := Val_Bits (writeSuccess156a8Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn. reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess156a8TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp) (value := RVal_Bits satp);
        [reflexivity|writeSuccess156a8TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess156a8Address address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128
        (writeSuccess156a8Address address))). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { destruct Hread as [(-> & Hmem)|(-> & Hmem & Hrange & Houtside)].
      - eapply writeSuccessSeqReadMemBacked with
          (address := writeSuccess156a8Address address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess156a8TraceCbn; constructor|lia|exact Hmem].
      - eapply writeSuccessSeqReadMemMmio with
          (address := writeSuccess156a8Address address) (len := 8%N) (value := value);
          [reflexivity|writeSuccess156a8TraceCbn; constructor|lia|exact Hmem|exact Hrange|exact Houtside]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess156a8TraceCbn.
      eapply DefineConstS with (v := Val_Bits value).
      cbn. rewrite writeSuccess156a8SignExtendIdentity. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits oldDest)
        (value := RVal_Bits value) (updated := RVal_Bits value);
        [reflexivity|writeSuccess156a8TraceCbn; constructor|exact Hdest|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := RVal_Bits (Z_to_bv 64 0x156a8))
        (value := RVal_Bits writeSuccess156a8NextPc)
        (updated := RVal_Bits writeSuccess156a8NextPc).
      - reflexivity. - writeSuccess156a8TraceCbn. constructor.
      - unfold writeSuccess156a8Regs. rewrite lookup_insert_ne; last congruence. exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156ac) (trace := a156ac).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x156ac). unfold writeSuccess156a8Regs.
      rewrite lookup_insert writeSuccess156a8NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156ac), a156ac.
    cbn. unfold writeSuccess156a8Regs. rewrite lookup_insert.
    rewrite writeSuccess156a8NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_156a8 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 = Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionSegment (writeSuccess156a8Before regs global)
    (writeSuccess156a8Observations regs global mstatusBits address satp value)
    (writeSuccess156a8After regs global value) /\
  (writeSuccess156a8After regs global value).2.(seq_mem) = global.(seq_mem).
Proof.
  intros. split; last reflexivity.
  unfold writeSuccess156a8Observations.
  eapply segment_156a8_core; try eassumption. left. split; eassumption || reflexivity.
Qed.

Lemma segment_156a8_mmio (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 = None ->
  (bv_unsigned (writeSuccess156a8Address address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item => ~ (bv_unsigned (writeSuccess156a8Address address) <=
    bv_unsigned item < bv_unsigned (writeSuccess156a8Address address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionSegment (writeSuccess156a8Before regs global)
    (writeSuccess156a8MmioObservations regs global mstatusBits address satp value)
    (writeSuccess156a8After regs global value) /\
  (writeSuccess156a8After regs global value).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a8MmioObservations regs global
    mstatusBits address satp value)) =
    [SReadMem (writeSuccess156a8Address address) (bv_to_bvn value)].
Proof.
  intros. repeat split; try reflexivity.
  unfold writeSuccess156a8MmioObservations.
  eapply segment_156a8_core; try eassumption.
  right. repeat split; eassumption || reflexivity.
Qed.

Print Assumptions writeSuccess156a8NextPcExact.
Print Assumptions writeSuccess156a8SignExtendIdentity.
Print Assumptions writeSuccess156a8RegsLookupOther.
Print Assumptions writeSuccess156a8RegsDom.
Print Assumptions segment_156a8.
Print Assumptions segment_156a8_mmio.
