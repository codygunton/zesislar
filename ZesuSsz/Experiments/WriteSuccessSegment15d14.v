From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d14.
Require Import IslaTraces.write_success_07.a15d18.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d14Aligned : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x2" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d14Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess15d14Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess15d14SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess15d14NextPc : bv 64 :=
  (Z_to_bv 64 0x15d14 + BV 64 4)%bv.
Definition writeSuccess15d14Address (sp : bv 64) : bv 64 :=
  (sp + BV 64 8)%bv.
Definition writeSuccess15d14Bytes (value : bv 64) : list (bv 8) :=
  bv_to_little_endian 8 8 (bv_unsigned value).
Definition writeSuccess15d14Memory (global : seq_global_state)
    (address value : bv 64) : mem_map :=
  write_mem_list global.(seq_mem) (writeSuccess15d14Address address)
    (writeSuccess15d14Bytes value).
Definition writeSuccess15d14Global (global : seq_global_state)
    (address value : bv 64) : seq_global_state :=
  global <| seq_mem := writeSuccess15d14Memory global address value |>.

Definition writeSuccess15d14Trace1 := writeSuccessTraceTail a15d14.
Definition writeSuccess15d14Trace2 := writeSuccessTraceTail writeSuccess15d14Trace1.
Definition writeSuccess15d14Trace3 := writeSuccessTraceTail writeSuccess15d14Trace2.
Definition writeSuccess15d14Trace4 := writeSuccessTraceTail writeSuccess15d14Trace3.
Definition writeSuccess15d14Trace5 := writeSuccessTraceTail writeSuccess15d14Trace4.
Definition writeSuccess15d14Trace6 := writeSuccessTraceTail writeSuccess15d14Trace5.
Definition writeSuccess15d14Trace7 := writeSuccessTraceTail writeSuccess15d14Trace6.
Definition writeSuccess15d14Trace8 := writeSuccessTraceTail writeSuccess15d14Trace7.
Definition writeSuccess15d14Trace9 := writeSuccessTraceTail writeSuccess15d14Trace8.
Definition writeSuccess15d14Trace10 := writeSuccessTraceTail writeSuccess15d14Trace9.
Definition writeSuccess15d14Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess15d14Trace10).
Definition writeSuccess15d14Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace11 mstatusBits).
Definition writeSuccess15d14Trace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess15d14Trace12 mstatusBits)).
Definition writeSuccess15d14Trace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace13 mstatusBits address).
Definition writeSuccess15d14Trace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace14 mstatusBits address).
Definition writeSuccess15d14TraceUpper (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace15 mstatusBits address).
Definition writeSuccess15d14Trace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d14)) 4
    (writeSuccessTraceTail (writeSuccess15d14TraceUpper mstatusBits address)).
Definition writeSuccess15d14Trace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace16 mstatusBits address).
Definition writeSuccess15d14Trace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess15d14NextPc) 5
    (writeSuccessTraceTail (writeSuccess15d14Trace17 mstatusBits address)).
Definition writeSuccess15d14Trace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace18 mstatusBits address).
Definition writeSuccess15d14Trace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (writeSuccess15d14Address address)) 6
    (writeSuccessTraceTail (writeSuccess15d14Trace19 mstatusBits address)).
Definition writeSuccess15d14Trace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace20 mstatusBits address).
Definition writeSuccess15d14Trace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess15d14Trace21 mstatusBits address)).
Definition writeSuccess15d14Trace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace22 mstatusBits address satp).
Definition writeSuccess15d14Trace24 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 24
    (writeSuccessTraceTail (writeSuccess15d14Trace23 mstatusBits address satp)).
Definition writeSuccess15d14Trace25 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d14Trace24 mstatusBits address satp value).
Definition writeSuccess15d14Trace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 19
    (writeSuccessTraceTail (writeSuccess15d14Trace25 mstatusBits address satp value)).
Definition writeSuccess15d14Trace27 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))) 27
    (writeSuccessTraceTail (writeSuccess15d14Trace25 mstatusBits address satp value)).
Definition writeSuccess15d14Trace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))) 33
    (writeSuccessTraceTail (writeSuccess15d14Trace27 mstatusBits address satp value)).
Definition writeSuccess15d14Trace29 (mstatusBits address satp value : bv 64) (result : bool) :=
  subst_trace (Val_Bool result) 37
    (writeSuccessTraceTail (writeSuccess15d14Trace28 mstatusBits address satp value)).
Definition writeSuccess15d14Trace30 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess15d14Trace29 mstatusBits address satp value result).
Definition writeSuccess15d14Trace31 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess15d14Trace30 mstatusBits address satp value result).

Definition writeSuccess15d14Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d14NextPc]> regs.
Definition writeSuccess15d14Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d14 regs, global).
Definition writeSuccess15d14After (regs : reg_map)
    (global : seq_global_state) (address value : bv 64) : IslaState :=
  (writeSuccess15694Local a15d18 (writeSuccess15d14Regs regs),
   writeSuccess15d14Global global address value).

Definition writeSuccess15d14PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d14Trace1; writeSuccess15d14Trace2;
     writeSuccess15d14Trace3; writeSuccess15d14Trace4;
     writeSuccess15d14Trace5; writeSuccess15d14Trace6;
     writeSuccess15d14Trace7; writeSuccess15d14Trace8;
     writeSuccess15d14Trace9; writeSuccess15d14Trace10;
     writeSuccess15d14Trace11 mstatusBits;
     writeSuccess15d14Trace12 mstatusBits;
     writeSuccess15d14Trace13 mstatusBits address;
     writeSuccess15d14Trace14 mstatusBits address;
     writeSuccess15d14Trace15 mstatusBits address;
     writeSuccess15d14TraceUpper mstatusBits address;
     writeSuccess15d14Trace16 mstatusBits address;
     writeSuccess15d14Trace17 mstatusBits address;
     writeSuccess15d14Trace18 mstatusBits address;
     writeSuccess15d14Trace19 mstatusBits address;
     writeSuccess15d14Trace20 mstatusBits address;
     writeSuccess15d14Trace21 mstatusBits address;
     writeSuccess15d14Trace22 mstatusBits address satp;
     writeSuccess15d14Trace23 mstatusBits address satp;
     writeSuccess15d14Trace24 mstatusBits address satp value;
     writeSuccess15d14Trace25 mstatusBits address satp value;
     writeSuccess15d14Trace27 mstatusBits address satp value;
     writeSuccess15d14Trace28 mstatusBits address satp value;
     writeSuccess15d14Trace29 mstatusBits address satp value result] ++
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace30 mstatusBits address satp value result) regs)
     (writeSuccess15d14Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace31 mstatusBits address satp value result)
       (writeSuccess15d14Regs regs))
     (writeSuccess15d14Global global address value)].

Definition writeSuccess15d14Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  writeSuccess15d14PrefixObservations regs global mstatusBits address satp value result ++
  [writeSuccess15694Observation
     (writeSuccess15d14After regs global address value).1
     (writeSuccess15d14Global global address value)].

Definition writeSuccess15d14MmioAfter (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d18 (writeSuccess15d14Regs regs), global).

Definition writeSuccess15d14MmioPrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d14Trace1; writeSuccess15d14Trace2;
     writeSuccess15d14Trace3; writeSuccess15d14Trace4;
     writeSuccess15d14Trace5; writeSuccess15d14Trace6;
     writeSuccess15d14Trace7; writeSuccess15d14Trace8;
     writeSuccess15d14Trace9; writeSuccess15d14Trace10;
     writeSuccess15d14Trace11 mstatusBits;
     writeSuccess15d14Trace12 mstatusBits;
     writeSuccess15d14Trace13 mstatusBits address;
     writeSuccess15d14Trace14 mstatusBits address;
     writeSuccess15d14Trace15 mstatusBits address;
     writeSuccess15d14TraceUpper mstatusBits address;
     writeSuccess15d14Trace16 mstatusBits address;
     writeSuccess15d14Trace17 mstatusBits address;
     writeSuccess15d14Trace18 mstatusBits address;
     writeSuccess15d14Trace19 mstatusBits address;
     writeSuccess15d14Trace20 mstatusBits address;
     writeSuccess15d14Trace21 mstatusBits address;
     writeSuccess15d14Trace22 mstatusBits address satp;
     writeSuccess15d14Trace23 mstatusBits address satp;
     writeSuccess15d14Trace24 mstatusBits address satp value;
     writeSuccess15d14Trace25 mstatusBits address satp value;
     writeSuccess15d14Trace27 mstatusBits address satp value;
     writeSuccess15d14Trace28 mstatusBits address satp value;
     writeSuccess15d14Trace29 mstatusBits address satp value result] ++
  [ {| microLabels :=
        [SWriteMem (writeSuccess15d14Address address) (bv_to_bvn value)];
      microAfter :=
        (writeSuccess15694Local
          (writeSuccess15d14Trace30 mstatusBits address satp value result) regs,
         global) |};
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace31 mstatusBits address satp value result)
       (writeSuccess15d14Regs regs)) global].

Definition writeSuccess15d14MmioObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  writeSuccess15d14MmioPrefixObservations regs global mstatusBits address satp
    value result ++
  [writeSuccess15694Observation
     (writeSuccess15d14MmioAfter regs global).1 global].

Lemma writeSuccess15d14NextPcExact :
  writeSuccess15d14NextPc = Z_to_bv 64 0x15d18.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess15d14RegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess15d14Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc. unfold writeSuccess15d14Regs.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess15d14RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  dom (writeSuccess15d14Regs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess15d14Regs.
  rewrite dom_insert_L. set_solver. Qed.

Ltac writeSuccess15d14TraceCbn :=
  cbv [writeSuccess15d14Trace1 writeSuccess15d14Trace2
    writeSuccess15d14Trace3 writeSuccess15d14Trace4
    writeSuccess15d14Trace5 writeSuccess15d14Trace6
    writeSuccess15d14Trace7 writeSuccess15d14Trace8
    writeSuccess15d14Trace9 writeSuccess15d14Trace10
    writeSuccess15d14Trace11 writeSuccess15d14Trace12
    writeSuccess15d14Trace13 writeSuccess15d14Trace14
    writeSuccess15d14Trace15 writeSuccess15d14TraceUpper
    writeSuccess15d14Trace16
    writeSuccess15d14Trace17 writeSuccess15d14Trace18
    writeSuccess15d14Trace19 writeSuccess15d14Trace20
    writeSuccess15d14Trace21 writeSuccess15d14Trace22
    writeSuccess15d14Trace23 writeSuccess15d14Trace24
    writeSuccess15d14Trace25 writeSuccess15d14Trace26
    writeSuccess15d14Trace27 writeSuccess15d14Trace28
    writeSuccess15d14Trace29 writeSuccess15d14Trace30
    writeSuccess15d14Trace31 writeSuccess15d14NextPc
    writeSuccess15d14Address writeSuccessTraceTail a15d14].

Lemma segment_15d14 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) (result : bool) old :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits value) ->
  writeSuccess15d14SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d14Address address)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionSegment (writeSuccess15d14Before regs global)
    (writeSuccess15d14Observations regs global mstatusBits address satp value result)
    (writeSuccess15d14After regs global address value) /\
  (writeSuccess15d14After regs global address value).1.(seq_regs) =
    writeSuccess15d14Regs regs /\
  (writeSuccess15d14After regs global address value).2.(seq_mem) =
    write_mem_list global.(seq_mem) (writeSuccess15d14Address address)
      (writeSuccess15d14Bytes value) /\
  concat (map microLabels
    (writeSuccess15d14Observations regs global mstatusBits address satp value result)) = [].
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx1 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d14Observations, writeSuccess15d14PrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d14Regs regs),
      writeSuccess15d14Global global address value))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d14), a15d14.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess15d14TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d14). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d14))
        (value := RVal_Bits (Z_to_bv 64 0x15d14));
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d14NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address)
        (value := RVal_Bits address);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (writeSuccess15d14Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
        (value := RVal_Bits satp);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
        (value := RVal_Bits value);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hx1|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBoolS with (b := result). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteMemBacked with
        (result := RVal_Bool result)
        (address := writeSuccess15d14Address address) (len := 8%N)
        (value := value);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|lia|eauto]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d14))
        (value := RVal_Bits writeSuccess15d14NextPc)
        (updated := RVal_Bits writeSuccess15d14NextPc).
      - reflexivity. - writeSuccess15d14TraceCbn. constructor.
      - exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d18) (trace := a15d18).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15d18). unfold writeSuccess15d14Regs.
      rewrite lookup_insert writeSuccess15d14NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d18), a15d18.
    cbn. unfold writeSuccess15d14Regs. rewrite lookup_insert.
    rewrite writeSuccess15d14NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_15d14_mmio (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) (result : bool) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits value) ->
  writeSuccess15d14SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d14Address address)) 8 = None ->
  (bv_unsigned (writeSuccess15d14Address address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item =>
    ~ (bv_unsigned (writeSuccess15d14Address address) <= bv_unsigned item <
       bv_unsigned (writeSuccess15d14Address address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionSegment (writeSuccess15d14Before regs global)
    (writeSuccess15d14MmioObservations regs global mstatusBits address satp value result)
    (writeSuccess15d14MmioAfter regs global) /\
  (writeSuccess15d14MmioAfter regs global).1.(seq_regs) =
    writeSuccess15d14Regs regs /\
  (writeSuccess15d14MmioAfter regs global).2.(seq_mem) =
    global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess15d14MmioObservations regs global mstatusBits address satp value result)) = [SWriteMem (writeSuccess15d14Address address) (bv_to_bvn value)].
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx1 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hrange Houtside Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d14MmioObservations, writeSuccess15d14MmioPrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d14Regs regs),
      global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d14), a15d14.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess15d14TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d14TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d14TraceCbn. apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d14). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d14))
        (value := RVal_Bits (Z_to_bv 64 0x15d14));
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d14NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address)
        (value := RVal_Bits address);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (writeSuccess15d14Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
        (value := RVal_Bits satp);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
        (value := RVal_Bits value);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|exact Hx1|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d14Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d14TraceCbn.
      apply DeclareConstBoolS with (b := result). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteMemMmio with
        (result := RVal_Bool result)
        (address := writeSuccess15d14Address address) (len := 8%N)
        (value := value);
        [reflexivity|writeSuccess15d14TraceCbn; constructor|lia|exact Hmem|
         exact Hrange|exact Houtside]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d14))
        (value := RVal_Bits writeSuccess15d14NextPc)
        (updated := RVal_Bits writeSuccess15d14NextPc).
      - reflexivity. - writeSuccess15d14TraceCbn. constructor.
      - exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d18) (trace := a15d18).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15d18). unfold writeSuccess15d14Regs.
      rewrite lookup_insert writeSuccess15d14NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d18), a15d18.
    cbn. unfold writeSuccess15d14Regs. rewrite lookup_insert.
    rewrite writeSuccess15d14NextPcExact Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess15d14NextPcExact.
Print Assumptions writeSuccess15d14RegsLookupOther.
Print Assumptions writeSuccess15d14RegsDom.
Print Assumptions segment_15d14.
Print Assumptions segment_15d14_mmio.
