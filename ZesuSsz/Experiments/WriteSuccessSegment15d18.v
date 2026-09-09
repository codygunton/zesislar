From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d18.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d18Aligned : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x2" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d18Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess15d18Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x2" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess15d18SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess15d18NextPc : bv 64 :=
  (Z_to_bv 64 0x15d18 + BV 64 4)%bv.
Definition writeSuccess15d18Address (sp : bv 64) : bv 64 :=
  (sp + BV 64 0)%bv.
Definition writeSuccess15d18Bytes (value : bv 64) : list (bv 8) :=
  bv_to_little_endian 8 8 (bv_unsigned value).
Definition writeSuccess15d18Memory (global : seq_global_state)
    (address value : bv 64) : mem_map :=
  write_mem_list global.(seq_mem) (writeSuccess15d18Address address)
    (writeSuccess15d18Bytes value).
Definition writeSuccess15d18Global (global : seq_global_state)
    (address value : bv 64) : seq_global_state :=
  global <| seq_mem := writeSuccess15d18Memory global address value |>.

Definition writeSuccess15d18Trace1 := writeSuccessTraceTail a15d18.
Definition writeSuccess15d18Trace2 := writeSuccessTraceTail writeSuccess15d18Trace1.
Definition writeSuccess15d18Trace3 := writeSuccessTraceTail writeSuccess15d18Trace2.
Definition writeSuccess15d18Trace4 := writeSuccessTraceTail writeSuccess15d18Trace3.
Definition writeSuccess15d18Trace5 := writeSuccessTraceTail writeSuccess15d18Trace4.
Definition writeSuccess15d18Trace6 := writeSuccessTraceTail writeSuccess15d18Trace5.
Definition writeSuccess15d18Trace7 := writeSuccessTraceTail writeSuccess15d18Trace6.
Definition writeSuccess15d18Trace8 := writeSuccessTraceTail writeSuccess15d18Trace7.
Definition writeSuccess15d18Trace9 := writeSuccessTraceTail writeSuccess15d18Trace8.
Definition writeSuccess15d18Trace10 := writeSuccessTraceTail writeSuccess15d18Trace9.
Definition writeSuccess15d18Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess15d18Trace10).
Definition writeSuccess15d18Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace11 mstatusBits).
Definition writeSuccess15d18Trace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess15d18Trace12 mstatusBits)).
Definition writeSuccess15d18Trace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace13 mstatusBits address).
Definition writeSuccess15d18Trace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace14 mstatusBits address).
Definition writeSuccess15d18TraceUpper (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace15 mstatusBits address).
Definition writeSuccess15d18Trace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d18)) 4
    (writeSuccessTraceTail (writeSuccess15d18TraceUpper mstatusBits address)).
Definition writeSuccess15d18Trace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace16 mstatusBits address).
Definition writeSuccess15d18Trace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess15d18NextPc) 5
    (writeSuccessTraceTail (writeSuccess15d18Trace17 mstatusBits address)).
Definition writeSuccess15d18Trace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace18 mstatusBits address).
Definition writeSuccess15d18Trace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (writeSuccess15d18Address address)) 6
    (writeSuccessTraceTail (writeSuccess15d18Trace19 mstatusBits address)).
Definition writeSuccess15d18Trace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace20 mstatusBits address).
Definition writeSuccess15d18Trace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess15d18Trace21 mstatusBits address)).
Definition writeSuccess15d18Trace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace22 mstatusBits address satp).
Definition writeSuccess15d18Trace24 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 24
    (writeSuccessTraceTail (writeSuccess15d18Trace23 mstatusBits address satp)).
Definition writeSuccess15d18Trace25 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d18Trace24 mstatusBits address satp value).
Definition writeSuccess15d18Trace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 19
    (writeSuccessTraceTail (writeSuccess15d18Trace25 mstatusBits address satp value)).
Definition writeSuccess15d18Trace27 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))) 27
    (writeSuccessTraceTail (writeSuccess15d18Trace25 mstatusBits address satp value)).
Definition writeSuccess15d18Trace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))) 33
    (writeSuccessTraceTail (writeSuccess15d18Trace27 mstatusBits address satp value)).
Definition writeSuccess15d18Trace29 (mstatusBits address satp value : bv 64) (result : bool) :=
  subst_trace (Val_Bool result) 37
    (writeSuccessTraceTail (writeSuccess15d18Trace28 mstatusBits address satp value)).
Definition writeSuccess15d18Trace30 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess15d18Trace29 mstatusBits address satp value result).
Definition writeSuccess15d18Trace31 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess15d18Trace30 mstatusBits address satp value result).

Definition writeSuccess15d18Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d18NextPc]> regs.
Definition writeSuccess15d18Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d18 regs, global).
Definition writeSuccess15d18After (regs : reg_map)
    (global : seq_global_state) (address value : bv 64) : IslaState :=
  (writeSuccess15694Local a15d1c (writeSuccess15d18Regs regs),
   writeSuccess15d18Global global address value).

Definition writeSuccess15d18PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18Trace1; writeSuccess15d18Trace2;
     writeSuccess15d18Trace3; writeSuccess15d18Trace4;
     writeSuccess15d18Trace5; writeSuccess15d18Trace6;
     writeSuccess15d18Trace7; writeSuccess15d18Trace8;
     writeSuccess15d18Trace9; writeSuccess15d18Trace10;
     writeSuccess15d18Trace11 mstatusBits;
     writeSuccess15d18Trace12 mstatusBits;
     writeSuccess15d18Trace13 mstatusBits address;
     writeSuccess15d18Trace14 mstatusBits address;
     writeSuccess15d18Trace15 mstatusBits address;
     writeSuccess15d18TraceUpper mstatusBits address;
     writeSuccess15d18Trace16 mstatusBits address;
     writeSuccess15d18Trace17 mstatusBits address;
     writeSuccess15d18Trace18 mstatusBits address;
     writeSuccess15d18Trace19 mstatusBits address;
     writeSuccess15d18Trace20 mstatusBits address;
     writeSuccess15d18Trace21 mstatusBits address;
     writeSuccess15d18Trace22 mstatusBits address satp;
     writeSuccess15d18Trace23 mstatusBits address satp;
     writeSuccess15d18Trace24 mstatusBits address satp value;
     writeSuccess15d18Trace25 mstatusBits address satp value;
     writeSuccess15d18Trace27 mstatusBits address satp value;
     writeSuccess15d18Trace28 mstatusBits address satp value;
     writeSuccess15d18Trace29 mstatusBits address satp value result] ++
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace30 mstatusBits address satp value result) regs)
     (writeSuccess15d18Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace31 mstatusBits address satp value result)
       (writeSuccess15d18Regs regs))
     (writeSuccess15d18Global global address value)].

Definition writeSuccess15d18Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  writeSuccess15d18PrefixObservations regs global mstatusBits address satp value result ++
  [writeSuccess15694Observation
     (writeSuccess15d18After regs global address value).1
     (writeSuccess15d18Global global address value)].

Definition writeSuccess15d18MmioAfter (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15d1c (writeSuccess15d18Regs regs), global).

Definition writeSuccess15d18MmioPrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18Trace1; writeSuccess15d18Trace2;
     writeSuccess15d18Trace3; writeSuccess15d18Trace4;
     writeSuccess15d18Trace5; writeSuccess15d18Trace6;
     writeSuccess15d18Trace7; writeSuccess15d18Trace8;
     writeSuccess15d18Trace9; writeSuccess15d18Trace10;
     writeSuccess15d18Trace11 mstatusBits;
     writeSuccess15d18Trace12 mstatusBits;
     writeSuccess15d18Trace13 mstatusBits address;
     writeSuccess15d18Trace14 mstatusBits address;
     writeSuccess15d18Trace15 mstatusBits address;
     writeSuccess15d18TraceUpper mstatusBits address;
     writeSuccess15d18Trace16 mstatusBits address;
     writeSuccess15d18Trace17 mstatusBits address;
     writeSuccess15d18Trace18 mstatusBits address;
     writeSuccess15d18Trace19 mstatusBits address;
     writeSuccess15d18Trace20 mstatusBits address;
     writeSuccess15d18Trace21 mstatusBits address;
     writeSuccess15d18Trace22 mstatusBits address satp;
     writeSuccess15d18Trace23 mstatusBits address satp;
     writeSuccess15d18Trace24 mstatusBits address satp value;
     writeSuccess15d18Trace25 mstatusBits address satp value;
     writeSuccess15d18Trace27 mstatusBits address satp value;
     writeSuccess15d18Trace28 mstatusBits address satp value;
     writeSuccess15d18Trace29 mstatusBits address satp value result] ++
  [ {| microLabels :=
        [SWriteMem (writeSuccess15d18Address address) (bv_to_bvn value)];
      microAfter :=
        (writeSuccess15694Local
          (writeSuccess15d18Trace30 mstatusBits address satp value result) regs,
         global) |};
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace31 mstatusBits address satp value result)
       (writeSuccess15d18Regs regs)) global].

Definition writeSuccess15d18MmioObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  writeSuccess15d18MmioPrefixObservations regs global mstatusBits address satp
    value result ++
  [writeSuccess15694Observation
     (writeSuccess15d18MmioAfter regs global).1 global].

Lemma writeSuccess15d18NextPcExact :
  writeSuccess15d18NextPc = Z_to_bv 64 0x15d1c.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess15d18RegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess15d18Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc. unfold writeSuccess15d18Regs.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess15d18RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  dom (writeSuccess15d18Regs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess15d18Regs.
  rewrite dom_insert_L. set_solver. Qed.

Ltac writeSuccess15d18TraceCbn :=
  cbv [writeSuccess15d18Trace1 writeSuccess15d18Trace2
    writeSuccess15d18Trace3 writeSuccess15d18Trace4
    writeSuccess15d18Trace5 writeSuccess15d18Trace6
    writeSuccess15d18Trace7 writeSuccess15d18Trace8
    writeSuccess15d18Trace9 writeSuccess15d18Trace10
    writeSuccess15d18Trace11 writeSuccess15d18Trace12
    writeSuccess15d18Trace13 writeSuccess15d18Trace14
    writeSuccess15d18Trace15 writeSuccess15d18TraceUpper
    writeSuccess15d18Trace16
    writeSuccess15d18Trace17 writeSuccess15d18Trace18
    writeSuccess15d18Trace19 writeSuccess15d18Trace20
    writeSuccess15d18Trace21 writeSuccess15d18Trace22
    writeSuccess15d18Trace23 writeSuccess15d18Trace24
    writeSuccess15d18Trace25 writeSuccess15d18Trace26
    writeSuccess15d18Trace27 writeSuccess15d18Trace28
    writeSuccess15d18Trace29 writeSuccess15d18Trace30
    writeSuccess15d18Trace31 writeSuccess15d18NextPc
    writeSuccess15d18Address writeSuccessTraceTail a15d18].

Lemma segment_15d18 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) (result : bool) old :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  writeSuccess15d18SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d18Address address)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  IslaInstructionSegment (writeSuccess15d18Before regs global)
    (writeSuccess15d18Observations regs global mstatusBits address satp value result)
    (writeSuccess15d18After regs global address value) /\
  (writeSuccess15d18After regs global address value).1.(seq_regs) =
    writeSuccess15d18Regs regs /\
  (writeSuccess15d18After regs global address value).2.(seq_mem) =
    write_mem_list global.(seq_mem) (writeSuccess15d18Address address)
      (writeSuccess15d18Bytes value) /\
  concat (map microLabels
    (writeSuccess15d18Observations regs global mstatusBits address satp value result)) = [].
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx10 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d18Observations, writeSuccess15d18PrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d18Regs regs),
      writeSuccess15d18Global global address value))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d18), a15d18.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess15d18TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d18). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d18))
        (value := RVal_Bits (Z_to_bv 64 0x15d18));
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d18NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address)
        (value := RVal_Bits address);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (writeSuccess15d18Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
        (value := RVal_Bits satp);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
        (value := RVal_Bits value);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hx10|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBoolS with (b := result). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteMemBacked with
        (result := RVal_Bool result)
        (address := writeSuccess15d18Address address) (len := 8%N)
        (value := value);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|lia|eauto]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d18))
        (value := RVal_Bits writeSuccess15d18NextPc)
        (updated := RVal_Bits writeSuccess15d18NextPc).
      - reflexivity. - writeSuccess15d18TraceCbn. constructor.
      - exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d1c) (trace := a15d1c).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15d1c). unfold writeSuccess15d18Regs.
      rewrite lookup_insert writeSuccess15d18NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d1c), a15d1c.
    cbn. unfold writeSuccess15d18Regs. rewrite lookup_insert.
    rewrite writeSuccess15d18NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_15d18_mmio (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) (result : bool) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  writeSuccess15d18SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d18Address address)) 8 = None ->
  (bv_unsigned (writeSuccess15d18Address address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item =>
    ~ (bv_unsigned (writeSuccess15d18Address address) <= bv_unsigned item <
       bv_unsigned (writeSuccess15d18Address address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  IslaInstructionSegment (writeSuccess15d18Before regs global)
    (writeSuccess15d18MmioObservations regs global mstatusBits address satp value result)
    (writeSuccess15d18MmioAfter regs global) /\
  (writeSuccess15d18MmioAfter regs global).1.(seq_regs) =
    writeSuccess15d18Regs regs /\
  (writeSuccess15d18MmioAfter regs global).2.(seq_mem) =
    global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess15d18MmioObservations regs global mstatusBits address satp value result)) = [SWriteMem (writeSuccess15d18Address address) (bv_to_bvn value)].
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx10 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hrange Houtside Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d18MmioObservations, writeSuccess15d18MmioPrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15d18Regs regs),
      global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d18), a15d18.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess15d18TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Haligned. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess15d18TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess15d18TraceCbn. apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d18). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d18))
        (value := RVal_Bits (Z_to_bv 64 0x15d18));
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess15d18NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address)
        (value := RVal_Bits address);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hx2|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (writeSuccess15d18Address address)). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
        (value := RVal_Bits satp);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
        (value := RVal_Bits value);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|exact Hx10|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 (writeSuccess15d18Address address))).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess15d18TraceCbn.
      apply DeclareConstBoolS with (b := result). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteMemMmio with
        (result := RVal_Bool result)
        (address := writeSuccess15d18Address address) (len := 8%N)
        (value := value);
        [reflexivity|writeSuccess15d18TraceCbn; constructor|lia|exact Hmem|
         exact Hrange|exact Houtside]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d18))
        (value := RVal_Bits writeSuccess15d18NextPc)
        (updated := RVal_Bits writeSuccess15d18NextPc).
      - reflexivity. - writeSuccess15d18TraceCbn. constructor.
      - exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d1c) (trace := a15d1c).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15d1c). unfold writeSuccess15d18Regs.
      rewrite lookup_insert writeSuccess15d18NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d1c), a15d1c.
    cbn. unfold writeSuccess15d18Regs. rewrite lookup_insert.
    rewrite writeSuccess15d18NextPcExact Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess15d18NextPcExact.
Print Assumptions writeSuccess15d18RegsLookupOther.
Print Assumptions writeSuccess15d18RegsDom.
Print Assumptions segment_15d18.
Print Assumptions segment_15d18_mmio.
