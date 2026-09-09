From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101f0.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101f0Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x14" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess101f0Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x14" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 1)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess101f0SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess101f0NextPc : bv 64 :=
  (Z_to_bv 64 0x101f0 + BV 64 4)%bv.
Definition writeSuccess101f0Byte (value : bv 64) : bv 8 := bv_extract 0 8 value.
Definition writeSuccess101f0Bytes (value : bv 64) : list (bv 8) :=
  bv_to_little_endian 1 8 (bv_unsigned (writeSuccess101f0Byte value)).
Definition writeSuccess101f0Memory (global : seq_global_state)
    (address value : bv 64) : mem_map :=
  write_mem_list global.(seq_mem) address (writeSuccess101f0Bytes value).
Definition writeSuccess101f0Global (global : seq_global_state)
    (address value : bv 64) : seq_global_state :=
  global <| seq_mem := writeSuccess101f0Memory global address value |>.

Definition writeSuccess101f0Trace1 := writeSuccessTraceTail a101f0.
Definition writeSuccess101f0Trace2 := writeSuccessTraceTail writeSuccess101f0Trace1.
Definition writeSuccess101f0Trace3 := writeSuccessTraceTail writeSuccess101f0Trace2.
Definition writeSuccess101f0Trace4 := writeSuccessTraceTail writeSuccess101f0Trace3.
Definition writeSuccess101f0Trace5 := writeSuccessTraceTail writeSuccess101f0Trace4.
Definition writeSuccess101f0Trace6 := writeSuccessTraceTail writeSuccess101f0Trace5.
Definition writeSuccess101f0Trace7 := writeSuccessTraceTail writeSuccess101f0Trace6.
Definition writeSuccess101f0Trace8 := writeSuccessTraceTail writeSuccess101f0Trace7.
Definition writeSuccess101f0Trace9 := writeSuccessTraceTail writeSuccess101f0Trace8.
Definition writeSuccess101f0Trace10 := writeSuccessTraceTail writeSuccess101f0Trace9.
Definition writeSuccess101f0Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess101f0Trace10).
Definition writeSuccess101f0Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace11 mstatusBits).
Definition writeSuccess101f0Trace13 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess101f0Trace12 mstatusBits)).
Definition writeSuccess101f0Trace14 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace13 mstatusBits address).
Definition writeSuccess101f0Trace15 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace14 mstatusBits address).
Definition writeSuccess101f0Trace16 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101f0)) 4
    (writeSuccessTraceTail (writeSuccess101f0Trace15 mstatusBits address)).
Definition writeSuccess101f0Trace17 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace16 mstatusBits address).
Definition writeSuccess101f0Trace18 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits writeSuccess101f0NextPc) 5
    (writeSuccessTraceTail (writeSuccess101f0Trace17 mstatusBits address)).
Definition writeSuccess101f0Trace19 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace18 mstatusBits address).
Definition writeSuccess101f0Trace20 (mstatusBits address : bv 64) :=
  subst_trace (Val_Bits address) 6
    (writeSuccessTraceTail (writeSuccess101f0Trace19 mstatusBits address)).
Definition writeSuccess101f0Trace21 (mstatusBits address : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace20 mstatusBits address).
Definition writeSuccess101f0Trace22 (mstatusBits address satp : bv 64) :=
  subst_trace (Val_Bits satp) 13
    (writeSuccessTraceTail (writeSuccess101f0Trace21 mstatusBits address)).
Definition writeSuccess101f0Trace23 (mstatusBits address satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace22 mstatusBits address satp).
Definition writeSuccess101f0Trace24 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits value) 18
    (writeSuccessTraceTail (writeSuccess101f0Trace23 mstatusBits address satp)).
Definition writeSuccess101f0Trace25 (mstatusBits address satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess101f0Trace24 mstatusBits address satp value).
Definition writeSuccess101f0Trace26 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (writeSuccess101f0Byte value)) 19
    (writeSuccessTraceTail (writeSuccess101f0Trace25 mstatusBits address satp value)).
Definition writeSuccess101f0Trace27 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 address)) 22
    (writeSuccessTraceTail (writeSuccess101f0Trace26 mstatusBits address satp value)).
Definition writeSuccess101f0Trace28 (mstatusBits address satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 address)) 28
    (writeSuccessTraceTail (writeSuccess101f0Trace27 mstatusBits address satp value)).
Definition writeSuccess101f0Trace29 (mstatusBits address satp value : bv 64) (result : bool) :=
  subst_trace (Val_Bool result) 32
    (writeSuccessTraceTail (writeSuccess101f0Trace28 mstatusBits address satp value)).
Definition writeSuccess101f0Trace30 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess101f0Trace29 mstatusBits address satp value result).
Definition writeSuccess101f0Trace31 (mstatusBits address satp value : bv 64) (result : bool) :=
  writeSuccessTraceTail (writeSuccess101f0Trace30 mstatusBits address satp value result).

Definition writeSuccess101f0Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101f0NextPc]> regs.
Definition writeSuccess101f0Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a101f0 regs, global).
Definition writeSuccess101f0After (regs : reg_map)
    (global : seq_global_state) (address value : bv 64) : IslaState :=
  (writeSuccess15694Local a101f4 (writeSuccess101f0Regs regs),
   writeSuccess101f0Global global address value).

Definition writeSuccess101f0PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess101f0Trace1; writeSuccess101f0Trace2;
     writeSuccess101f0Trace3; writeSuccess101f0Trace4;
     writeSuccess101f0Trace5; writeSuccess101f0Trace6;
     writeSuccess101f0Trace7; writeSuccess101f0Trace8;
     writeSuccess101f0Trace9; writeSuccess101f0Trace10;
     writeSuccess101f0Trace11 mstatusBits;
     writeSuccess101f0Trace12 mstatusBits;
     writeSuccess101f0Trace13 mstatusBits address;
     writeSuccess101f0Trace14 mstatusBits address;
     writeSuccess101f0Trace15 mstatusBits address;
     writeSuccess101f0Trace16 mstatusBits address;
     writeSuccess101f0Trace17 mstatusBits address;
     writeSuccess101f0Trace18 mstatusBits address;
     writeSuccess101f0Trace19 mstatusBits address;
     writeSuccess101f0Trace20 mstatusBits address;
     writeSuccess101f0Trace21 mstatusBits address;
     writeSuccess101f0Trace22 mstatusBits address satp;
     writeSuccess101f0Trace23 mstatusBits address satp;
     writeSuccess101f0Trace24 mstatusBits address satp value;
     writeSuccess101f0Trace25 mstatusBits address satp value;
     writeSuccess101f0Trace26 mstatusBits address satp value;
     writeSuccess101f0Trace27 mstatusBits address satp value;
     writeSuccess101f0Trace28 mstatusBits address satp value;
     writeSuccess101f0Trace29 mstatusBits address satp value result] ++
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101f0Trace30 mstatusBits address satp value result) regs)
     (writeSuccess101f0Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101f0Trace31 mstatusBits address satp value result)
       (writeSuccess101f0Regs regs))
     (writeSuccess101f0Global global address value)].

Definition writeSuccess101f0Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) : list IslaMicroObservation :=
  writeSuccess101f0PrefixObservations regs global mstatusBits address satp value result ++
  [writeSuccess15694Observation
     (writeSuccess101f0After regs global address value).1
     (writeSuccess101f0Global global address value)].

Lemma writeSuccess101f0NextPcExact :
  writeSuccess101f0NextPc = Z_to_bv 64 0x101f4.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess101f0RegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess101f0Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc. unfold writeSuccess101f0Regs.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess101f0RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f0)) ->
  dom (writeSuccess101f0Regs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess101f0Regs.
  rewrite dom_insert_L. set_solver. Qed.

Ltac writeSuccess101f0TraceCbn :=
  cbn [writeSuccess101f0Trace1 writeSuccess101f0Trace2
    writeSuccess101f0Trace3 writeSuccess101f0Trace4
    writeSuccess101f0Trace5 writeSuccess101f0Trace6
    writeSuccess101f0Trace7 writeSuccess101f0Trace8
    writeSuccess101f0Trace9 writeSuccess101f0Trace10
    writeSuccess101f0Trace11 writeSuccess101f0Trace12
    writeSuccess101f0Trace13 writeSuccess101f0Trace14
    writeSuccess101f0Trace15 writeSuccess101f0Trace16
    writeSuccess101f0Trace17 writeSuccess101f0Trace18
    writeSuccess101f0Trace19 writeSuccess101f0Trace20
    writeSuccess101f0Trace21 writeSuccess101f0Trace22
    writeSuccess101f0Trace23 writeSuccess101f0Trace24
    writeSuccess101f0Trace25 writeSuccess101f0Trace26
    writeSuccess101f0Trace27 writeSuccess101f0Trace28
    writeSuccess101f0Trace29 writeSuccess101f0Trace30
    writeSuccess101f0Trace31 writeSuccess101f0NextPc
    writeSuccess101f0Byte writeSuccessTraceTail a101f0].

Lemma segment_101f0 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) (result : bool) old :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f0)) ->
  regs !! "x14" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x13" = Some (RVal_Bits value) ->
  writeSuccess101f0SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101f0Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101f0Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  IslaInstructionSegment (writeSuccess101f0Before regs global)
    (writeSuccess101f0Observations regs global mstatusBits address satp value result)
    (writeSuccess101f0After regs global address value) /\
  (writeSuccess101f0After regs global address value).1.(seq_regs) =
    writeSuccess101f0Regs regs /\
  (writeSuccess101f0After regs global address value).2.(seq_mem) =
    write_mem_list global.(seq_mem) address (writeSuccess101f0Bytes value) /\
  concat (map microLabels
    (writeSuccess101f0Observations regs global mstatusBits address satp value result)) = [].
Proof.
  intros Hpc Hx14 Hmstatus Hsatp Hx13 Hsys HmstatusAssume Hlower Hupper
    Hmem Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess101f0Observations, writeSuccess101f0PrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess101f0Regs regs),
      writeSuccess101f0Global global address value))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101f0), a101f0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess101f0TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101f0TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101f0TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101f0TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101f0TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101f0TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101f0TraceCbn. apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101f0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x101f0))
        (value := RVal_Bits (Z_to_bv 64 0x101f0));
        [reflexivity|writeSuccess101f0TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess101f0NextPc). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits address)
        (value := RVal_Bits address);
        [reflexivity|writeSuccess101f0TraceCbn; constructor|exact Hx14|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      eapply DefineConstS with (v := Val_Bits address). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        have -> : (bv_add address (BV 64 0)) = address by bv_solve. reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess101f0TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
        (value := RVal_Bits satp);
        [reflexivity|writeSuccess101f0TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      apply DeclareConstBitVecS' with (b := value). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
        (value := RVal_Bits value);
        [reflexivity|writeSuccess101f0TraceCbn; constructor|exact Hx13|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      eapply DefineConstS with (v := Val_Bits (writeSuccess101f0Byte value)). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128 address)). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      eapply DefineConstS with (v := Val_Bits (bv_zero_extend 128 address)). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity. writeSuccess101f0TraceCbn.
      apply DeclareConstBoolS with (b := result). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteMemBacked with
        (result := RVal_Bool result) (address := address) (len := 1%N)
        (value := writeSuccess101f0Byte value);
        [reflexivity|writeSuccess101f0TraceCbn; constructor|lia|eauto]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x101f0))
        (value := RVal_Bits writeSuccess101f0NextPc)
        (updated := RVal_Bits writeSuccess101f0NextPc).
      - reflexivity. - writeSuccess101f0TraceCbn. constructor.
      - exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101f4) (trace := a101f4).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101f4). unfold writeSuccess101f0Regs.
      rewrite lookup_insert writeSuccess101f0NextPcExact Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101f4), a101f4.
    cbn. unfold writeSuccess101f0Regs. rewrite lookup_insert.
    rewrite writeSuccess101f0NextPcExact Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess101f0NextPcExact.
Print Assumptions writeSuccess101f0RegsLookupOther.
Print Assumptions writeSuccess101f0RegsDom.
Print Assumptions segment_101f0.
