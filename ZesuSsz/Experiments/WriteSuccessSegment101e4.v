From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e4.
Require Import IslaTraces.write_success_02.a101e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101e4Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x13" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess101e4Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x13" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 1)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess101e4SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess101e4NextPc : bv 64 :=
  (Z_to_bv 64 0x101e4 + BV 64 4)%bv.
Definition writeSuccess101e4Loaded (byte : bv 8) : bv 64 :=
  bv_zero_extend 64 byte.

Definition writeSuccess101e4Trace1 := writeSuccessTraceTail a101e4.
Definition writeSuccess101e4Trace2 := writeSuccessTraceTail writeSuccess101e4Trace1.
Definition writeSuccess101e4Trace3 := writeSuccessTraceTail writeSuccess101e4Trace2.
Definition writeSuccess101e4Trace4 := writeSuccessTraceTail writeSuccess101e4Trace3.
Definition writeSuccess101e4Trace5 := writeSuccessTraceTail writeSuccess101e4Trace4.
Definition writeSuccess101e4Trace6 := writeSuccessTraceTail writeSuccess101e4Trace5.
Definition writeSuccess101e4Trace7 := writeSuccessTraceTail writeSuccess101e4Trace6.
Definition writeSuccess101e4Trace8 := writeSuccessTraceTail writeSuccess101e4Trace7.
Definition writeSuccess101e4Trace9 := writeSuccessTraceTail writeSuccess101e4Trace8.
Definition writeSuccess101e4Trace10 := writeSuccessTraceTail writeSuccess101e4Trace9.
Definition writeSuccess101e4Trace11 mstatusBits :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess101e4Trace10).
Definition writeSuccess101e4Trace12 mstatusBits :=
  writeSuccessTraceTail (writeSuccess101e4Trace11 mstatusBits).
Definition writeSuccess101e4Trace13 mstatusBits address :=
  subst_trace (Val_Bits address) 3
    (writeSuccessTraceTail (writeSuccess101e4Trace12 mstatusBits)).
Definition writeSuccess101e4Trace14 mstatusBits address :=
  writeSuccessTraceTail (writeSuccess101e4Trace13 mstatusBits address).
Definition writeSuccess101e4Trace15 mstatusBits address :=
  writeSuccessTraceTail (writeSuccess101e4Trace14 mstatusBits address).
Definition writeSuccess101e4Trace16 mstatusBits address :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101e4)) 4
    (writeSuccessTraceTail (writeSuccess101e4Trace15 mstatusBits address)).
Definition writeSuccess101e4Trace17 mstatusBits address :=
  writeSuccessTraceTail (writeSuccess101e4Trace16 mstatusBits address).
Definition writeSuccess101e4Trace18 mstatusBits address :=
  subst_trace (Val_Bits writeSuccess101e4NextPc) 5
    (writeSuccessTraceTail (writeSuccess101e4Trace17 mstatusBits address)).
Definition writeSuccess101e4Trace19 mstatusBits address :=
  writeSuccessTraceTail (writeSuccess101e4Trace18 mstatusBits address).
Definition writeSuccess101e4Trace20 mstatusBits address :=
  subst_trace (Val_Bits address) 6
    (writeSuccessTraceTail (writeSuccess101e4Trace19 mstatusBits address)).
Definition writeSuccess101e4Trace21 mstatusBits address :=
  writeSuccessTraceTail (writeSuccess101e4Trace20 mstatusBits address).
Definition writeSuccess101e4Trace22 mstatusBits address satp :=
  subst_trace (Val_Bits satp) 13
    (writeSuccessTraceTail (writeSuccess101e4Trace21 mstatusBits address)).
Definition writeSuccess101e4Trace23 mstatusBits address satp :=
  writeSuccessTraceTail (writeSuccess101e4Trace22 mstatusBits address satp).
Definition writeSuccess101e4Trace24 mstatusBits (address : bv 64) satp :=
  subst_trace (Val_Bits (bv_zero_extend 128 address)) 20
    (writeSuccessTraceTail (writeSuccess101e4Trace23 mstatusBits address satp)).
Definition writeSuccess101e4Trace25 mstatusBits (address : bv 64) satp :=
  subst_trace (Val_Bits (bv_zero_extend 128 address)) 26
    (writeSuccessTraceTail (writeSuccess101e4Trace24 mstatusBits address satp)).
Definition writeSuccess101e4Trace26 mstatusBits address satp byte :=
  subst_trace (Val_Bits byte) 30
    (writeSuccessTraceTail (writeSuccess101e4Trace25 mstatusBits address satp)).
Definition writeSuccess101e4Trace27 mstatusBits address satp byte :=
  writeSuccessTraceTail (writeSuccess101e4Trace26 mstatusBits address satp byte).
Definition writeSuccess101e4Trace28 mstatusBits address satp byte :=
  subst_trace (Val_Bits (writeSuccess101e4Loaded byte)) 31
    (writeSuccessTraceTail (writeSuccess101e4Trace27 mstatusBits address satp byte)).
Definition writeSuccess101e4Trace29 mstatusBits address satp byte :=
  writeSuccessTraceTail (writeSuccess101e4Trace28 mstatusBits address satp byte).
Definition writeSuccess101e4Trace30 mstatusBits address satp byte :=
  writeSuccessTraceTail (writeSuccess101e4Trace29 mstatusBits address satp byte).

Definition writeSuccess101e4Regs (regs : reg_map) (byte : bv 8) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101e4NextPc]>
    (<["x13" := RVal_Bits (writeSuccess101e4Loaded byte)]> regs).
Definition writeSuccess101e4Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a101e4 regs, global).
Definition writeSuccess101e4After (regs : reg_map)
    (global : seq_global_state) (byte : bv 8) : IslaState :=
  (writeSuccess15694Local a101e8 (writeSuccess101e4Regs regs byte), global).

Definition writeSuccess101e4PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp : bv 64)
    (byte : bv 8) : list IslaMicroObservation :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess101e4Trace1; writeSuccess101e4Trace2;
     writeSuccess101e4Trace3; writeSuccess101e4Trace4;
     writeSuccess101e4Trace5; writeSuccess101e4Trace6;
     writeSuccess101e4Trace7; writeSuccess101e4Trace8;
     writeSuccess101e4Trace9; writeSuccess101e4Trace10;
     writeSuccess101e4Trace11 mstatusBits;
     writeSuccess101e4Trace12 mstatusBits;
     writeSuccess101e4Trace13 mstatusBits address;
     writeSuccess101e4Trace14 mstatusBits address;
     writeSuccess101e4Trace15 mstatusBits address;
     writeSuccess101e4Trace16 mstatusBits address;
     writeSuccess101e4Trace17 mstatusBits address;
     writeSuccess101e4Trace18 mstatusBits address;
     writeSuccess101e4Trace19 mstatusBits address;
     writeSuccess101e4Trace20 mstatusBits address;
     writeSuccess101e4Trace21 mstatusBits address;
     writeSuccess101e4Trace22 mstatusBits address satp;
     writeSuccess101e4Trace23 mstatusBits address satp;
     writeSuccess101e4Trace24 mstatusBits address satp;
     writeSuccess101e4Trace25 mstatusBits address satp;
     writeSuccess101e4Trace26 mstatusBits address satp byte;
     writeSuccess101e4Trace27 mstatusBits address satp byte;
     writeSuccess101e4Trace28 mstatusBits address satp byte] ++
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace29 mstatusBits address satp byte)
       (<["x13" := RVal_Bits (writeSuccess101e4Loaded byte)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace30 mstatusBits address satp byte)
       (writeSuccess101e4Regs regs byte)) global].

Definition writeSuccess101e4Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp : bv 64)
    (byte : bv 8) : list IslaMicroObservation :=
  writeSuccess101e4PrefixObservations regs global mstatusBits address satp byte ++
  [writeSuccess15694Observation (writeSuccess101e4After regs global byte).1 global].

Lemma writeSuccess101e4NextPcExact :
  writeSuccess101e4NextPc = Z_to_bv 64 0x101e8.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess101e4RegsLookupOther regs byte reg :
  reg <> "PC" -> reg <> "x13" ->
  writeSuccess101e4Regs regs byte !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess101e4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess101e4RegsDom regs address byte :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e4)) ->
  regs !! "x13" = Some (RVal_Bits address) ->
  dom (writeSuccess101e4Regs regs byte) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc.
  apply elem_of_dom_2 in Hdest. unfold writeSuccess101e4Regs.
  rewrite !dom_insert_L. set_solver. Qed.

Ltac writeSuccess101e4TraceCbn :=
  cbn [writeSuccess101e4Trace1 writeSuccess101e4Trace2
    writeSuccess101e4Trace3 writeSuccess101e4Trace4
    writeSuccess101e4Trace5 writeSuccess101e4Trace6
    writeSuccess101e4Trace7 writeSuccess101e4Trace8
    writeSuccess101e4Trace9 writeSuccess101e4Trace10
    writeSuccess101e4Trace11 writeSuccess101e4Trace12
    writeSuccess101e4Trace13 writeSuccess101e4Trace14
    writeSuccess101e4Trace15 writeSuccess101e4Trace16
    writeSuccess101e4Trace17 writeSuccess101e4Trace18
    writeSuccess101e4Trace19 writeSuccess101e4Trace20
    writeSuccess101e4Trace21 writeSuccess101e4Trace22
    writeSuccess101e4Trace23 writeSuccess101e4Trace24
    writeSuccess101e4Trace25 writeSuccess101e4Trace26
    writeSuccess101e4Trace27 writeSuccess101e4Trace28
    writeSuccess101e4Trace29 writeSuccess101e4Trace30
    writeSuccess101e4NextPc writeSuccess101e4Loaded
    writeSuccessTraceTail a101e4].

Lemma segment_101e4 (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp : bv 64) (byte : bv 8) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e4)) ->
  regs !! "x13" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  writeSuccess101e4SysRegs regs ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some (bv_to_bvn byte) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101e4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101e4Upper = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e4Before regs global)
    (writeSuccess101e4Observations regs global mstatusBits address satp byte)
    (writeSuccess101e4After regs global byte) /\
  (writeSuccess101e4After regs global byte).1.(seq_regs) =
    writeSuccess101e4Regs regs byte /\
  (writeSuccess101e4After regs global byte).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess101e4Observations regs global mstatusBits address satp byte)) = [].
Proof.
  intros Hpc Hx13 Hmstatus Hsatp Hsys Hmem Hcode Hnext
    HmstatusAssume Hlower Hupper.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  split; [|repeat split; reflexivity].
  unfold writeSuccess101e4Observations, writeSuccess101e4PrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess101e4Regs regs byte), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101e4), a101e4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - do 10 (eapply IslaInstructionPrefixStep; first discriminate;
      [eapply writeSuccessSeqAssumeReg;
       [reflexivity|writeSuccess101e4TraceCbn; apply AssumeRegS|
        first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
          exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
          exact Htohost | exact Hpriv]|reflexivity]|]).
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn. apply DeclareConstBitVecS' with (b := mstatusBits). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101e4TraceCbn. eapply AssumeS. exact HmstatusAssume. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn. apply DeclareConstBitVecS' with (b := address). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101e4TraceCbn. eapply AssumeS. exact Hlower. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      writeSuccess101e4TraceCbn. eapply AssumeS. exact Hupper. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101e4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x101e4))
        (value := RVal_Bits (Z_to_bv 64 0x101e4));
        [reflexivity|writeSuccess101e4TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      eapply DefineConstS with (v := Val_Bits writeSuccess101e4NextPc).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits address) (value := RVal_Bits address);
        [reflexivity|writeSuccess101e4TraceCbn; constructor|exact Hx13|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      eapply DefineConstS with (v := Val_Bits address). cbn.
      destruct (decide (64%N = 64%N)) as [Heq|Hneq].
      - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
        have -> : (bv_add address (BV 64 0)) = address by bv_solve.
        reflexivity.
      - exfalso. apply Hneq. reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
        (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
        [reflexivity|writeSuccess101e4TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn. apply DeclareConstBitVecS' with (b := satp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits satp) (value := RVal_Bits satp);
        [reflexivity|writeSuccess101e4TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 address)). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      eapply DefineConstS with
        (v := Val_Bits (bv_zero_extend 128 address)). reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn. apply DeclareConstBitVecS' with (b := byte). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadMemBacked with
        (address := address) (len := 1%N) (value := byte);
        [reflexivity|writeSuccess101e4TraceCbn; constructor|lia|exact Hmem]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      writeSuccess101e4TraceCbn.
      eapply DefineConstS with (v := Val_Bits (writeSuccess101e4Loaded byte)).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits address)
        (value := RVal_Bits (writeSuccess101e4Loaded byte))
        (updated := RVal_Bits (writeSuccess101e4Loaded byte));
        [reflexivity|writeSuccess101e4TraceCbn; constructor|exact Hx13|reflexivity|reflexivity]. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x101e4))
        (value := RVal_Bits writeSuccess101e4NextPc)
        (updated := RVal_Bits writeSuccess101e4NextPc).
      - reflexivity. - writeSuccess101e4TraceCbn. constructor.
      - unfold writeSuccess101e4Regs. rewrite lookup_insert_ne; last congruence.
        exact Hpc.
      - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101e8) (trace := a101e8).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101e8). unfold writeSuccess101e4Regs.
      rewrite lookup_insert. rewrite writeSuccess101e4NextPcExact. rewrite Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101e8), a101e8.
    cbn. unfold writeSuccess101e4Regs. rewrite lookup_insert.
    rewrite writeSuccess101e4NextPcExact. rewrite Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess101e4NextPcExact.
Print Assumptions writeSuccess101e4RegsLookupOther.
Print Assumptions writeSuccess101e4RegsDom.
Print Assumptions segment_101e4.
