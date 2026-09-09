From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10198.
Require Import IslaTraces.write_success_01.a1019c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess10198Lower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x5" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess10198Upper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x5" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess10198Align : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x5" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 8)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess10198SysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess10198NextPc : bv 64 :=
  (Z_to_bv 64 0x10198 + BV 64 4)%bv.
Definition writeSuccess10198Address (base : bv 64) : bv 64 :=
  (base + BV 64 8)%bv.
Definition writeSuccess10198Memory (global : seq_global_state)
    (base value : bv 64) (outcome : WriteSuccessStoreOutcome) : mem_map :=
  writeSuccessStoreOutcomeMemory global (writeSuccess10198Address base)
    value outcome.
Definition writeSuccess10198Global (global : seq_global_state)
    (base value : bv 64) (outcome : WriteSuccessStoreOutcome) :
    seq_global_state :=
  writeSuccessStoreOutcomeGlobal global (writeSuccess10198Address base)
    value outcome.

Definition writeSuccess10198Trace1 := writeSuccessTraceTail a10198.
Definition writeSuccess10198Trace2 := writeSuccessTraceTail writeSuccess10198Trace1.
Definition writeSuccess10198Trace3 := writeSuccessTraceTail writeSuccess10198Trace2.
Definition writeSuccess10198Trace4 := writeSuccessTraceTail writeSuccess10198Trace3.
Definition writeSuccess10198Trace5 := writeSuccessTraceTail writeSuccess10198Trace4.
Definition writeSuccess10198Trace6 := writeSuccessTraceTail writeSuccess10198Trace5.
Definition writeSuccess10198Trace7 := writeSuccessTraceTail writeSuccess10198Trace6.
Definition writeSuccess10198Trace8 := writeSuccessTraceTail writeSuccess10198Trace7.
Definition writeSuccess10198Trace9 := writeSuccessTraceTail writeSuccess10198Trace8.
Definition writeSuccess10198Trace10 := writeSuccessTraceTail writeSuccess10198Trace9.
Definition writeSuccess10198Trace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess10198Trace10).
Definition writeSuccess10198Trace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace11 mstatusBits).
Definition writeSuccess10198Trace13 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits base) 3
    (writeSuccessTraceTail (writeSuccess10198Trace12 mstatusBits)).
Definition writeSuccess10198Trace14 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace13 mstatusBits base).
Definition writeSuccess10198Trace15 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace14 mstatusBits base).
Definition writeSuccess10198Trace16 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace15 mstatusBits base).
Definition writeSuccess10198Trace17 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x10198)) 4
    (writeSuccessTraceTail (writeSuccess10198Trace16 mstatusBits base)).
Definition writeSuccess10198Trace18 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace17 mstatusBits base).
Definition writeSuccess10198Trace19 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits writeSuccess10198NextPc) 5
    (writeSuccessTraceTail (writeSuccess10198Trace18 mstatusBits base)).
Definition writeSuccess10198Trace20 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace19 mstatusBits base).
Definition writeSuccess10198Trace21 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits (writeSuccess10198Address base)) 6
    (writeSuccessTraceTail (writeSuccess10198Trace20 mstatusBits base)).
Definition writeSuccess10198Trace22 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace21 mstatusBits base).
Definition writeSuccess10198Trace23 (mstatusBits base satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess10198Trace22 mstatusBits base)).
Definition writeSuccess10198Trace24 (mstatusBits base satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace23 mstatusBits base satp).
Definition writeSuccess10198Trace25 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits value) 24
    (writeSuccessTraceTail (writeSuccess10198Trace24 mstatusBits base satp)).
Definition writeSuccess10198Trace26 (mstatusBits base satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess10198Trace25 mstatusBits base satp value).
Definition writeSuccess10198Trace27 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess10198Address base))) 27
    (writeSuccessTraceTail (writeSuccess10198Trace26 mstatusBits base satp value)).
Definition writeSuccess10198Trace28 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess10198Address base))) 33
    (writeSuccessTraceTail (writeSuccess10198Trace27 mstatusBits base satp value)).
Definition writeSuccess10198Trace29 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  subst_trace (Val_Bool result) 37
    (writeSuccessTraceTail (writeSuccess10198Trace28 mstatusBits base satp value)).
Definition writeSuccess10198Trace30 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess10198Trace29 mstatusBits base satp value result).
Definition writeSuccess10198Trace31 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess10198Trace30 mstatusBits base satp value result).
Definition writeSuccess10198Trace32 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess10198Trace31 mstatusBits base satp value result).

Definition writeSuccess10198Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess10198NextPc]> regs.
Definition writeSuccess10198Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a10198 regs, global).
Definition writeSuccess10198After (regs : reg_map)
    (global : seq_global_state) (address value : bv 64)
    (outcome : WriteSuccessStoreOutcome) : IslaState :=
  (writeSuccess15694Local a1019c (writeSuccess10198Regs regs),
   writeSuccess10198Global global address value outcome).

Definition writeSuccess10198Observation (labels : list seq_label)
    (local : seq_local_state) (global : seq_global_state) :
    IslaMicroObservation := {| microLabels := labels; microAfter := (local, global) |}.

Definition writeSuccess10198PrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) (outcome : WriteSuccessStoreOutcome) :
    list IslaMicroObservation :=
  map (fun trace => writeSuccess10198Observation []
    (writeSuccess15694Local trace regs) global)
    [writeSuccess10198Trace1; writeSuccess10198Trace2;
     writeSuccess10198Trace3; writeSuccess10198Trace4;
     writeSuccess10198Trace5; writeSuccess10198Trace6;
     writeSuccess10198Trace7; writeSuccess10198Trace8;
     writeSuccess10198Trace9; writeSuccess10198Trace10;
     writeSuccess10198Trace11 mstatusBits;
     writeSuccess10198Trace12 mstatusBits;
     writeSuccess10198Trace13 mstatusBits address;
     writeSuccess10198Trace14 mstatusBits address;
     writeSuccess10198Trace15 mstatusBits address;
     writeSuccess10198Trace16 mstatusBits address;
     writeSuccess10198Trace17 mstatusBits address;
     writeSuccess10198Trace18 mstatusBits address;
     writeSuccess10198Trace19 mstatusBits address;
     writeSuccess10198Trace20 mstatusBits address;
     writeSuccess10198Trace21 mstatusBits address;
     writeSuccess10198Trace22 mstatusBits address;
     writeSuccess10198Trace23 mstatusBits address satp;
     writeSuccess10198Trace24 mstatusBits address satp;
     writeSuccess10198Trace25 mstatusBits address satp value;
     writeSuccess10198Trace26 mstatusBits address satp value;
     writeSuccess10198Trace27 mstatusBits address satp value;
     writeSuccess10198Trace28 mstatusBits address satp value;
     writeSuccess10198Trace29 mstatusBits address satp value result] ++
  [writeSuccess10198Observation
     (writeSuccessStoreOutcomeLabels (writeSuccess10198Address address) value outcome)
     (writeSuccess15694Local
       (writeSuccess10198Trace30 mstatusBits address satp value result) regs)
     (writeSuccess10198Global global address value outcome);
   writeSuccess10198Observation []
     (writeSuccess15694Local
       (writeSuccess10198Trace31 mstatusBits address satp value result)
       (writeSuccess10198Regs regs))
     (writeSuccess10198Global global address value outcome)].

Definition writeSuccess10198Observations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) (outcome : WriteSuccessStoreOutcome) :
    list IslaMicroObservation :=
  writeSuccess10198PrefixObservations regs global mstatusBits address satp value
    result outcome ++
  [writeSuccess10198Observation []
     (writeSuccess10198After regs global address value outcome).1
     (writeSuccess10198Global global address value outcome)].

Lemma writeSuccess10198NextPcExact :
  writeSuccess10198NextPc = Z_to_bv 64 0x1019c.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess10198RegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess10198Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc. unfold writeSuccess10198Regs.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess10198RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  dom (writeSuccess10198Regs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess10198Regs.
  rewrite dom_insert_L. set_solver. Qed.

Ltac writeSuccess10198TraceCbn :=
  cbn [writeSuccess10198Trace1 writeSuccess10198Trace2
    writeSuccess10198Trace3 writeSuccess10198Trace4
    writeSuccess10198Trace5 writeSuccess10198Trace6
    writeSuccess10198Trace7 writeSuccess10198Trace8
    writeSuccess10198Trace9 writeSuccess10198Trace10
    writeSuccess10198Trace11 writeSuccess10198Trace12
    writeSuccess10198Trace13 writeSuccess10198Trace14
    writeSuccess10198Trace15 writeSuccess10198Trace16
    writeSuccess10198Trace17 writeSuccess10198Trace18
    writeSuccess10198Trace19 writeSuccess10198Trace20
    writeSuccess10198Trace21 writeSuccess10198Trace22
    writeSuccess10198Trace23 writeSuccess10198Trace24
    writeSuccess10198Trace25 writeSuccess10198Trace26
    writeSuccess10198Trace27 writeSuccess10198Trace28
    writeSuccess10198Trace29 writeSuccess10198Trace30
    writeSuccess10198Trace31 writeSuccess10198Trace32
    writeSuccess10198NextPc writeSuccess10198Address writeSuccessTraceTail a10198].

Lemma segment_10198 (regs : reg_map) (global : seq_global_state)
    (mstatusBits base satp value : bv 64) (result : bool)
    (outcome : WriteSuccessStoreOutcome) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  regs !! "x5" = Some (RVal_Bits base) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  writeSuccess10198SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Align = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Upper = Some (Val_Bool true) ->
  writeSuccessStoreOutcomePermitted global (writeSuccess10198Address base)
    outcome ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c ->
  IslaInstructionSegment (writeSuccess10198Before regs global)
    (writeSuccess10198Observations regs global mstatusBits base satp value
      result outcome)
    (writeSuccess10198After regs global base value outcome) /\
  (writeSuccess10198After regs global base value outcome).1.(seq_regs) =
    writeSuccess10198Regs regs /\
  (writeSuccess10198After regs global base value outcome).2.(seq_mem) =
    writeSuccessStoreOutcomeMemory global (writeSuccess10198Address base)
      value outcome /\
  concat (map microLabels
    (writeSuccess10198Observations regs global mstatusBits base satp value
      result outcome)) =
    writeSuccessStoreOutcomeLabels (writeSuccess10198Address base) value outcome.
Proof.
  intros Hpc Hbase Hmstatus Hsatp Hvalue Hsys HmstatusAssume Halign
    Hlower Hupper Houtcome Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  destruct outcome; cbn in Houtcome |- *.
  - destruct Houtcome as [old Hmem].
    split; [|repeat split; reflexivity].
    unfold writeSuccess10198Observations, writeSuccess10198PrefixObservations.
    eapply islaInstructionSegmentIntro with
      (prefix := writeSuccess10198PrefixObservations regs global mstatusBits
        base satp value result WriteSuccessStoreBacked)
      (done := (writeSuccess15694Local tnil (writeSuccess10198Regs regs),
        writeSuccess10198Global global base value WriteSuccessStoreBacked))
      (after := writeSuccess10198After regs global base value
        WriteSuccessStoreBacked)
      (labels := []) (spawned := []).
    + split; first reflexivity. exists (Z_to_bv 64 0x10198), a10198.
      cbn. rewrite Hpc Hcode. repeat split; reflexivity.
    + do 10 (eapply IslaInstructionPrefixStep; first discriminate;
        [eapply writeSuccessSeqAssumeReg;
         [reflexivity|writeSuccess10198TraceCbn; apply AssumeRegS|
          first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
            exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
            exact Htohost | exact Hpriv]|reflexivity]|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := mstatusBits). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact HmstatusAssume. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := base). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Halign. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Hlower. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Hupper. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x10198). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RVal_Bits (Z_to_bv 64 0x10198))
          (value := RVal_Bits (Z_to_bv 64 0x10198));
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        eapply DefineConstS with (v := Val_Bits writeSuccess10198NextPc). reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits base)
          (value := RVal_Bits base);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hbase|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        eapply DefineConstS with (v := Val_Bits (writeSuccess10198Address base)).
        reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
          (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := satp). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
          (value := RVal_Bits satp);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := value). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
          (value := RVal_Bits value);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hvalue|reflexivity|reflexivity]. }
      do 2 (eapply IslaInstructionPrefixStep; first discriminate;
        [apply writeSuccessSeqSilent; first reflexivity; writeSuccess10198TraceCbn;
         eapply DefineConstS with
           (v := Val_Bits (bv_zero_extend 128 (writeSuccess10198Address base)));
         reflexivity|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBoolS with (b := result). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteMemBacked with
          (result := RVal_Bool result) (address := writeSuccess10198Address base)
          (len := 8%N) (value := value);
          [reflexivity|writeSuccess10198TraceCbn; constructor|lia|eauto]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteReg with
          (root := RVal_Bits (Z_to_bv 64 0x10198))
          (value := RVal_Bits writeSuccess10198NextPc)
          (updated := RVal_Bits writeSuccess10198NextPc).
        - reflexivity. - writeSuccess10198TraceCbn. constructor.
        - exact Hpc. - reflexivity. - reflexivity. }
      apply IslaInstructionPrefixRefl.
    + reflexivity.
    + apply writeSuccessSeqDoneTabled with (next := a1019c) (trace := a1019c).
      * reflexivity. * reflexivity. * constructor.
      * exists (Z_to_bv 64 0x1019c). unfold writeSuccess10198Regs.
        rewrite lookup_insert writeSuccess10198NextPcExact Hnext.
        repeat split; reflexivity.
    + left. split; first reflexivity. exists (Z_to_bv 64 0x1019c), a1019c.
      cbn. unfold writeSuccess10198Regs. rewrite lookup_insert.
      rewrite writeSuccess10198NextPcExact Hnext. repeat split; reflexivity.
  - destruct Houtcome as (Hnone & Hrange & Houtside).
    split; [|repeat split; reflexivity].
    unfold writeSuccess10198Observations, writeSuccess10198PrefixObservations.
    eapply islaInstructionSegmentIntro with
      (prefix := writeSuccess10198PrefixObservations regs global mstatusBits
        base satp value result WriteSuccessStoreMmio)
      (done := (writeSuccess15694Local tnil (writeSuccess10198Regs regs), global))
      (after := writeSuccess10198After regs global base value
        WriteSuccessStoreMmio)
      (labels := []) (spawned := []).
    + split; first reflexivity. exists (Z_to_bv 64 0x10198), a10198.
      cbn. rewrite Hpc Hcode. repeat split; reflexivity.
    + do 10 (eapply IslaInstructionPrefixStep; first discriminate;
        [eapply writeSuccessSeqAssumeReg;
         [reflexivity|writeSuccess10198TraceCbn; apply AssumeRegS|
          first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
            exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
            exact Htohost | exact Hpriv]|reflexivity]|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := mstatusBits). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact HmstatusAssume. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := base). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Halign. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Hlower. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess10198TraceCbn.
        eapply AssumeS. exact Hupper. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x10198). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RVal_Bits (Z_to_bv 64 0x10198))
          (value := RVal_Bits (Z_to_bv 64 0x10198));
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        eapply DefineConstS with (v := Val_Bits writeSuccess10198NextPc). reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits base)
          (value := RVal_Bits base);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hbase|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        eapply DefineConstS with (v := Val_Bits (writeSuccess10198Address base)).
        reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
          (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := satp). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
          (value := RVal_Bits satp);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBitVecS' with (b := value). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
          (value := RVal_Bits value);
          [reflexivity|writeSuccess10198TraceCbn; constructor|exact Hvalue|reflexivity|reflexivity]. }
      do 2 (eapply IslaInstructionPrefixStep; first discriminate;
        [apply writeSuccessSeqSilent; first reflexivity; writeSuccess10198TraceCbn;
         eapply DefineConstS with
           (v := Val_Bits (bv_zero_extend 128 (writeSuccess10198Address base)));
         reflexivity|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess10198TraceCbn.
        apply DeclareConstBoolS with (b := result). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteMemMmio with
          (result := RVal_Bool result) (address := writeSuccess10198Address base)
          (len := 8%N) (value := value);
          [reflexivity|writeSuccess10198TraceCbn; constructor|lia|exact Hnone|
           exact Hrange|exact Houtside]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteReg with
          (root := RVal_Bits (Z_to_bv 64 0x10198))
          (value := RVal_Bits writeSuccess10198NextPc)
          (updated := RVal_Bits writeSuccess10198NextPc).
        - reflexivity. - writeSuccess10198TraceCbn. constructor.
        - exact Hpc. - reflexivity. - reflexivity. }
      apply IslaInstructionPrefixRefl.
    + reflexivity.
    + apply writeSuccessSeqDoneTabled with (next := a1019c) (trace := a1019c).
      * reflexivity. * reflexivity. * constructor.
      * exists (Z_to_bv 64 0x1019c). unfold writeSuccess10198Regs.
        rewrite lookup_insert writeSuccess10198NextPcExact Hnext.
        repeat split; reflexivity.
    + left. split; first reflexivity. exists (Z_to_bv 64 0x1019c), a1019c.
      cbn. unfold writeSuccess10198Regs. rewrite lookup_insert.
      rewrite writeSuccess10198NextPcExact Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess10198NextPcExact.
Print Assumptions writeSuccess10198RegsLookupOther.
Print Assumptions writeSuccess10198RegsDom.
Print Assumptions segment_10198.
