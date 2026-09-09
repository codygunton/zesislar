From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a1019c.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess1019cLower : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x5" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 16)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.
Definition writeSuccess1019cUpper : a_exp :=
  AExp_Binop (Bvcomp Bvule)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x5" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 16)) Mk_annot] Mk_annot)
    (AExp_Binop (Bvarith Bvsub)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot;
         AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot)
      (AExp_Val (AVal_Bits (BV 64 8)) Mk_annot) Mk_annot) Mk_annot.

Definition writeSuccess1019cAlign : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 2 0)
      (AExp_Manyop (Bvmanyarith Bvadd)
        [AExp_Val (AVal_Var "x5" []) Mk_annot;
         AExp_Val (AVal_Bits (BV 64 16)) Mk_annot] Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 3 0)) Mk_annot) Mk_annot.

Definition writeSuccess1019cSysRegs (regs : reg_map) : Prop :=
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

Definition writeSuccess1019cNextPc : bv 64 :=
  (Z_to_bv 64 0x1019c + BV 64 4)%bv.
Definition writeSuccess1019cAddress (base : bv 64) : bv 64 :=
  (base + BV 64 16)%bv.
Definition writeSuccess1019cMemory (global : seq_global_state)
    (base value : bv 64) (outcome : WriteSuccessStoreOutcome) : mem_map :=
  writeSuccessStoreOutcomeMemory global (writeSuccess1019cAddress base)
    value outcome.
Definition writeSuccess1019cGlobal (global : seq_global_state)
    (base value : bv 64) (outcome : WriteSuccessStoreOutcome) :
    seq_global_state :=
  writeSuccessStoreOutcomeGlobal global (writeSuccess1019cAddress base)
    value outcome.

Definition writeSuccess1019cTrace1 := writeSuccessTraceTail a1019c.
Definition writeSuccess1019cTrace2 := writeSuccessTraceTail writeSuccess1019cTrace1.
Definition writeSuccess1019cTrace3 := writeSuccessTraceTail writeSuccess1019cTrace2.
Definition writeSuccess1019cTrace4 := writeSuccessTraceTail writeSuccess1019cTrace3.
Definition writeSuccess1019cTrace5 := writeSuccessTraceTail writeSuccess1019cTrace4.
Definition writeSuccess1019cTrace6 := writeSuccessTraceTail writeSuccess1019cTrace5.
Definition writeSuccess1019cTrace7 := writeSuccessTraceTail writeSuccess1019cTrace6.
Definition writeSuccess1019cTrace8 := writeSuccessTraceTail writeSuccess1019cTrace7.
Definition writeSuccess1019cTrace9 := writeSuccessTraceTail writeSuccess1019cTrace8.
Definition writeSuccess1019cTrace10 := writeSuccessTraceTail writeSuccess1019cTrace9.
Definition writeSuccess1019cTrace11 (mstatusBits : bv 64) :=
  subst_trace (Val_Bits mstatusBits) 2 (writeSuccessTraceTail writeSuccess1019cTrace10).
Definition writeSuccess1019cTrace12 (mstatusBits : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace11 mstatusBits).
Definition writeSuccess1019cTrace13 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits base) 3
    (writeSuccessTraceTail (writeSuccess1019cTrace12 mstatusBits)).
Definition writeSuccess1019cTrace14 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace13 mstatusBits base).
Definition writeSuccess1019cTrace15 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace14 mstatusBits base).
Definition writeSuccess1019cTrace16 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace15 mstatusBits base).
Definition writeSuccess1019cTrace17 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x1019c)) 4
    (writeSuccessTraceTail (writeSuccess1019cTrace16 mstatusBits base)).
Definition writeSuccess1019cTrace18 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace17 mstatusBits base).
Definition writeSuccess1019cTrace19 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits writeSuccess1019cNextPc) 5
    (writeSuccessTraceTail (writeSuccess1019cTrace18 mstatusBits base)).
Definition writeSuccess1019cTrace20 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace19 mstatusBits base).
Definition writeSuccess1019cTrace21 (mstatusBits base : bv 64) :=
  subst_trace (Val_Bits (writeSuccess1019cAddress base)) 6
    (writeSuccessTraceTail (writeSuccess1019cTrace20 mstatusBits base)).
Definition writeSuccess1019cTrace22 (mstatusBits base : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace21 mstatusBits base).
Definition writeSuccess1019cTrace23 (mstatusBits base satp : bv 64) :=
  subst_trace (Val_Bits satp) 19
    (writeSuccessTraceTail (writeSuccess1019cTrace22 mstatusBits base)).
Definition writeSuccess1019cTrace24 (mstatusBits base satp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace23 mstatusBits base satp).
Definition writeSuccess1019cTrace25 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits value) 24
    (writeSuccessTraceTail (writeSuccess1019cTrace24 mstatusBits base satp)).
Definition writeSuccess1019cTrace26 (mstatusBits base satp value : bv 64) :=
  writeSuccessTraceTail (writeSuccess1019cTrace25 mstatusBits base satp value).
Definition writeSuccess1019cTrace27 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess1019cAddress base))) 27
    (writeSuccessTraceTail (writeSuccess1019cTrace26 mstatusBits base satp value)).
Definition writeSuccess1019cTrace28 (mstatusBits base satp value : bv 64) :=
  subst_trace (Val_Bits (bv_zero_extend 128 (writeSuccess1019cAddress base))) 33
    (writeSuccessTraceTail (writeSuccess1019cTrace27 mstatusBits base satp value)).
Definition writeSuccess1019cTrace29 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  subst_trace (Val_Bool result) 37
    (writeSuccessTraceTail (writeSuccess1019cTrace28 mstatusBits base satp value)).
Definition writeSuccess1019cTrace30 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess1019cTrace29 mstatusBits base satp value result).
Definition writeSuccess1019cTrace31 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess1019cTrace30 mstatusBits base satp value result).
Definition writeSuccess1019cTrace32 (mstatusBits base satp value : bv 64)
    (result : bool) :=
  writeSuccessTraceTail (writeSuccess1019cTrace31 mstatusBits base satp value result).

Definition writeSuccess1019cRegs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess1019cNextPc]> regs.
Definition writeSuccess1019cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a1019c regs, global).
Definition writeSuccess1019cAfter (regs : reg_map)
    (global : seq_global_state) (address value : bv 64)
    (outcome : WriteSuccessStoreOutcome) : IslaState :=
  (writeSuccess15694Local a101a0 (writeSuccess1019cRegs regs),
   writeSuccess1019cGlobal global address value outcome).

Definition writeSuccess1019cObservation (labels : list seq_label)
    (local : seq_local_state) (global : seq_global_state) :
    IslaMicroObservation := {| microLabels := labels; microAfter := (local, global) |}.

Definition writeSuccess1019cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) (outcome : WriteSuccessStoreOutcome) :
    list IslaMicroObservation :=
  map (fun trace => writeSuccess1019cObservation []
    (writeSuccess15694Local trace regs) global)
    [writeSuccess1019cTrace1; writeSuccess1019cTrace2;
     writeSuccess1019cTrace3; writeSuccess1019cTrace4;
     writeSuccess1019cTrace5; writeSuccess1019cTrace6;
     writeSuccess1019cTrace7; writeSuccess1019cTrace8;
     writeSuccess1019cTrace9; writeSuccess1019cTrace10;
     writeSuccess1019cTrace11 mstatusBits;
     writeSuccess1019cTrace12 mstatusBits;
     writeSuccess1019cTrace13 mstatusBits address;
     writeSuccess1019cTrace14 mstatusBits address;
     writeSuccess1019cTrace15 mstatusBits address;
     writeSuccess1019cTrace16 mstatusBits address;
     writeSuccess1019cTrace17 mstatusBits address;
     writeSuccess1019cTrace18 mstatusBits address;
     writeSuccess1019cTrace19 mstatusBits address;
     writeSuccess1019cTrace20 mstatusBits address;
     writeSuccess1019cTrace21 mstatusBits address;
     writeSuccess1019cTrace22 mstatusBits address;
     writeSuccess1019cTrace23 mstatusBits address satp;
     writeSuccess1019cTrace24 mstatusBits address satp;
     writeSuccess1019cTrace25 mstatusBits address satp value;
     writeSuccess1019cTrace26 mstatusBits address satp value;
     writeSuccess1019cTrace27 mstatusBits address satp value;
     writeSuccess1019cTrace28 mstatusBits address satp value;
     writeSuccess1019cTrace29 mstatusBits address satp value result] ++
  [writeSuccess1019cObservation
     (writeSuccessStoreOutcomeLabels (writeSuccess1019cAddress address) value outcome)
     (writeSuccess15694Local
       (writeSuccess1019cTrace30 mstatusBits address satp value result) regs)
     (writeSuccess1019cGlobal global address value outcome);
   writeSuccess1019cObservation []
     (writeSuccess15694Local
       (writeSuccess1019cTrace31 mstatusBits address satp value result)
       (writeSuccess1019cRegs regs))
     (writeSuccess1019cGlobal global address value outcome)].

Definition writeSuccess1019cObservations (regs : reg_map)
    (global : seq_global_state) (mstatusBits address satp value : bv 64)
    (result : bool) (outcome : WriteSuccessStoreOutcome) :
    list IslaMicroObservation :=
  writeSuccess1019cPrefixObservations regs global mstatusBits address satp value
    result outcome ++
  [writeSuccess1019cObservation []
     (writeSuccess1019cAfter regs global address value outcome).1
     (writeSuccess1019cGlobal global address value outcome)].

Lemma writeSuccess1019cNextPcExact :
  writeSuccess1019cNextPc = Z_to_bv 64 0x101a0.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess1019cRegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess1019cRegs regs !! reg = regs !! reg.
Proof.
  intros Hpc. unfold writeSuccess1019cRegs.
  rewrite lookup_insert_ne; last congruence. reflexivity.
Qed.

Lemma writeSuccess1019cRegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1019c)) ->
  dom (writeSuccess1019cRegs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess1019cRegs.
  rewrite dom_insert_L. set_solver. Qed.

Ltac writeSuccess1019cTraceCbn :=
  cbn [writeSuccess1019cTrace1 writeSuccess1019cTrace2
    writeSuccess1019cTrace3 writeSuccess1019cTrace4
    writeSuccess1019cTrace5 writeSuccess1019cTrace6
    writeSuccess1019cTrace7 writeSuccess1019cTrace8
    writeSuccess1019cTrace9 writeSuccess1019cTrace10
    writeSuccess1019cTrace11 writeSuccess1019cTrace12
    writeSuccess1019cTrace13 writeSuccess1019cTrace14
    writeSuccess1019cTrace15 writeSuccess1019cTrace16
    writeSuccess1019cTrace17 writeSuccess1019cTrace18
    writeSuccess1019cTrace19 writeSuccess1019cTrace20
    writeSuccess1019cTrace21 writeSuccess1019cTrace22
    writeSuccess1019cTrace23 writeSuccess1019cTrace24
    writeSuccess1019cTrace25 writeSuccess1019cTrace26
    writeSuccess1019cTrace27 writeSuccess1019cTrace28
    writeSuccess1019cTrace29 writeSuccess1019cTrace30
    writeSuccess1019cTrace31 writeSuccess1019cTrace32
    writeSuccess1019cNextPc writeSuccess1019cAddress writeSuccessTraceTail a1019c].

Lemma segment_1019c (regs : reg_map) (global : seq_global_state)
    (mstatusBits base satp value : bv 64) (result : bool)
    (outcome : WriteSuccessStoreOutcome) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1019c)) ->
  regs !! "x5" = Some (RVal_Bits base) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x11" = Some (RVal_Bits value) ->
  writeSuccess1019cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cAlign = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cUpper = Some (Val_Bool true) ->
  writeSuccessStoreOutcomePermitted global (writeSuccess1019cAddress base)
    outcome ->
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c ->
  global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0 ->
  IslaInstructionSegment (writeSuccess1019cBefore regs global)
    (writeSuccess1019cObservations regs global mstatusBits base satp value
      result outcome)
    (writeSuccess1019cAfter regs global base value outcome) /\
  (writeSuccess1019cAfter regs global base value outcome).1.(seq_regs) =
    writeSuccess1019cRegs regs /\
  (writeSuccess1019cAfter regs global base value outcome).2.(seq_mem) =
    writeSuccessStoreOutcomeMemory global (writeSuccess1019cAddress base)
      value outcome /\
  concat (map microLabels
    (writeSuccess1019cObservations regs global mstatusBits base satp value
      result outcome)) =
    writeSuccessStoreOutcomeLabels (writeSuccess1019cAddress base) value outcome.
Proof.
  intros Hpc Hbase Hmstatus Hsatp Hvalue Hsys HmstatusAssume Halign
    Hlower Hupper Houtcome Hcode Hnext.
  destruct Hsys as
    (Hpmp & Hmisaligned & Hrambase & Hramsize & Hrombase & Hromsize &
     Hclintbase & Hclintsize & Htohost & Hpriv).
  destruct outcome; cbn in Houtcome |- *.
  - destruct Houtcome as [old Hmem].
    split; [|repeat split; reflexivity].
    unfold writeSuccess1019cObservations, writeSuccess1019cPrefixObservations.
    eapply islaInstructionSegmentIntro with
      (prefix := writeSuccess1019cPrefixObservations regs global mstatusBits
        base satp value result WriteSuccessStoreBacked)
      (done := (writeSuccess15694Local tnil (writeSuccess1019cRegs regs),
        writeSuccess1019cGlobal global base value WriteSuccessStoreBacked))
      (after := writeSuccess1019cAfter regs global base value
        WriteSuccessStoreBacked)
      (labels := []) (spawned := []).
    + split; first reflexivity. exists (Z_to_bv 64 0x1019c), a1019c.
      cbn. rewrite Hpc Hcode. repeat split; reflexivity.
    + do 10 (eapply IslaInstructionPrefixStep; first discriminate;
        [eapply writeSuccessSeqAssumeReg;
         [reflexivity|writeSuccess1019cTraceCbn; apply AssumeRegS|
          first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
            exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
            exact Htohost | exact Hpriv]|reflexivity]|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := mstatusBits). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact HmstatusAssume. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := base). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Halign. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Hlower. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Hupper. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x1019c). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RVal_Bits (Z_to_bv 64 0x1019c))
          (value := RVal_Bits (Z_to_bv 64 0x1019c));
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        eapply DefineConstS with (v := Val_Bits writeSuccess1019cNextPc). reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits base)
          (value := RVal_Bits base);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hbase|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        eapply DefineConstS with (v := Val_Bits (writeSuccess1019cAddress base)).
        reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
          (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := satp). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
          (value := RVal_Bits satp);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := value). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
          (value := RVal_Bits value);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hvalue|reflexivity|reflexivity]. }
      do 2 (eapply IslaInstructionPrefixStep; first discriminate;
        [apply writeSuccessSeqSilent; first reflexivity; writeSuccess1019cTraceCbn;
         eapply DefineConstS with
           (v := Val_Bits (bv_zero_extend 128 (writeSuccess1019cAddress base)));
         reflexivity|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBoolS with (b := result). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteMemBacked with
          (result := RVal_Bool result) (address := writeSuccess1019cAddress base)
          (len := 8%N) (value := value);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|lia|eauto]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteReg with
          (root := RVal_Bits (Z_to_bv 64 0x1019c))
          (value := RVal_Bits writeSuccess1019cNextPc)
          (updated := RVal_Bits writeSuccess1019cNextPc).
        - reflexivity. - writeSuccess1019cTraceCbn. constructor.
        - exact Hpc. - reflexivity. - reflexivity. }
      apply IslaInstructionPrefixRefl.
    + reflexivity.
    + apply writeSuccessSeqDoneTabled with (next := a101a0) (trace := a101a0).
      * reflexivity. * reflexivity. * constructor.
      * exists (Z_to_bv 64 0x101a0). unfold writeSuccess1019cRegs.
        rewrite lookup_insert writeSuccess1019cNextPcExact Hnext.
        repeat split; reflexivity.
    + left. split; first reflexivity. exists (Z_to_bv 64 0x101a0), a101a0.
      cbn. unfold writeSuccess1019cRegs. rewrite lookup_insert.
      rewrite writeSuccess1019cNextPcExact Hnext. repeat split; reflexivity.
  - destruct Houtcome as (Hnone & Hrange & Houtside).
    split; [|repeat split; reflexivity].
    unfold writeSuccess1019cObservations, writeSuccess1019cPrefixObservations.
    eapply islaInstructionSegmentIntro with
      (prefix := writeSuccess1019cPrefixObservations regs global mstatusBits
        base satp value result WriteSuccessStoreMmio)
      (done := (writeSuccess15694Local tnil (writeSuccess1019cRegs regs), global))
      (after := writeSuccess1019cAfter regs global base value
        WriteSuccessStoreMmio)
      (labels := []) (spawned := []).
    + split; first reflexivity. exists (Z_to_bv 64 0x1019c), a1019c.
      cbn. rewrite Hpc Hcode. repeat split; reflexivity.
    + do 10 (eapply IslaInstructionPrefixStep; first discriminate;
        [eapply writeSuccessSeqAssumeReg;
         [reflexivity|writeSuccess1019cTraceCbn; apply AssumeRegS|
          first [exact Hpmp | exact Hmisaligned | exact Hrambase | exact Hramsize |
            exact Hrombase | exact Hromsize | exact Hclintbase | exact Hclintsize |
            exact Htohost | exact Hpriv]|reflexivity]|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := mstatusBits). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact HmstatusAssume. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := base). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Halign. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Hlower. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqAssume; first reflexivity. writeSuccess1019cTraceCbn.
        eapply AssumeS. exact Hupper. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x1019c). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RVal_Bits (Z_to_bv 64 0x1019c))
          (value := RVal_Bits (Z_to_bv 64 0x1019c));
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hpc|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        eapply DefineConstS with (v := Val_Bits writeSuccess1019cNextPc). reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits base)
          (value := RVal_Bits base);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hbase|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        eapply DefineConstS with (v := Val_Bits (writeSuccess1019cAddress base)).
        reflexivity. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with
          (root := RegVal_Struct [("bits", RVal_Bits mstatusBits)])
          (value := RegVal_Struct [("bits", RVal_Bits mstatusBits)]);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hmstatus|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := satp). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits satp)
          (value := RVal_Bits satp);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hsatp|reflexivity|reflexivity]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBitVecS' with (b := value). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqReadReg with (root := RVal_Bits value)
          (value := RVal_Bits value);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|exact Hvalue|reflexivity|reflexivity]. }
      do 2 (eapply IslaInstructionPrefixStep; first discriminate;
        [apply writeSuccessSeqSilent; first reflexivity; writeSuccess1019cTraceCbn;
         eapply DefineConstS with
           (v := Val_Bits (bv_zero_extend 128 (writeSuccess1019cAddress base)));
         reflexivity|]).
      eapply IslaInstructionPrefixStep; first discriminate.
      { apply writeSuccessSeqSilent; first reflexivity. writeSuccess1019cTraceCbn.
        apply DeclareConstBoolS with (b := result). }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteMemMmio with
          (result := RVal_Bool result) (address := writeSuccess1019cAddress base)
          (len := 8%N) (value := value);
          [reflexivity|writeSuccess1019cTraceCbn; constructor|lia|exact Hnone|
           exact Hrange|exact Houtside]. }
      eapply IslaInstructionPrefixStep; first discriminate.
      { eapply writeSuccessSeqWriteReg with
          (root := RVal_Bits (Z_to_bv 64 0x1019c))
          (value := RVal_Bits writeSuccess1019cNextPc)
          (updated := RVal_Bits writeSuccess1019cNextPc).
        - reflexivity. - writeSuccess1019cTraceCbn. constructor.
        - exact Hpc. - reflexivity. - reflexivity. }
      apply IslaInstructionPrefixRefl.
    + reflexivity.
    + apply writeSuccessSeqDoneTabled with (next := a101a0) (trace := a101a0).
      * reflexivity. * reflexivity. * constructor.
      * exists (Z_to_bv 64 0x101a0). unfold writeSuccess1019cRegs.
        rewrite lookup_insert writeSuccess1019cNextPcExact Hnext.
        repeat split; reflexivity.
    + left. split; first reflexivity. exists (Z_to_bv 64 0x101a0), a101a0.
      cbn. unfold writeSuccess1019cRegs. rewrite lookup_insert.
      rewrite writeSuccess1019cNextPcExact Hnext. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess1019cNextPcExact.
Print Assumptions writeSuccess1019cRegsLookupOther.
Print Assumptions writeSuccess1019cRegsDom.
Print Assumptions segment_1019c.
