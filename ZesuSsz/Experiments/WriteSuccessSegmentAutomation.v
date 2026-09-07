From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Import ListNotations.

Ltac writeSuccessTraceStep :=
  first [ eapply DeclareConstBitVecS'
        | eapply DeclareConstBoolS
        | eapply DeclareConstEnumS
        | eapply DefineConstS
        | eapply AssertS
        | eapply AssumeS
        | eapply AssumeRegS
        | eapply ReadRegS
        | eapply WriteRegS
        | eapply ReadMemS
        | eapply WriteMemS
        | eapply BranchAddressS
        | eapply BranchS
        | eapply CasesES
        | eapply DoneES ].

Lemma writeSuccessSeqSilent local global trace' :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs) None trace' ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace. eapply (SeqStep global local None trace' None); [exact Hnb | exact Htrace |].
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqAssume local global trace' :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs) (Some (LAssume true)) trace' ->
  seq_step local global []
    (local <| seq_trace := trace' |> <| seq_nb_state := false |>) global [].
Proof.
  intros Hnb Htrace. eapply (SeqStep global local (Some (LAssume true)) trace' None);
    [exact Hnb | exact Htrace |].
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqAssertTrue local global trace' :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs) (Some (LAssert true)) trace' ->
  seq_step local global []
    (local <| seq_trace := trace' |> <| seq_nb_state := false |>) global [].
Proof.
  intros Hnb Htrace. eapply (SeqStep global local (Some (LAssert true)) trace' None);
    [exact Hnb | exact Htrace |].
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqAssumeReg local global trace' register access expected root :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LAssumeReg register access expected)) trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access root = Some expected ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace Hregister Haccess.
  eapply (SeqStep global local (Some (LAssumeReg register access expected)) trace' None);
    [exact Hnb | exact Htrace |].
  simpl. exists root. repeat split; assumption || reflexivity.
Qed.

Lemma writeSuccessSeqReadReg local global trace' register access symbolic root value :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LReadReg register access symbolic)) trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access root = Some value ->
  read_accessor access symbolic = Some value ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace Hregister Hroot Hsymbolic.
  eapply (SeqStep global local (Some (LReadReg register access symbolic)) trace' None);
    [exact Hnb | exact Htrace |].
  simpl. exists root, value, value. repeat split; try assumption; try reflexivity.
  left. split; reflexivity.
Qed.

Lemma writeSuccessSeqWriteReg local global trace' register access symbolic
    root value updated :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LWriteReg register access symbolic)) trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access symbolic = Some value ->
  write_accessor access root value = Some updated ->
  seq_step local global []
    (local <| seq_trace := trace' |>
      <| seq_regs := <[register := updated]> local.(seq_regs) |>) global [].
Proof.
  intros Hnb Htrace Hregister Hread Hwrite.
  eapply (SeqStep global local (Some (LWriteReg register access symbolic)) trace' None);
    [exact Hnb | exact Htrace |].
  simpl. exists root, updated, value. repeat split; assumption || reflexivity.
Qed.

Lemma writeSuccessSeqBranchAddress local global trace' target :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LBranchAddress target)) trace' ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace.
  eapply (SeqStep global local (Some (LBranchAddress target)) trace' None);
    [exact Hnb | exact Htrace |].
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqBranch local global trace' branch description :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LBranch branch description)) trace' ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace.
  eapply (SeqStep global local (Some (LBranch branch description)) trace' None);
    [exact Hnb | exact Htrace |].
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqReadMemBacked local global trace' kind
    (address : bv 64) len tag (value : bv (8 * len)) :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag)) trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len =
    Some (bv_to_bvn value) ->
  seq_step local global [] (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace Hlen Hread.
  eapply (SeqStep global local
    (Some (LReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag)) trace' None);
    [exact Hnb | exact Htrace |].
  simpl. exists address, value, value. repeat split; try assumption; try reflexivity.
  rewrite Hread. repeat split; try assumption; try reflexivity.
  left. split; reflexivity.
Qed.

Lemma writeSuccessSeqReadMemMmio local global trace' kind
    (address : bv 64) len tag (value : bv (8 * len)) :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag)) trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = None ->
  (bv_unsigned address + Z.of_N len <= 2 ^ 64)%Z ->
  set_Forall
    (fun item => ~ (bv_unsigned address <= bv_unsigned item <
      bv_unsigned address + Z.of_N len)%Z) (dom global.(seq_mem)) ->
  seq_step local global [SReadMem address (bv_to_bvn value)]
    (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace Hlen Hnone Hrange Houtside.
  eapply (SeqStep global local
    (Some (LReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag)) trace'
    (Some (SReadMem address (bv_to_bvn value))));
    [exact Hnb | exact Htrace |].
  simpl. exists address, value, value. repeat split; try assumption; try reflexivity.
  rewrite Hnone. repeat split; assumption || reflexivity.
Qed.

Lemma writeSuccessSeqWriteMemBacked local global trace' result kind
    (address : bv 64) len tag (value : bv (8 * len)) :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LWriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag)) trace' ->
  (0 < Z.of_N len)%Z ->
  (exists old, read_mem global.(seq_mem) (bv_unsigned address) len = Some old) ->
  seq_step local global [] (local <| seq_trace := trace' |>)
    (global <| seq_mem := write_mem len global.(seq_mem) address
      (bv_unsigned value) |>) [].
Proof.
  intros Hnb Htrace Hlen [old Hread].
  eapply (SeqStep global local
    (Some (LWriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag)) trace' None);
    [exact Hnb | exact Htrace |].
  simpl. eexists (write_mem len global.(seq_mem) address (bv_unsigned value)),
    address, value.
  repeat split; try assumption; try reflexivity.
  rewrite Hread. repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqWriteMemMmio local global trace' result kind
    (address : bv 64) len tag (value : bv (8 * len)) :
  local.(seq_nb_state) = false ->
  trace_step local.(seq_trace) local.(seq_regs)
    (Some (LWriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag)) trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = None ->
  (bv_unsigned address + Z.of_N len <= 2 ^ 64)%Z ->
  set_Forall
    (fun item => ~ (bv_unsigned address <= bv_unsigned item <
      bv_unsigned address + Z.of_N len)%Z) (dom global.(seq_mem)) ->
  seq_step local global [SWriteMem address (bv_to_bvn value)]
    (local <| seq_trace := trace' |>) global [].
Proof.
  intros Hnb Htrace Hlen Hnone Hrange Houtside.
  eapply (SeqStep global local
    (Some (LWriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag)) trace'
    (Some (SWriteMem address (bv_to_bvn value))));
    [exact Hnb | exact Htrace |].
  simpl. eexists global.(seq_mem), address, value.
  repeat split; try assumption; try reflexivity.
  rewrite Hnone. repeat split; assumption || reflexivity.
Qed.

Lemma writeSuccessSeqDoneTabled local global next trace :
  local.(seq_nb_state) = false ->
  local.(seq_trace) = tnil ->
  trace_step local.(seq_trace) local.(seq_regs) (Some (LDone next)) next ->
  (exists pc : bv 64,
    local.(seq_regs) !! local.(seq_pc_reg) = Some (RVal_Bits pc) /\
    global.(seq_instrs) !! pc = Some trace /\ next = trace) ->
  seq_step local global [] (local <| seq_trace := next |>) global [].
Proof.
  intros Hnb Hnil Htrace (pc & Hpc & Htable & Hnext).
  subst trace.
  eapply (SeqStep global local (Some (LDone next)) next None);
    [exact Hnb | exact Htrace |].
  simpl. split; first reflexivity. exists pc. rewrite Hpc. rewrite Htable.
  repeat split; reflexivity.
Qed.

Lemma writeSuccessSeqDoneTrap local global next (pc : bv 64) :
  local.(seq_nb_state) = false ->
  local.(seq_trace) = tnil ->
  trace_step local.(seq_trace) local.(seq_regs) (Some (LDone next)) next ->
  local.(seq_regs) !! local.(seq_pc_reg) = Some (RVal_Bits pc) ->
  global.(seq_instrs) !! pc = None ->
  seq_step local global [SInstrTrap pc]
    (local <| seq_nb_state := true |>) global [].
Proof.
  intros Hnb Hnil Htrace Hpc Hnone.
  eapply (SeqStep global local (Some (LDone next)) next
    (Some (SInstrTrap pc))); [exact Hnb | exact Htrace |].
  simpl. split; first reflexivity. exists pc. rewrite Hpc. rewrite Hnone.
  repeat split; reflexivity.
Qed.

Print Assumptions writeSuccessSeqSilent.
Print Assumptions writeSuccessSeqAssume.
Print Assumptions writeSuccessSeqAssertTrue.
Print Assumptions writeSuccessSeqAssumeReg.
Print Assumptions writeSuccessSeqReadReg.
Print Assumptions writeSuccessSeqWriteReg.
Print Assumptions writeSuccessSeqBranchAddress.
Print Assumptions writeSuccessSeqBranch.
Print Assumptions writeSuccessSeqReadMemBacked.
Print Assumptions writeSuccessSeqReadMemMmio.
Print Assumptions writeSuccessSeqWriteMemBacked.
Print Assumptions writeSuccessSeqWriteMemMmio.
Print Assumptions writeSuccessSeqDoneTabled.
Print Assumptions writeSuccessSeqDoneTrap.
