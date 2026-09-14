Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
Require Import isla.spec.
Definition physicalRegister64 (regs : reg_map) (register : sail_name) (value : bv 64) : Prop :=
  regs !! register = Some (RVal_Bits value).
Definition physicalMemoryBytes (sigma : seq_global_state) (address : Z) (bytes : list (bv 8)) : Prop :=
  read_mem_list (seq_mem sigma) address (N.of_nat (length bytes)) = Some bytes.
Definition physicalMemoryValue {n} (sigma : seq_global_state) (address : Z) (value : bv n) : Prop :=
  read_mem (seq_mem sigma) address (n / 8) = Some (bv_to_bvn value).
Definition physicalSavedRegisters (regs : reg_map) (saved : list (bv 64)) : Prop :=
  Forall2 (fun register value => physicalRegister64 regs register value)
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
     "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] saved.
Definition physicalCallerFrame (sigma : seq_global_state)
    (sp inputPointer inputSize allocatorPointer allocatorSize savedRa : bv 64)
    (padding : list (bv 8)) : Prop :=
  length padding = 6%nat /\
  physicalMemoryValue sigma (bv_unsigned sp) inputPointer /\
  physicalMemoryValue sigma (bv_unsigned sp + 8) inputSize /\
  physicalMemoryValue sigma (bv_unsigned sp + 16) allocatorPointer /\
  physicalMemoryValue sigma (bv_unsigned sp + 24) allocatorSize /\
  physicalMemoryBytes sigma (bv_unsigned sp + 882) padding /\
  physicalMemoryValue sigma (bv_unsigned sp + 888) savedRa.
Definition traceResidual (initial : spec) (prefix : list seq_label) (residual : spec) : Prop :=
  forall suffix, initial (prefix ++ suffix) <-> residual suffix.
Lemma trace_residual_empty initial : traceResidual initial [] initial.
Proof. intros suffix. reflexivity. Qed.
Lemma trace_residual_append initial prefix residual next final :
  traceResidual initial prefix residual -> traceResidual residual next final ->
  traceResidual initial (prefix ++ next) final.
Proof.
  intros Hprefix Hnext suffix. unfold traceResidual in *.
  rewrite <- app_assoc. rewrite Hprefix. apply Hnext.
Qed.
Lemma physical_saved_registers_length regs saved :
  physicalSavedRegisters regs saved -> length saved = 12%nat.
Proof. intros H. apply Forall2_length in H. simpl in H. symmetry. exact H. Qed.
Print Assumptions trace_residual_append.
Print Assumptions physical_saved_registers_length.
