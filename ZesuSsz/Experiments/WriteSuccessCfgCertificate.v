From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.Machine.

Import ListNotations.

(** A path in the generated writeSuccess CFG.  The path contains block entry
    PCs, while [Forall] excludes its terminal exit PC. *)
Definition writeSuccessCfgPath
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (path : list Z) : Prop :=
  hd_error path = Some entryPc /\
  InstructionPathFollows nextPc path /\
  Forall region (removelast path).

(** A maximal path has no outgoing edge after its final PC.  This condition
    makes the universal claim stronger than a single selected execution. *)
Definition writeSuccessCfgMaximal
    (nextPc : Z -> Z -> Prop) (exitPc : Z -> Prop)
    (path : list Z) : Prop :=
  exists pc, last path 0%Z = pc /\
    (exitPc pc \/ forall next, ~ nextPc pc next).

(** This record separates the finite witness consumed by the existing bridge
    from the universal bounded-path obligation.  A cyclic CFG must supply a
    ranking or explicit loop budgets to prove [writeSuccessCfgAllPaths]. *)
Record WriteSuccessCfgCertificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Prop := {
  writeSuccessCfgWitness :
    InstructionPathCertificate nextPc region exitPc entryPc bound;
  writeSuccessCfgAllPaths :
    forall path,
      writeSuccessCfgPath nextPc region exitPc entryPc path ->
      writeSuccessCfgMaximal nextPc exitPc path ->
      exists pc, last path 0%Z = pc /\ exitPc pc /\
        length path <= S bound
}.

Lemma writeSuccessCfgCertificateBridge
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) :
  WriteSuccessCfgCertificate nextPc region exitPc entryPc bound ->
  correctness ->
  NativeContractAssumption correctness nextPc region exitPc entryPc bound.
Proof.
  intros certificate Hcorrect.
  apply nativeContractBridge; [exact Hcorrect |].
  exact (writeSuccessCfgWitness nextPc region exitPc entryPc bound certificate).
Qed.
