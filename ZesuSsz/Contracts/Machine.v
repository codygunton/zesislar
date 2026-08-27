From Coq Require Import Lists.List ZArith.ZArith.

Import ListNotations.

(** A machine contract describes one binary region without selecting a proof method. *)
Record RelationalMachineContract
    (State Args Outcome : Type) : Type := {
  contractAllows : Args -> Outcome -> Prop;
  contractEntry : Args -> State -> Prop;
  contractExit : Args -> Outcome -> State -> State -> Prop;
  contractStepBound : Args -> nat
}.

Inductive ConfinedTrace {State : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z)
    (region : Z -> Prop) : nat -> nat -> State -> State -> Prop :=
| ConfinedTraceRefl fromStep state :
    ConfinedTrace step pc region fromStep 0 state state
| ConfinedTraceStep fromStep count address before middle after :
    pc before = Some address ->
    region address ->
    step fromStep before middle ->
    ConfinedTrace step pc region (S fromStep) count middle after ->
    ConfinedTrace step pc region fromStep (S count) before after.

Definition ContractImplements {State Args Outcome : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z)
    (region exitPc : Z -> Prop)
    (contract : RelationalMachineContract State Args Outcome) : Prop :=
  forall args (fromStep : nat) before,
    contractEntry State Args Outcome contract args before ->
    exists (count : nat) after outcome,
      0 < count /\
      count <= contractStepBound State Args Outcome contract args /\
      ConfinedTrace step pc region fromStep count before after /\
      (exists address, pc after = Some address /\ exitPc address) /\
      contractAllows State Args Outcome contract args outcome /\
      contractExit State Args Outcome contract args outcome before after.

Definition PcInRanges (ranges : list (Z * Z)) (pc : Z) : Prop :=
  exists lower upper, In (lower, upper) ranges /\ (lower <= pc < upper)%Z.

Definition PcInList (pcs : list Z) (pc : Z) : Prop := In pc pcs.

Inductive InstructionPathFollows (nextPc : Z -> Z -> Prop) :
    list Z -> Prop :=
| InstructionPathOne pc : InstructionPathFollows nextPc [pc]
| InstructionPathNext fromPc toPc rest :
    nextPc fromPc toPc ->
    InstructionPathFollows nextPc (toPc :: rest) ->
    InstructionPathFollows nextPc (fromPc :: toPc :: rest).

Definition StraightLineInstructionStep (fromPc toPc : Z) : Prop :=
  (toPc = fromPc + 4)%Z.

(** A finite path certifies the instruction bound separately from the
    Islaris resource proof. The path contains its terminal PC. *)
Definition InstructionPathCertificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Prop :=
  exists instructionPath : list Z,
    hd_error instructionPath = Some entryPc /\
    InstructionPathFollows nextPc instructionPath /\
    Forall region (removelast instructionPath) /\
    (exists pc, last instructionPath entryPc = pc /\ exitPc pc) /\
    length instructionPath = S bound /\
    0 < bound.

(** The bridge keeps state correctness and termination as separate proofs. *)
Record NativeContractAssumption
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Prop := {
  nativeStateCorrect : correctness;
  nativeTermination :
    InstructionPathCertificate nextPc region exitPc entryPc bound
}.

Lemma nativeContractBridge
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) :
  correctness ->
  InstructionPathCertificate nextPc region exitPc entryPc bound ->
  NativeContractAssumption correctness nextPc region exitPc entryPc bound.
Proof. constructor; assumption. Qed.
