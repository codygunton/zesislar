From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Import ListNotations.

Definition zesu_ram_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x20000000)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x20000000)));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 0x1000)));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 0x100)));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 0x2000000)));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 0xc0000)));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x40001000)));
  (KindReg "cur_privilege", ExactShape (RVal_Enum "Machine"));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0x8000000000001100))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].
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

Ltac solve_instruction_path solve_edge :=
  lazymatch goal with
  | |- InstructionPathFollows _ (_ :: _ :: _) =>
      apply InstructionPathNext;
      [ solve [solve_edge] | solve_instruction_path solve_edge ]
  | |- InstructionPathFollows _ [_] => constructor
  end.

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
    (exists pc, List.last instructionPath entryPc = pc /\ exitPc pc) /\
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
