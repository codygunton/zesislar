From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.

(** An Islaris implementation can map each relational entry and exit to owned resources. *)
Record IslarisContractResources `{!islaG Sigma} `{!threadG}
    (Args Outcome : Type) : Type := {
  islarisCode : iProp Sigma;
  islarisEntry : Args -> iProp Sigma;
  islarisExit : Args -> Outcome -> iProp Sigma
}.

Definition IslarisContractSpec `{!Arch} `{!islaG Sigma} `{!threadG}
    {Args Outcome : Type} (entryPc exitPc : Z)
    (allows : Args -> Outcome -> Prop)
  (resources : IslarisContractResources Args Outcome) : iProp Sigma :=
  (islarisCode Args Outcome resources -∗
    ∀ args : Args,
      instr_body entryPc (
        islarisEntry Args Outcome resources args ∗
        instr_pre exitPc (
          ∃ outcome : Outcome,
            ⌜allows args outcome⌝ ∗
            islarisExit Args Outcome resources args outcome)))%I.

(** A contract model fixes its outcome relation and every owned resource. *)
Record IslarisContractModel (Args Outcome : Type) : Type := {
  islarisContractAllows : Args -> Outcome -> Prop;
  islarisContractStep : Z -> Z -> Prop;
  islarisContractResources : forall (Sigma : gFunctors)
    (HG : islaG Sigma) (HT : threadG),
    @IslarisContractResources Sigma HG HT Args Outcome
}.

Definition IslarisContractCorrect {Args Outcome : Type}
    (entryPc exitPc : Z) (model : IslarisContractModel Args Outcome) : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ @IslarisContractSpec riscv64_arch Sigma HG HT Args Outcome
      entryPc exitPc (islarisContractAllows Args Outcome model)
      (islarisContractResources Args Outcome model Sigma HG HT).
