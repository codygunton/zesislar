Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Require Export ZesuSsz.Proofs.ReadInput.Resources.

#[local] Hint Rewrite read_input_buffer_pointer_eq : isla_coq_rewrite.

Theorem read_input_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x10140 0x14ccc
    readInputAllows read_input_resources.
Proof.
  rewrite /IslarisContractSpec /read_input_resources /=.
  iStartProof.
  iIntros "(Hi1&Hi2&Hi3&Hi4&Hi5&Hi6&Hi7&Hi8)" (args).
  repeat lazymatch goal with
  | |- _ ⊢ WPasm tnil => fail 1
  | _ => zesu_liAStep
  end.
  liShow.
  iExists (Build_ReadInputOutcome (mapInputBufferAddress defaultMap), tt)ₗ.
  red_li_prod. iSplit; first done.
  iExists bufferSlot, sizeSlot, sizeWord, savedWord.
  unshelve (repeat zesu_liAStep; liShow).
  Unshelve. all: prepare_sidecond.
  all: try (apply Z.le_ge;
    change ((mapRamBase defaultMap) <= bv_unsigned sizeSlot)%Z;
    clear -H0 H1 H3 H9; lia).
  all: zesu_finish.
Qed.

