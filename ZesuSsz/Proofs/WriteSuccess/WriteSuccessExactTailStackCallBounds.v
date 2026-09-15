Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessExactPrefixStackFacts.
Open Scope Z_scope.
Lemma exact_tail_stack_call_bounds {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  mapRamBase defaultMap <= bv_unsigned (writeSuccessFrameSp witness) - 80 /\
  bv_unsigned (writeSuccessFrameSp witness) < machineRamEnd defaultMap.
Proof.
  have Hlower : mapRamBase defaultMap + 0x880 <= bv_unsigned (writeSuccessEntrySp witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  split; lia.
Qed.
Print Assumptions exact_tail_stack_call_bounds.
