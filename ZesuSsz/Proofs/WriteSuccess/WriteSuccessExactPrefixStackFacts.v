Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeContract WriteSuccessRepresentation.
Lemma exact_frame_unsigned (sp : bv 64)
    (Hlower : mapRamBase defaultMap + 0x880 <= bv_unsigned sp) :
  bv_unsigned (sp - BV 64 2000)%bv = (bv_unsigned sp - 2000)%Z.
Proof. cbv [mapRamBase defaultMap] in Hlower. bv_solve. Qed.
Print Assumptions exact_frame_unsigned.

Lemma exact_prefix_stack_facts {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  bv_unsigned (writeSuccessEntrySp witness) =
    (bv_unsigned (writeSuccessFrameSp witness) + 2000)%Z /\
  bv_unsigned (writeSuccessFrameSp witness) `mod` 16 = 0 /\
  bv_unsigned (writeSuccessFrameSp witness) + 1896 < machineRamEnd defaultMap.
Proof.
  have Hlower : mapRamBase defaultMap + 0x880 <= bv_unsigned (writeSuccessEntrySp witness).
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have Halign : bv_unsigned (writeSuccessEntrySp witness) `mod` 16 = 0.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have Hupper : bv_unsigned (writeSuccessEntrySp witness) + 0x7d0 < machineRamEnd defaultMap.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have Hframe := exact_frame_unsigned (writeSuccessEntrySp witness) Hlower.
  fold (writeSuccessFrameSp witness) in Hframe.
  split; [lia |]. split.
  - rewrite Hframe Zminus_mod Halign. reflexivity.
  - rewrite Hframe. lia.
Qed.
Print Assumptions exact_prefix_stack_facts.

(* The registration the finisher's C6 step looks for. Stated once here,
   beside the lemma it wraps: every segment that carries the witness's
   well-formedness gets the frame pointer's alignment, its offset from the
   entry pointer and its upper bound, and no segment spends a line on
   them. *)
Global Instance zesu_derived_prefix_stack_facts {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  ZesuDerivedFacts (writeSuccessWitnessWellFormed args witness)
    (bv_unsigned (writeSuccessEntrySp witness) =
       (bv_unsigned (writeSuccessFrameSp witness) + 2000)%Z /\
     bv_unsigned (writeSuccessFrameSp witness) `mod` 16 = 0 /\
     bv_unsigned (writeSuccessFrameSp witness) + 1896 <
       machineRamEnd defaultMap) :=
  exact_prefix_stack_facts args witness.
