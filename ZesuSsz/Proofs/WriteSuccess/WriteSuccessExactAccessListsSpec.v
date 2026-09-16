Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
From Coq Require Import Lists.List ZArith.ZArith.

Fixpoint writeSuccessExactStorageKeyEvents (sp : bv 64)
    (keys : list (list (bv 8))) (tail : spec) : spec :=
  match keys with
  | [] => tail
  | key :: keys => writeOutputEvents (sp + BV 64 1712)%bv (BV 64 32) key
      (writeSuccessExactStorageKeyEvents sp keys tail)
  end.

Definition writeSuccessExactAccessEntryEvents (sp : bv 64)
    (entry : writeSuccessAccessEntry) (tail : spec) : spec :=
  writeOutputEvents (sp + BV 64 1760)%bv (BV 64 20)
    (writeSuccessPrivateBytes
      (observationAccessAddress (writeSuccessAccessObservation entry)))
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (Z.of_nat (writeSuccessAccessEntryStorageCount entry))))
      (writeSuccessExactStorageKeyEvents sp
        (map writeSuccessPrivateBytes
          (observationStorageKeys (writeSuccessAccessObservation entry))) tail)).

Fixpoint writeSuccessExactAccessListsEvents (sp : bv 64)
    (entries : list writeSuccessAccessEntry) (tail : spec) : spec :=
  match entries with
  | [] => tail
  | entry :: entries => writeSuccessExactAccessEntryEvents sp entry
      (writeSuccessExactAccessListsEvents sp entries tail)
  end.

Lemma writeSuccessExactStorageKeyEvents_app sp left right tail :
  writeSuccessExactStorageKeyEvents sp (left ++ right) tail =
  writeSuccessExactStorageKeyEvents sp left
    (writeSuccessExactStorageKeyEvents sp right tail).
Proof. induction left; simpl; [reflexivity|rewrite IHleft; reflexivity]. Qed.

Lemma writeSuccessExactAccessListsEvents_app sp left right tail :
  writeSuccessExactAccessListsEvents sp (left ++ right) tail =
  writeSuccessExactAccessListsEvents sp left
    (writeSuccessExactAccessListsEvents sp right tail).
Proof. induction left; simpl; [reflexivity|rewrite IHleft; reflexivity]. Qed.

(** Every iteration retains the complete source array and all nested arrays.
    The processed list changes only the cursor and the trace continuation. *)
Definition writeSuccessExactAccessListsState `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (storedIndex x19 savedX22 x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessAccessListsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   writeSuccessAccessListsScratch sp base (length entries) storedIndex savedX22 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAccessListsEvents sp remaining tail) ∗
   ⌜entries = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗
   ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactAccessListsState) := I.

Print Assumptions writeSuccessExactStorageKeyEvents_app.
Print Assumptions writeSuccessExactAccessListsEvents_app.
