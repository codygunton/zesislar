Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.InstrPreAddress.
Require Import ZesuSsz.Automation.StackArrayLookup.
Require Import ZesuSsz.Automation.InteriorByteSlice.
Require Import ZesuSsz.Automation.RawWordArrayWitness.
Require Import ZesuSsz.Automation.Finish.
Require Import ZesuSsz.Automation.Legacy.Finish.
From Coq Require Import ZArith.ZArith NArith.NArith Lists.List.
From stdpp Require Import tactics bitvector.definitions.
Open Scope Z_scope.
Goal True.
Proof.
exact I.
Qed.
Lemma additional_literal_controls (input : Z) : True.
Proof.
ZesuSsz.Automation.StackArrayLookup.zesu_literal_Z constr:((2 + 3)%Z).
Fail ZesuSsz.Automation.StackArrayLookup.zesu_literal_Z constr:(input).
exact I.
Qed.
Lemma additional_raw_word_controls (word : bv 64) (narrow : bv 7) : True.
Proof.
ZesuSsz.Automation.RawWordArrayWitness.zesu_raw_array_check_word word.
Fail ZesuSsz.Automation.RawWordArrayWitness.zesu_raw_array_check_word narrow.
let bytes := ZesuSsz.Automation.RawWordArrayWitness.zesu_raw_array_word_bytes word in
 let expected := constr:(bv_to_little_endian 8 8 (bv_unsigned word)) in
 let Hbytes := fresh "Hbytes" in assert (Hbytes : bytes = expected) by reflexivity; clear Hbytes.
exact I.
Qed.
Lemma additional_legacy_constant : (BV 64 2 + BV 64 3)%bv = BV 64 5.
Proof.
ZesuSsz.Automation.Legacy.Finish.zesu_finish_constant.
Qed.
Lemma additional_legacy_symbolic (word : bv 64) : word = word.
Proof.
Fail ZesuSsz.Automation.Legacy.Finish.zesu_finish_constant.
reflexivity.
Qed.
#[local] Instance additional_instruction_switch : ZesuSsz.Automation.InstrPreAddress.ZesuStepInstrPreAddress := I.
Lemma additional_instruction_closed `{!islaG Sigma} `{!threadG} :
 FindInContext (FindInstrKind (1 + 1)%Z false) FICSyntactic.
Proof.
ZesuSsz.Automation.InstrPreAddress.zesu_reduce_instr_pre_address.
Qed.
Lemma additional_instruction_symbolic `{!islaG Sigma} `{!threadG} (address : Z) :
 FindInContext (FindInstrKind address false) FICSyntactic.
Proof.
Fail ZesuSsz.Automation.InstrPreAddress.zesu_reduce_instr_pre_address.
typeclasses eauto.
Qed.
Print Assumptions additional_literal_controls.
Print Assumptions additional_raw_word_controls.
Print Assumptions additional_legacy_constant.
Print Assumptions additional_legacy_symbolic.
Print Assumptions additional_instruction_closed.
Print Assumptions additional_instruction_symbolic.
Lemma additional_legacy_known_word `{!islaG Sigma} (root value : bv 64) :
 (bv_unsigned root + 8 < bv_modulus 64)%Z ->
 (bv_unsigned root + 8) ↦ₘ value -∗
 find_in_context (FindMemMapsTo (bv_unsigned (root + BV 64 8)%bv)) (fun _ => True%I).
Proof.
iIntros (Hrange) "Hword".
ZesuSsz.Automation.Legacy.Hooks.zesu_normalize_known_word_address.
iExists (MKMapsTo 64 value).
iFrame.
cbn [FindMemMapsTo mem_mapsto_kind_prop].
lazymatch goal with |- iris.proofmode.environments.envs_entails ?E _ => change (iris.proofmode.environments.envs_entails E (((bv_unsigned root + 8) ↦ₘ value) ∗ True)%I) end.
by iFrame.
Qed.
Lemma additional_legacy_symbolic_offset `{!islaG Sigma} (root offset value : bv 64) :
 (bv_unsigned (root + offset)%bv) ↦ₘ value -∗
 find_in_context (FindMemMapsTo (bv_unsigned (root + offset)%bv)) (fun _ => True%I).
Proof.
iIntros "Hword".
Fail ZesuSsz.Automation.Legacy.Hooks.zesu_normalize_known_word_address.
iExists (MKMapsTo 64 value).
lazymatch goal with |- iris.proofmode.environments.envs_entails ?E _ => change (iris.proofmode.environments.envs_entails E (((bv_unsigned (root + offset)%bv) ↦ₘ value) ∗ True)%I) end.
by iFrame.
Qed.
Lemma additional_stack_range :
 (bv_unsigned (BV 64 0) + 0 <= bv_unsigned (BV 64 0 + BV 64 8)%bv < bv_unsigned (BV 64 0) + 16)%Z \/ False.
Proof.
left; split; ZesuSsz.Automation.VmClosed.zesu_vm_closed_decide.
Qed.
Definition additional_folded_facts : Prop := (0 = 0)%Z /\ (0 = 0)%Z.
Lemma additional_stack_range_folded :
 (bv_unsigned (BV 64 0) + 0 <= bv_unsigned (BV 64 0 + BV 64 8)%bv < bv_unsigned (BV 64 0) + 16)%Z \/ False.
Proof.
assert (Hfolded : additional_folded_facts) by (split; reflexivity).
ZesuSsz.Automation.StackArrayLookup.zesu_stack_array_range.
Qed.
Print Assumptions additional_legacy_known_word.
Print Assumptions additional_legacy_symbolic_offset.
Print Assumptions additional_stack_range_folded.
Print Assumptions ZesuSsz.Automation.InteriorByteSlice.zesu_byte_array_lend_slice.
