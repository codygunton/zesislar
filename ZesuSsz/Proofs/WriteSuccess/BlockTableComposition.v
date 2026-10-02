Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BlockTable.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e28.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e38.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e48.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e58.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e68.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_14e78.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_1572c.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15118.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15154.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_153a8.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_153b4.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15558.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15614.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_1565c.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e28.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e38.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e48.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e58.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e68.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e78.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_14e88.
Require Import ZesuSsz.Generated.WriteSuccess.States.HeaderSuccessor_14e88.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteOutputContract.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15118.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15154.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_153a8.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_153b4.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15558.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15614.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_1565c.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_1572c.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_1573c.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15118_1511c.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15118_1513c.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15154_1515c.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15154_15194.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_153a8_15228.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_153a8_153b4.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_153b4_151d4.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15558_153d4.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15558_15564.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15614_15590.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15614_15620.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_1565c_14f00.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ZesuSsz.Generated.WriteSuccess.BlockTable.

Section table.
Context `{!islaG Sigma} `{!threadG}.
Context (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma).
Context (root oldData oldSize : bv 64).
Context (b15118_tag : bv 64) (b15118_P : iProp Sigma) (b15118_sp : bv 64).
Context (b15154_sp : bv 64) (b15154_tag : bv 64) (b15154_old_data : bv 64) (b15154_P : iProp Sigma).
Context (b153a8_pointer : bv 64) (b153a8_count : bv 64) (b153a8_P : iProp Sigma) (b153a8_sp : bv 64).
Context (b153b4_sp : bv 64) (b153b4_index : bv 64) (b153b4_old11 : bv 64) (b153b4_P : iProp Sigma).
Context (b15558_pointer : bv 64) (b15558_count : bv 64) (b15558_value22 : bv 64) (b15558_P : iProp Sigma) (b15558_sp : bv 64).
Context (b15614_pointer : bv 64) (b15614_count : bv 64) (b15614_P : iProp Sigma) (b15614_sp : bv 64).
Context (b1565c_sp : bv 64) (b1565c_index : bv 64) (b1565c_total : bv 64) (b1565c_P : iProp Sigma).

Local Notation tableEntries := (writeSuccessBlockTable sp bytes tail P root oldData oldSize b15118_tag b15118_P b15118_sp b15154_sp b15154_tag b15154_old_data b15154_P b153a8_pointer b153a8_count b153a8_P b153a8_sp b153b4_sp b153b4_index b153b4_old11 b153b4_P b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp b15614_pointer b15614_count b15614_P b15614_sp b1565c_sp b1565c_index b1565c_total b1565c_P).

(* Composition treats each boundary predicate as an opaque interface. *)
Local Opaque HeaderSuccessor_14e88 State_14e28 State_14e38 State_14e48 State_14e58 State_14e68 State_14e78 State_14e88 State_15118 State_15154 State_153a8 State_153b4 State_15558 State_15614 State_1565c State_1572c State_1573c Successor_15118_1511c Successor_15118_1513c Successor_15154_1515c Successor_15154_15194 Successor_153a8_15228 Successor_153a8_153b4 Successor_153b4_151d4 Successor_15558_153d4 Successor_15558_15564 Successor_15614_15590 Successor_15614_15620 Successor_1565c_14f00.

Local Lemma table_entry_14e28 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e38
    (State_14e38 sp bytes tail P) -∗
  instr_body 0x14e28
    (State_14e28 sp bytes tail P).
Proof. exact (block_14e28 sp bytes tail P). Qed.
Local Lemma table_entry_14e38 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e48
    (State_14e48 sp bytes tail P) -∗
  instr_body 0x14e38
    (State_14e38 sp bytes tail P).
Proof. exact (block_14e38 sp bytes tail P). Qed.
Local Lemma table_entry_14e48 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e58
    (State_14e58 sp bytes tail P) -∗
  instr_body 0x14e48
    (State_14e48 sp bytes tail P).
Proof. exact (block_14e48 sp bytes tail P). Qed.
Local Lemma table_entry_14e58 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e68
    (State_14e68 sp bytes tail P) -∗
  instr_body 0x14e58
    (State_14e58 sp bytes tail P).
Proof. exact (block_14e58 sp bytes tail P). Qed.
Local Lemma table_entry_14e68 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e78
    (State_14e78 sp bytes tail P) -∗
  instr_body 0x14e68
    (State_14e68 sp bytes tail P).
Proof. exact (block_14e68 sp bytes tail P). Qed.
Local Lemma table_entry_14e78 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e88
    (HeaderSuccessor_14e88 sp bytes tail P) -∗
  instr_body 0x14e78
    (State_14e78 sp bytes tail P).
Proof. exact (block_14e78 sp bytes tail P). Qed.
Local Lemma table_entry_1572c :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_pre 0x1573c
    (State_1573c P sp root oldData oldSize tail) -∗
  instr_body 0x1572c
    (State_1572c P sp root oldData oldSize tail).
Proof. exact (block_1572c P sp root oldData oldSize tail). Qed.
Local Lemma table_entry_15118 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x1513c
    (Successor_15118_1513c b15118_tag b15118_P b15118_sp) -∗
  instr_pre 0x1511c
    (Successor_15118_1511c b15118_tag b15118_P b15118_sp) -∗
  instr_body 0x15118
    (State_15118 b15118_tag b15118_P b15118_sp).
Proof. exact (block_15118 b15118_tag b15118_P b15118_sp). Qed.
Local Lemma table_entry_15154 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x15194
    (Successor_15154_15194 b15154_sp b15154_tag b15154_old_data b15154_P) -∗
  instr_pre 0x1515c
    (Successor_15154_1515c b15154_sp b15154_tag b15154_old_data b15154_P) -∗
  instr_body 0x15154
    (State_15154 b15154_sp b15154_tag b15154_old_data b15154_P).
Proof. exact (block_15154 b15154_sp b15154_tag b15154_old_data b15154_P). Qed.
Local Lemma table_entry_153a8 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x15228
    (Successor_153a8_15228 b153a8_pointer b153a8_count b153a8_P b153a8_sp) -∗
  instr_pre 0x153b4
    (Successor_153a8_153b4 b153a8_pointer b153a8_count b153a8_P b153a8_sp) -∗
  instr_body 0x153a8
    (State_153a8 b153a8_pointer b153a8_count b153a8_P b153a8_sp).
Proof. exact (block_153a8 b153a8_pointer b153a8_count b153a8_P b153a8_sp). Qed.
Local Lemma table_entry_153b4 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x151d4
    (Successor_153b4_151d4 b153b4_sp b153b4_index b153b4_old11 b153b4_P) -∗
  instr_body 0x153b4
    (State_153b4 b153b4_sp b153b4_index b153b4_old11 b153b4_P).
Proof. exact (block_153b4 b153b4_sp b153b4_index b153b4_old11 b153b4_P). Qed.
Local Lemma table_entry_15558 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x153d4
    (Successor_15558_153d4 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp) -∗
  instr_pre 0x15564
    (Successor_15558_15564 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp) -∗
  instr_body 0x15558
    (State_15558 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp).
Proof. exact (block_15558 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp). Qed.
Local Lemma table_entry_15614 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x15590
    (Successor_15614_15590 b15614_pointer b15614_count b15614_P b15614_sp) -∗
  instr_pre 0x15620
    (Successor_15614_15620 b15614_pointer b15614_count b15614_P b15614_sp) -∗
  instr_body 0x15614
    (State_15614 b15614_pointer b15614_count b15614_P b15614_sp).
Proof. exact (block_15614 b15614_pointer b15614_count b15614_P b15614_sp). Qed.
Local Lemma table_entry_1565c :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x14f00
    (Successor_1565c_14f00 b1565c_sp b1565c_index b1565c_total b1565c_P) -∗
  instr_body 0x1565c
    (State_1565c b1565c_sp b1565c_index b1565c_total b1565c_P).
Proof. exact (block_1565c b1565c_sp b1565c_index b1565c_total b1565c_P). Qed.
Lemma write_success_block_table_cases :
  instr_lookup_resources Index.lookup -∗ Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x14e88 (HeaderSuccessor_14e88 sp bytes tail P) -∗
  □ instr_pre 0x1573c (State_1573c P sp root oldData oldSize tail) -∗
  □ instr_pre 0x1513c (Successor_15118_1513c b15118_tag b15118_P b15118_sp) -∗
  □ instr_pre 0x1511c (Successor_15118_1511c b15118_tag b15118_P b15118_sp) -∗
  □ instr_pre 0x15194 (Successor_15154_15194 b15154_sp b15154_tag b15154_old_data b15154_P) -∗
  □ instr_pre 0x1515c (Successor_15154_1515c b15154_sp b15154_tag b15154_old_data b15154_P) -∗
  □ instr_pre 0x15228 (Successor_153a8_15228 b153a8_pointer b153a8_count b153a8_P b153a8_sp) -∗
  □ instr_pre 0x153b4 (Successor_153a8_153b4 b153a8_pointer b153a8_count b153a8_P b153a8_sp) -∗
  □ instr_pre 0x151d4 (Successor_153b4_151d4 b153b4_sp b153b4_index b153b4_old11 b153b4_P) -∗
  □ instr_pre 0x153d4 (Successor_15558_153d4 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp) -∗
  □ instr_pre 0x15564 (Successor_15558_15564 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp) -∗
  □ instr_pre 0x15590 (Successor_15614_15590 b15614_pointer b15614_count b15614_P b15614_sp) -∗
  □ instr_pre 0x15620 (Successor_15614_15620 b15614_pointer b15614_count b15614_P b15614_sp) -∗
  □ instr_pre 0x14f00 (Successor_1565c_14f00 b1565c_sp b1565c_index b1565c_total b1565c_P) -∗
  block_table_pre tableEntries -∗
  ∀ address state, ⌜(address, state) ∈ tableEntries⌝ -∗
    instr_body address state.
Proof.
  iIntros "#Hcode #Hspec #Houtput #Hgenericoutput #Hedge0 #Hedge1 #Hedge2 #Hedge3 #Hedge4 #Hedge5 #Hedge6 #Hedge7 #Hedge8 #Hedge9 #Hedge10 #Hedge11 #Hedge12 #Hedge13 #Htable".
  iEval (rewrite /block_table_pre /tableEntries /=) in "Htable".
  iDestruct "Htable" as
    "(#H14e28 & #H14e38 & #H14e48 & #H14e58 & #H14e68 & #H14e78 & #H1572c & #H15118 & #H15154 & #H153a8 & #H153b4 & #H15558 & #H15614 & #H1565c & _)".
  iApply block_table_cases_from_bodies.
  rewrite /tableEntries !big_sepL_cons big_sepL_nil.
  iSplitL; first (iApply (table_entry_14e28 with "Hcode Hspec Houtput H14e38")).
  iSplitL; first (iApply (table_entry_14e38 with "Hcode Hspec Houtput H14e48")).
  iSplitL; first (iApply (table_entry_14e48 with "Hcode Hspec Houtput H14e58")).
  iSplitL; first (iApply (table_entry_14e58 with "Hcode Hspec Houtput H14e68")).
  iSplitL; first (iApply (table_entry_14e68 with "Hcode Hspec Houtput H14e78")).
  iSplitL; first (iApply (table_entry_14e78 with "Hcode Hspec Houtput Hedge0")).
  iSplitL; first (iApply (table_entry_1572c with "Hcode Hspec Hgenericoutput Hedge1")).
  iSplitL; first (iApply (table_entry_15118 with "Hcode Hspec Hedge2 Hedge3")).
  iSplitL; first (iApply (table_entry_15154 with "Hcode Hspec Hedge4 Hedge5")).
  iSplitL; first (iApply (table_entry_153a8 with "Hcode Hspec Hedge6 Hedge7")).
  iSplitL; first (iApply (table_entry_153b4 with "Hcode Hspec Hedge8")).
  iSplitL; first (iApply (table_entry_15558 with "Hcode Hspec Hedge9 Hedge10")).
  iSplitL; first (iApply (table_entry_15614 with "Hcode Hspec Hedge11 Hedge12")).
  iSplitL; first (iApply (table_entry_1565c with "Hcode Hspec Hedge13")).
  done.
Qed.
End table.

Print Assumptions write_success_block_table_cases.
