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

Require Import ZesuSsz.Generated.WriteSuccess.States.State_150fc.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_150fc_15108.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntContract.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_150fc.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15148.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_15148_15154.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15148.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_151c4.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_151c4_151d0.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_151c4.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedEntry_151d4.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_151d4_153c0.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_151d4_151dc.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_151d4.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_1521c.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_1521c_153b4.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_1521c_15228.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_1521c.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_153c0.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_153c0_153d0.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_153c0.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15574.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_15574_15584.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15574.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15620.
Require Import ZesuSsz.Generated.WriteSuccess.States.CapturedSuccessor_15620_1562c.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15620.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15750.
Require Import ZesuSsz.Generated.WriteSuccess.States.Successor_15750_15754.
Require Import ZesuSsz.Generated.WriteSuccess.Blocks.Block_15750.

Section table.
Context `{!islaG Sigma} `{!threadG}.
Context (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma).
Context (oldra old5 oldData oldSize : bv 64).
Context (b15118_tag : bv 64) (b15118_P : iProp Sigma) (b15118_sp : bv 64).
Context (b15154_sp : bv 64) (b15154_tag : bv 64) (b15154_old_data : bv 64) (b15154_P : iProp Sigma).
Context (b153a8_pointer : bv 64) (b153a8_count : bv 64) (b153a8_P : iProp Sigma) (b153a8_sp : bv 64).
Context (b153b4_sp : bv 64) (b153b4_index : bv 64) (b153b4_old11 : bv 64) (b153b4_P : iProp Sigma).
Context (b15558_pointer : bv 64) (b15558_count : bv 64) (b15558_value22 : bv 64) (b15558_P : iProp Sigma) (b15558_sp : bv 64).
Context (b15614_pointer : bv 64) (b15614_count : bv 64) (b15614_P : iProp Sigma) (b15614_sp : bv 64).
Context (b1565c_sp : bv 64) (b1565c_index : bv 64) (b1565c_total : bv 64) (b1565c_P : iProp Sigma).

Context (b150fc_sp : bv 64) (b150fc_value : bv 64) (b150fc_oldra : bv 64) (b150fc_old5 : bv 64) (b150fc_old11 : bv 64) (b150fc_tail : spec) (b150fc_P : iProp Sigma).
Context (b15148_sp : bv 64) (b15148_value : bv 64) (b15148_oldra : bv 64) (b15148_old5 : bv 64) (b15148_old11 : bv 64) (b15148_tail : spec) (b15148_P : iProp Sigma).
Context (b151c4_sp : bv 64) (b151c4_value : bv 64) (b151c4_oldra : bv 64) (b151c4_old5 : bv 64) (b151c4_old11 : bv 64) (b151c4_tail : spec) (b151c4_P : iProp Sigma).
Context (b151d4_sp : bv 64) (b151d4_index : bv 64) (b151d4_old11 : bv 64) (b151d4_P : iProp Sigma).
Context (b1521c_sp : bv 64) (b1521c_data : bv 64) (b1521c_bytes : list (bv 8)) (b1521c_P : iProp Sigma).
Context (b153c0_sp : bv 64) (b153c0_savedX22 : bv 64) (b153c0_old22 : bv 64) (b153c0_old_ra : bv 64) (b153c0_old5 : bv 64) (b153c0_old_data : bv 64) (b153c0_old_size : bv 64) (b153c0_tail : spec) (b153c0_P : iProp Sigma).
Context (b15574_sp : bv 64) (b15574_count : bv 64) (b15574_oldra : bv 64) (b15574_old5 : bv 64) (b15574_old11 : bv 64) (b15574_tail : spec) (b15574_P : iProp Sigma).
Context (b15620_sp : bv 64) (b15620_value : bv 64) (b15620_oldra : bv 64) (b15620_old5 : bv 64) (b15620_old11 : bv 64) (b15620_tail : spec) (b15620_P : iProp Sigma).
Context (b15750_value : bv 64) (b15750_Q : iProp Sigma) (b15750_Hvalue : b15750_value ≠ 0%bv) (b15750_sp : bv 64).

Local Notation tableEntries := (writeSuccessBlockTable sp bytes tail P oldra old5 oldData oldSize b15118_tag b15118_P b15118_sp b15154_sp b15154_tag b15154_old_data b15154_P b153a8_pointer b153a8_count b153a8_P b153a8_sp b153b4_sp b153b4_index b153b4_old11 b153b4_P b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp b15614_pointer b15614_count b15614_P b15614_sp b1565c_sp b1565c_index b1565c_total b1565c_P b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P b151d4_sp b151d4_index b151d4_old11 b151d4_P b1521c_sp b1521c_data b1521c_bytes b1521c_P b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P b15750_value b15750_Q b15750_Hvalue b15750_sp).

(* Composition treats each boundary predicate as an opaque interface. *)
Local Opaque HeaderSuccessor_14e88 State_14e28 State_14e38 State_14e48 State_14e58 State_14e68 State_14e78 State_14e88 State_15118 State_15154 State_153a8 State_153b4 State_15558 State_15614 State_1565c State_1572c State_1573c Successor_15118_1511c Successor_15118_1513c Successor_15154_1515c Successor_15154_15194 Successor_153a8_15228 Successor_153a8_153b4 Successor_153b4_151d4 Successor_15558_153d4 Successor_15558_15564 Successor_15614_15590 Successor_15614_15620 Successor_1565c_14f00.

Local Opaque CapturedSuccessor_150fc_15108 State_150fc CapturedSuccessor_15148_15154 State_15148 CapturedSuccessor_151c4_151d0 State_151c4 CapturedSuccessor_151d4_153c0 CapturedSuccessor_151d4_151dc CapturedEntry_151d4 CapturedSuccessor_1521c_153b4 CapturedSuccessor_1521c_15228 State_1521c CapturedSuccessor_153c0_153d0 State_153c0 CapturedSuccessor_15574_15584 State_15574 CapturedSuccessor_15620_1562c State_15620 Successor_15750_15754 State_15750.

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
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x1573c
    (State_1573c sp oldra old5 oldData oldSize bytes tail P) -∗
  instr_body 0x1572c
    (State_1572c sp oldra old5 oldData oldSize bytes tail P).
Proof. exact (block_1572c sp oldra old5 oldData oldSize bytes tail P). Qed.
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
Local Lemma table_entry_150fc :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x15108
    (CapturedSuccessor_150fc_15108 b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P) -∗
  instr_body 0x150fc
    (State_150fc b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P).
Proof. exact (block_150fc b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P). Qed.

Local Lemma table_entry_15148 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x15154
    (CapturedSuccessor_15148_15154 b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P) -∗
  instr_body 0x15148
    (State_15148 b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P).
Proof. exact (block_15148 b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P). Qed.

Local Lemma table_entry_151c4 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x151d0
    (CapturedSuccessor_151c4_151d0 b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P) -∗
  instr_body 0x151c4
    (State_151c4 b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P).
Proof. exact (block_151c4 b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P). Qed.

Local Lemma table_entry_151d4 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x153c0
    (CapturedSuccessor_151d4_153c0 b151d4_sp b151d4_index b151d4_old11 b151d4_P) -∗
  instr_pre 0x151dc
    (CapturedSuccessor_151d4_151dc b151d4_sp b151d4_index b151d4_old11 b151d4_P) -∗
  instr_body 0x151d4
    (CapturedEntry_151d4 b151d4_sp b151d4_index b151d4_old11 b151d4_P).
Proof. exact (block_151d4 b151d4_sp b151d4_index b151d4_old11 b151d4_P). Qed.

Local Lemma table_entry_1521c :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x153b4
    (CapturedSuccessor_1521c_153b4 b1521c_sp b1521c_data b1521c_bytes b1521c_P) -∗
  instr_pre 0x15228
    (CapturedSuccessor_1521c_15228 b1521c_sp b1521c_data b1521c_bytes b1521c_P) -∗
  instr_body 0x1521c
    (State_1521c b1521c_sp b1521c_data b1521c_bytes b1521c_P).
Proof. exact (block_1521c b1521c_sp b1521c_data b1521c_bytes b1521c_P). Qed.

Local Lemma table_entry_153c0 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x153d0
    (CapturedSuccessor_153c0_153d0 b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P) -∗
  instr_body 0x153c0
    (State_153c0 b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P).
Proof. exact (block_153c0 b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P). Qed.

Local Lemma table_entry_15574 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x15584
    (CapturedSuccessor_15574_15584 b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P) -∗
  instr_body 0x15574
    (State_15574 b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P).
Proof. exact (block_15574 b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P). Qed.

Local Lemma table_entry_15620 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntContract -∗
  instr_pre 0x1562c
    (CapturedSuccessor_15620_1562c b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P) -∗
  instr_body 0x15620
    (State_15620 b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P).
Proof. exact (block_15620 b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P). Qed.

Local Lemma table_entry_15750 :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x158e0
    (False) -∗
  instr_pre 0x15754
    (Successor_15750_15754 b15750_value b15750_Q b15750_Hvalue b15750_sp) -∗
  instr_body 0x15750
    (State_15750 b15750_value b15750_Q b15750_Hvalue b15750_sp).
Proof. exact (block_15750 b15750_value b15750_Q b15750_Hvalue b15750_sp). Qed.

Lemma write_success_block_table_cases :
  instr_lookup_resources Index.lookup -∗ Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  □ instr_pre 0x14e88 (HeaderSuccessor_14e88 sp bytes tail P) -∗
  □ instr_pre 0x1573c (State_1573c sp oldra old5 oldData oldSize bytes tail P) -∗
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
  □ instr_pre 0x15d10 encoderIntContract -∗
  □ instr_pre 0x15108
    (CapturedSuccessor_150fc_15108 b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P) -∗
  □ instr_pre 0x15154
    (CapturedSuccessor_15148_15154 b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P) -∗
  □ instr_pre 0x151d0
    (CapturedSuccessor_151c4_151d0 b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P) -∗
  □ instr_pre 0x153c0
    (CapturedSuccessor_151d4_153c0 b151d4_sp b151d4_index b151d4_old11 b151d4_P) -∗
  □ instr_pre 0x151dc
    (CapturedSuccessor_151d4_151dc b151d4_sp b151d4_index b151d4_old11 b151d4_P) -∗
  □ instr_pre 0x153b4
    (CapturedSuccessor_1521c_153b4 b1521c_sp b1521c_data b1521c_bytes b1521c_P) -∗
  □ instr_pre 0x15228
    (CapturedSuccessor_1521c_15228 b1521c_sp b1521c_data b1521c_bytes b1521c_P) -∗
  □ instr_pre 0x153d0
    (CapturedSuccessor_153c0_153d0 b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P) -∗
  □ instr_pre 0x15584
    (CapturedSuccessor_15574_15584 b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P) -∗
  □ instr_pre 0x1562c
    (CapturedSuccessor_15620_1562c b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P) -∗
  □ instr_pre 0x158e0
    (False) -∗
  □ instr_pre 0x15754
    (Successor_15750_15754 b15750_value b15750_Q b15750_Hvalue b15750_sp) -∗
  block_table_pre tableEntries -∗
  ∀ address state, ⌜(address, state) ∈ tableEntries⌝ -∗
    instr_body address state.
Proof.
  iIntros "#Hcode #Hspec #Houtput #Hedge0 #Hedge1 #Hedge2 #Hedge3 #Hedge4 #Hedge5 #Hedge6 #Hedge7 #Hedge8 #Hedge9 #Hedge10 #Hedge11 #Hedge12 #Hedge13 #Hint #Hedge14 #Hedge15 #Hedge16 #Hedge17 #Hedge18 #Hedge19 #Hedge20 #Hedge21 #Hedge22 #Hedge23 #Hedge24 #Hedge25 #Htable".
  iEval (rewrite /block_table_pre /tableEntries /=) in "Htable".
  iDestruct "Htable" as
    "(#H14e28 & #H14e38 & #H14e48 & #H14e58 & #H14e68 & #H14e78 & #H1572c & #H15118 & #H15154 & #H153a8 & #H153b4 & #H15558 & #H15614 & #H1565c & #H150fc & #H15148 & #H151c4 & #H151d4 & #H1521c & #H153c0 & #H15574 & #H15620 & #H15750 & _)".
  iApply block_table_cases_from_bodies.
  rewrite /tableEntries !big_sepL_cons big_sepL_nil.
  iSplitL; first (iApply (table_entry_14e28 with "Hcode Hspec Houtput H14e38")).
  iSplitL; first (iApply (table_entry_14e38 with "Hcode Hspec Houtput H14e48")).
  iSplitL; first (iApply (table_entry_14e48 with "Hcode Hspec Houtput H14e58")).
  iSplitL; first (iApply (table_entry_14e58 with "Hcode Hspec Houtput H14e68")).
  iSplitL; first (iApply (table_entry_14e68 with "Hcode Hspec Houtput H14e78")).
  iSplitL; first (iApply (table_entry_14e78 with "Hcode Hspec Houtput Hedge0")).
  iSplitL; first (iApply (table_entry_1572c with "Hcode Hspec Houtput Hedge1")).
  iSplitL; first (iApply (table_entry_15118 with "Hcode Hspec Hedge2 Hedge3")).
  iSplitL; first (iApply (table_entry_15154 with "Hcode Hspec Hedge4 Hedge5")).
  iSplitL; first (iApply (table_entry_153a8 with "Hcode Hspec Hedge6 Hedge7")).
  iSplitL; first (iApply (table_entry_153b4 with "Hcode Hspec Hedge8")).
  iSplitL; first (iApply (table_entry_15558 with "Hcode Hspec Hedge9 Hedge10")).
  iSplitL; first (iApply (table_entry_15614 with "Hcode Hspec Hedge11 Hedge12")).
  iSplitL; first (iApply (table_entry_1565c with "Hcode Hspec Hedge13")).
  iSplitL; first (iApply (table_entry_150fc with "Hcode Hspec Hint Hedge14")).
  iSplitL; first (iApply (table_entry_15148 with "Hcode Hspec Hint Hedge15")).
  iSplitL; first (iApply (table_entry_151c4 with "Hcode Hspec Hint Hedge16")).
  iSplitL; first (iApply (table_entry_151d4 with "Hcode Hspec Hedge17 Hedge18")).
  iSplitL; first (iApply (table_entry_1521c with "Hcode Hspec Hedge19 Hedge20")).
  iSplitL; first (iApply (table_entry_153c0 with "Hcode Hspec Hint Hedge21")).
  iSplitL; first (iApply (table_entry_15574 with "Hcode Hspec Hint Hedge22")).
  iSplitL; first (iApply (table_entry_15620 with "Hcode Hspec Hint Hedge23")).
  iSplitL; first (iApply (table_entry_15750 with "Hcode Hspec Hedge24 Hedge25")).
  done.
Qed.
End table.

Print Assumptions write_success_block_table_cases.
