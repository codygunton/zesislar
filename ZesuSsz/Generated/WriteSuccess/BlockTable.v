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

(* Closed entries retain their original boundary arguments. *)
Definition writeSuccessBlockTable : blockTable Sigma :=
  [
   (0x14e28, State_14e28 sp bytes tail P);
   (0x14e38, State_14e38 sp bytes tail P);
   (0x14e48, State_14e48 sp bytes tail P);
   (0x14e58, State_14e58 sp bytes tail P);
   (0x14e68, State_14e68 sp bytes tail P);
   (0x14e78, State_14e78 sp bytes tail P);
   (0x1572c, State_1572c sp oldra old5 oldData oldSize bytes tail P);
   (0x15118, State_15118 b15118_tag b15118_P b15118_sp);
   (0x15154, State_15154 b15154_sp b15154_tag b15154_old_data b15154_P);
   (0x153a8, State_153a8 b153a8_pointer b153a8_count b153a8_P b153a8_sp);
   (0x153b4, State_153b4 b153b4_sp b153b4_index b153b4_old11 b153b4_P);
   (0x15558, State_15558 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp);
   (0x15614, State_15614 b15614_pointer b15614_count b15614_P b15614_sp);
   (0x1565c, State_1565c b1565c_sp b1565c_index b1565c_total b1565c_P);
   (0x150fc, State_150fc b150fc_sp b150fc_value b150fc_oldra b150fc_old5 b150fc_old11 b150fc_tail b150fc_P);
   (0x15148, State_15148 b15148_sp b15148_value b15148_oldra b15148_old5 b15148_old11 b15148_tail b15148_P);
   (0x151c4, State_151c4 b151c4_sp b151c4_value b151c4_oldra b151c4_old5 b151c4_old11 b151c4_tail b151c4_P);
   (0x151d4, CapturedEntry_151d4 b151d4_sp b151d4_index b151d4_old11 b151d4_P);
   (0x1521c, State_1521c b1521c_sp b1521c_data b1521c_bytes b1521c_P);
   (0x153c0, State_153c0 b153c0_sp b153c0_savedX22 b153c0_old22 b153c0_old_ra b153c0_old5 b153c0_old_data b153c0_old_size b153c0_tail b153c0_P);
   (0x15574, State_15574 b15574_sp b15574_count b15574_oldra b15574_old5 b15574_old11 b15574_tail b15574_P);
   (0x15620, State_15620 b15620_sp b15620_value b15620_oldra b15620_old5 b15620_old11 b15620_tail b15620_P);
   (0x15750, State_15750 b15750_value b15750_Q b15750_Hvalue b15750_sp)].

End table.
