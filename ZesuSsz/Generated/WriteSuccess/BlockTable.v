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

(* Closed entries retain their original boundary arguments. *)
Definition writeSuccessBlockTable : blockTable Sigma :=
  [
   (0x14e28, State_14e28 sp bytes tail P);
   (0x14e38, State_14e38 sp bytes tail P);
   (0x14e48, State_14e48 sp bytes tail P);
   (0x14e58, State_14e58 sp bytes tail P);
   (0x14e68, State_14e68 sp bytes tail P);
   (0x14e78, State_14e78 sp bytes tail P);
   (0x1572c, State_1572c P sp root oldData oldSize tail);
   (0x15118, State_15118 b15118_tag b15118_P b15118_sp);
   (0x15154, State_15154 b15154_sp b15154_tag b15154_old_data b15154_P);
   (0x153a8, State_153a8 b153a8_pointer b153a8_count b153a8_P b153a8_sp);
   (0x153b4, State_153b4 b153b4_sp b153b4_index b153b4_old11 b153b4_P);
   (0x15558, State_15558 b15558_pointer b15558_count b15558_value22 b15558_P b15558_sp);
   (0x15614, State_15614 b15614_pointer b15614_count b15614_P b15614_sp);
   (0x1565c, State_1565c b1565c_sp b1565c_index b1565c_total b1565c_P)].

End table.
