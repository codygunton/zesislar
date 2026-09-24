Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
From Coq Require Import Lists.List.
Import ListNotations.
Definition elf_rw_00 : list (bv 8) := [
  BV 8 0; BV 8 160; BV 8 1; BV 8 32; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 160; BV 8 1; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0
].
Lemma elf_rw_00_length : List.length elf_rw_00 = 16%nat.
Proof. vm_compute. reflexivity. Qed.
