Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
From Coq Require Import Lists.List.
Import ListNotations.
Definition elf_rx_32 : list (bv 8) := [
  BV 8 80; BV 8 11; BV 8 2; BV 8 120; BV 8 193; BV 8 200; BV 8 201; BV 8 68; BV 8 14; BV 8 0; BV 8 0; BV 8 0; BV 8 40; BV 8 0; BV 8 0; BV 8 0;
  BV 8 64; BV 8 6; BV 8 0; BV 8 0; BV 8 64; BV 8 241; BV 8 255; BV 8 255; BV 8 164; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 68; BV 8 14; BV 8 80;
  BV 8 84; BV 8 129; BV 8 1; BV 8 136; BV 8 2; BV 8 137; BV 8 3; BV 8 146; BV 8 4; BV 8 147; BV 8 5; BV 8 10; BV 8 80; BV 8 11; BV 8 2; BV 8 116;
  BV 8 193; BV 8 200; BV 8 201; BV 8 210; BV 8 211; BV 8 68; BV 8 14; BV 8 0
].
Lemma elf_rx_32_length : List.length elf_rx_32 = 56%nat.
Proof. vm_compute. reflexivity. Qed.
