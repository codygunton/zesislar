Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
From Coq Require Import Lists.List micromega.Lia.
Require Import ZesuSsz.Generated.ElfImage.rx_00.
Require Import ZesuSsz.Generated.ElfImage.rx_01.
Require Import ZesuSsz.Generated.ElfImage.rx_02.
Require Import ZesuSsz.Generated.ElfImage.rx_03.
Require Import ZesuSsz.Generated.ElfImage.rx_04.
Require Import ZesuSsz.Generated.ElfImage.rx_05.
Require Import ZesuSsz.Generated.ElfImage.rx_06.
Require Import ZesuSsz.Generated.ElfImage.rx_07.
Require Import ZesuSsz.Generated.ElfImage.rx_08.
Require Import ZesuSsz.Generated.ElfImage.rx_09.
Require Import ZesuSsz.Generated.ElfImage.rx_10.
Require Import ZesuSsz.Generated.ElfImage.rx_11.
Require Import ZesuSsz.Generated.ElfImage.rx_12.
Require Import ZesuSsz.Generated.ElfImage.rx_13.
Require Import ZesuSsz.Generated.ElfImage.rx_14.
Require Import ZesuSsz.Generated.ElfImage.rx_15.
Require Import ZesuSsz.Generated.ElfImage.rx_16.
Require Import ZesuSsz.Generated.ElfImage.rx_17.
Require Import ZesuSsz.Generated.ElfImage.rx_18.
Require Import ZesuSsz.Generated.ElfImage.rx_19.
Require Import ZesuSsz.Generated.ElfImage.rx_20.
Require Import ZesuSsz.Generated.ElfImage.rx_21.
Require Import ZesuSsz.Generated.ElfImage.rx_22.
Require Import ZesuSsz.Generated.ElfImage.rx_23.
Require Import ZesuSsz.Generated.ElfImage.rx_24.
Require Import ZesuSsz.Generated.ElfImage.rx_25.
Require Import ZesuSsz.Generated.ElfImage.rx_26.
Require Import ZesuSsz.Generated.ElfImage.rx_27.
Require Import ZesuSsz.Generated.ElfImage.rx_28.
Require Import ZesuSsz.Generated.ElfImage.rx_29.
Require Import ZesuSsz.Generated.ElfImage.rx_30.
Require Import ZesuSsz.Generated.ElfImage.rx_31.
Require Import ZesuSsz.Generated.ElfImage.rx_32.
Require Import ZesuSsz.Generated.ElfImage.rw_00.
Definition elfRxBytes : list (bv 8) :=
  elf_rx_00 ++
  elf_rx_01 ++
  elf_rx_02 ++
  elf_rx_03 ++
  elf_rx_04 ++
  elf_rx_05 ++
  elf_rx_06 ++
  elf_rx_07 ++
  elf_rx_08 ++
  elf_rx_09 ++
  elf_rx_10 ++
  elf_rx_11 ++
  elf_rx_12 ++
  elf_rx_13 ++
  elf_rx_14 ++
  elf_rx_15 ++
  elf_rx_16 ++
  elf_rx_17 ++
  elf_rx_18 ++
  elf_rx_19 ++
  elf_rx_20 ++
  elf_rx_21 ++
  elf_rx_22 ++
  elf_rx_23 ++
  elf_rx_24 ++
  elf_rx_25 ++
  elf_rx_26 ++
  elf_rx_27 ++
  elf_rx_28 ++
  elf_rx_29 ++
  elf_rx_30 ++
  elf_rx_31 ++
  elf_rx_32.
Definition elfRwBytes : list (bv 8) := elf_rw_00.
Lemma elf_rx_length : List.length elfRxBytes = 0x8038%nat.
Proof. unfold elfRxBytes. repeat rewrite app_length. rewrite elf_rx_00_length elf_rx_01_length elf_rx_02_length elf_rx_03_length elf_rx_04_length elf_rx_05_length elf_rx_06_length elf_rx_07_length elf_rx_08_length elf_rx_09_length elf_rx_10_length elf_rx_11_length elf_rx_12_length elf_rx_13_length elf_rx_14_length elf_rx_15_length elf_rx_16_length elf_rx_17_length elf_rx_18_length elf_rx_19_length elf_rx_20_length elf_rx_21_length elf_rx_22_length elf_rx_23_length elf_rx_24_length elf_rx_25_length elf_rx_26_length elf_rx_27_length elf_rx_28_length elf_rx_29_length elf_rx_30_length elf_rx_31_length elf_rx_32_length. reflexivity. Qed.
Lemma elf_rw_length : List.length elfRwBytes = 0x10%nat.
Proof. exact elf_rw_00_length. Qed.
