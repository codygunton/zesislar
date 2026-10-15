Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
Require Import ZesuSsz.Compliance.FreeEntryIntroductions.
Require Import ZesuSsz.Automation.EntryIntro.
Open Scope Z_scope.

#[export] Instance freeEntry42134IntroductionRegistered
    `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro
    (freeEntryAt80042134 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes) _ :=
  freeEntry42134Introduction args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42154IntroductionRegistered
    `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro
    (freeEntryAt80042154 args x1 x2 x8 x10 x11 x12 x13 x14
      bufferBytes listBytes frameBytes) _ :=
  freeEntry42154Introduction args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes.
