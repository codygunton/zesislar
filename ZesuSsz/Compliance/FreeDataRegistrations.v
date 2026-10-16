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

Require Import ZesuSsz.Compliance.FreeLeafIntroductions.

#[export] Instance freeEntry41f7cLeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80041f7c args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry41f7cLeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry41fb4LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80041fb4 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry41fb4LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry41fd8LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80041fd8 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry41fd8LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42010LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80042010 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry42010LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42028LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80042028 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry42028LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42054LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80042054 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry42054LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42070LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80042070 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry42070LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry42090LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt80042090 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry42090LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry420b0LeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt800420b0 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry420b0LeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry420ccLeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt800420cc args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry420ccLeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry420ecLeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt800420ec args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry420ecLeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

#[export] Instance freeEntry4210cLeafIntroductionRegistered `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  ZesuEntryIntro (freeEntryAt8004210c args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes) _ :=
  freeEntry4210cLeafIntroduction args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes.

