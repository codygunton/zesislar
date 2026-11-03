Require Import ZesuSsz.Automation.SourceRegisterOrigin194.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import isla.riscv64.riscv64.
Require Import isla.automation.
Require Import lithium.base.
From Coq Require Import Strings.String.
From iris.proofmode Require Import environments.

Class ZesuSourceUnusedDeclaration (pc : bv 64) (variable : Z) (width : N) : Prop :=
  zesu_source_unused_declaration : True.
#[global] Hint Mode ZesuSourceUnusedDeclaration + + + : typeclass_instances.
Class ZesuSourceRegisterRead (pc : bv 64) (register field : string)
    (width : N) (key : string) : Prop := zesu_source_register_read : True.
#[global] Hint Mode ZesuSourceRegisterRead + + + - - : typeclass_instances.
