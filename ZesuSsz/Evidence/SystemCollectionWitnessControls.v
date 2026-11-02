Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From stdpp Require Import list bitvector.definitions.
Require Import ZesuSsz.Automation.SystemCollectionWitness.
From Coq Require Import Lists.List String.
Import ListNotations.
Open Scope string_scope.

Lemma system_bits_preserves `{!islaG Sigma} `{!threadG}
 (width : N) (name : string) (K : iProp Sigma) :
 reg_col [(KindReg name, BitsShape width)] ∗ K -∗
 reg_col [(KindReg name, BitsShape width)] ∗ K.
Proof.
 iIntros "[Hregisters HK]".
 Fail zesu_system_collection_witness constr:([(KindReg name, BitsShape width)]) constr:(0%nat) constr:((KindReg name, BitsShape width)) ltac:(fun word => idtac).
 assert (enabled : ZesuStepSystemCollectionWitness) by constructor.
 Fail zesu_system_collection_witness constr:([(KindField name "field", BitsShape width)]) constr:(0%nat) constr:((KindField name "field", BitsShape width)) ltac:(fun word => idtac).
 Fail zesu_system_collection_witness constr:([(KindReg name, BitsShape width)]) constr:(1%nat) constr:((KindReg name, BitsShape width)) ltac:(fun word => idtac).
 Fail zesu_system_collection_witness constr:([(KindReg name, BitsShape width)]) constr:(0%nat) constr:((KindField name "field", BitsShape width)) ltac:(fun word => idtac).
 zesu_system_collection_witness constr:([(KindReg name, BitsShape width)]) constr:(0%nat) constr:((KindReg name, BitsShape width)) ltac:(fun word => idtac).
 iFrame.

Qed.
Lemma system_mask_preserves `{!islaG Sigma} `{!threadG}
 (width : N) (name field : string) (mask expected : Z) (K : iProp Sigma) :
 reg_col [(KindReg name, StructShape [(field, MaskShape width mask expected)])] ∗ K -∗
 reg_col [(KindReg name, StructShape [(field, MaskShape width mask expected)])] ∗ K.
Proof.
 iIntros "[Hregisters HK]".
 assert (enabled : ZesuStepSystemCollectionWitness) by constructor.
 zesu_system_collection_witness constr:([(KindReg name, StructShape [(field, MaskShape width mask expected)])]) constr:(0%nat) constr:((KindReg name, StructShape [(field, MaskShape width mask expected)])) ltac:(fun word => match goal with Hmask : Z.land (bv_unsigned word) mask = expected |- _ => idtac end).
 iFrame.

Qed.
Lemma system_unsupported_refuses `{!islaG Sigma} `{!threadG}
 (name : string) (K : iProp Sigma) :
 reg_col [(KindReg name, StructShape [])] ∗ K -∗
 reg_col [(KindReg name, StructShape [])] ∗ K.
Proof.
 iIntros "[Hregisters HK]".
 assert (enabled : ZesuStepSystemCollectionWitness) by constructor.
 Fail zesu_system_collection_witness constr:([(KindReg name, StructShape [])]) constr:(0%nat) constr:((KindReg name, StructShape [])) ltac:(fun word => idtac).
 iFrame.

Qed.
Lemma system_missing_owner_refuses `{!islaG Sigma} `{!threadG}
 (width : N) (name : string) (K : iProp Sigma) : K -∗ K.
Proof.
 iIntros "HK".
 assert (enabled : ZesuStepSystemCollectionWitness) by constructor.
 Fail zesu_system_collection_witness constr:([(KindReg name, BitsShape width)]) constr:(0%nat) constr:((KindReg name, BitsShape width)) ltac:(fun word => idtac).
 iExact "HK".

Qed.
