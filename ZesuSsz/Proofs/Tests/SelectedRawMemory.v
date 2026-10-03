Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SealedCoverage.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Definition memoryRaw (base : Z) (bytes : list (bv 8)) (stack : Z) (value : bv 64) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗ stack ↦ₘ value ∗ True)%I.
Definition memorySeal (base : Z) (bytes : list (bv 8)) (stack : Z) (value : bv 64) : iProp Sigma :=
  memoryRaw base bytes stack value.
Global Instance memoryDecl base bytes stack value :
  ZesuSealed (memorySeal base bytes stack value) (memoryRaw base bytes stack value)
    [(base, base + Z.of_nat (length bytes)); (stack,stack+8)] [].
Proof. done. Qed.
Global Opaque memorySeal.
Definition protectedRaw (address : Z) (value : bv 64) : iProp Sigma := (address ↦ₘ value ∗ True)%I.
Definition protectedSeal (address : Z) (value : bv 64) : iProp Sigma := protectedRaw address value.
Global Instance protectedDecl address value :
  ZesuSealed (protectedSeal address value) (protectedRaw address value) [(address,address+8)] [].
Proof. done. Qed.
Global Opaque protectedSeal.
Definition codeResources (lookup : Z -> option isla_trace) (specLookup : Z -> option (iProp Sigma)) : iProp Sigma :=
  (instr_lookup_resources lookup ∗ instr_body_lookup_resources specLookup)%I.
Global Instance codeResourcesPersistent lookup specLookup : Persistent (codeResources lookup specLookup).
Proof. apply _. Qed.
Global Instance : LithiumUnfold (@codeResources) := I.
Global Opaque codeResources.
Lemma selected_raw_head (pointer : bv 64) (base stack : Z) (processed remaining : nat)
    (bytes : list (bv 8)) (word protected : bv 64)
    (lookup : Z -> option isla_trace) (specLookup : Z -> option (iProp Sigma)) :
  (base + Z.of_nat (length bytes) < machineRamEnd defaultMap)%Z ->
  (mapRamBase defaultMap <= base)%Z ->
  bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z ->
  length bytes = (32 * (processed + S remaining))%nat ->
  codeResources lookup specLookup -∗ protectedSeal (-16) protected -∗
  memorySeal base bytes stack word -∗
  memoryRaw base bytes stack word ∗ protectedSeal (-16) protected ∗ codeResources lookup specLookup.
Proof.
  intros Hram Hbase Hpointer Hlength.
  iIntros "#Hcode Hprotected Hmemory".
  zesu_open_declared_cover (bv_unsigned (pointer+25)).
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iRename select (base ↦ₘ∗ bytes)%I into "Harray".
  iRename select (protectedSeal (-16) protected) into "Hpreserved".
  iMatchHyp ltac:(fun _ body => let wanted := constr:(codeResources lookup specLookup) in constr_eq body wanted).
  iFrame "Hpreserved Hcode".
  iEval (unfold memoryRaw).
  iFrame.
Qed.
Definition directArraySeal (base : Z) (bytes : list (bv 8)) : iProp Sigma := (base ↦ₘ∗ bytes)%I.
Global Instance directArrayDecl base bytes :
  ZesuSealed (directArraySeal base bytes) (base ↦ₘ∗ bytes)%I [(base,base+Z.of_nat(length bytes))] [].
Proof. done. Qed.
Global Opaque directArraySeal.
Lemma selected_direct_array base bytes :
  (0 < length bytes)%nat -> directArraySeal base bytes -∗ (base ↦ₘ∗ bytes)%I.
Proof.
  intros Hlength. iIntros "Hmemory".
  zesu_open_declared_cover base.
  iRename select (base ↦ₘ∗ bytes)%I into "Harray".
  iExact "Harray".
Qed.
End Tests.
Print Assumptions selected_raw_head.
Print Assumptions selected_direct_array.
