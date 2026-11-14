From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Open Scope Z_scope.
Open Scope stdpp_scope.
Set Default Proof Mode "Classic".

Notation memcpyCsrPc := ((0x800e06c0) : Z) (only parsing).
Notation parentHeaderMemcpySource := ((0x80114fb8) : Z) (only parsing).
Notation parentHeaderMemcpyLength := ((80) : Z) (only parsing).

Definition parentHeaderMemcpyArguments (destination returnAddress : Z) :
    ZiskMemcpyArguments :=
  {| ziskMemcpyDestination := destination;
     ziskMemcpySource := parentHeaderMemcpySource;
     ziskMemcpyLength := parentHeaderMemcpyLength;
     ziskMemcpyReturnAddress := returnAddress |}.

(* The section permissions of the stock image (core/src/mem.rs:877-927).
   A read lies inside one populated readable section. A write lies in RAM
   and in no populated section that is not writable. *)
Definition stockZiskPermissions : ZiskRuntimePermissions :=
  {| ziskReadableSection := fun address count =>
       Exists (fun section =>
         sectionReadable section = true /\
         sectionBase section <= address /\
         address + count <= sectionEnd section)
         (mapPopulatedSections defaultMap);
     ziskWritableSection := fun address count =>
       mapRamBase defaultMap <= address /\
       address + count <= machineRamEnd defaultMap /\
       Forall (fun section =>
         sectionWritable section = true \/
         address + count <= sectionBase section \/
         sectionEnd section <= address)
         (mapPopulatedSections defaultMap) |}.

(* The runtime domain of the reached copy without the return address.
   machine_call supplies the return address conditions. *)
Definition parentHeaderMemcpyDomain (destination : Z) : Prop :=
  ziskMemcpyRange destination parentHeaderMemcpyLength /\
  ziskReadableSection stockZiskPermissions
    parentHeaderMemcpySource parentHeaderMemcpyLength /\
  ziskWritableSection stockZiskPermissions
    destination parentHeaderMemcpyLength /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8.

Lemma parentHeaderMemcpyDomain_runtime (destination returnAddress : Z) :
  parentHeaderMemcpyDomain destination ->
  0 <= returnAddress < 2 ^ 64 ->
  returnAddress mod 4 = 0 ->
  ziskMemcpyDomain stockZiskPermissions
    (parentHeaderMemcpyArguments destination returnAddress).
Proof.
  unfold parentHeaderMemcpyDomain, ziskMemcpyDomain, ziskMemcpyRange,
    ziskWord; cbn.
  intros (Hrange & Hread & Hwrite & Hextra) Hret Hmod.
  assert (Hland : Z.land returnAddress (-2) mod 4 = 0).
  { change (-2) with (Z.lnot (Z.ones 1)).
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2,
      Z.shiftr_div_pow2 by lia.
    change (2 ^ 1) with 2.
    pose proof (Z.div_mod returnAddress 4 ltac:(lia)) as Hsplit.
    rewrite Hmod in Hsplit. rewrite Z.add_0_r in Hsplit. rewrite Hsplit.
    replace (4 * (returnAddress / 4) / 2) with (2 * (returnAddress / 4)).
    - replace (2 * (returnAddress / 4) * 2) with (returnAddress / 4 * 4)
        by lia.
      apply Z.mod_mul. lia.
    - replace (4 * (returnAddress / 4)) with (2 * (returnAddress / 4) * 2)
        by lia.
      rewrite Z.div_mul; lia. }
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  split; [exact Hland |]. split; [exact Hextra |].
  intros _. split; [exact Hrange |]. split; [lia |].
  split; [exact Hread | exact Hwrite].
Qed.

(* The ZisK memcpy service (ZiskRuntime.v, from memcpy.s and dma_memcpy.rs)
   in the machine_call shape, restricted to the reached copy: source
   0x80114fb8 and length 80. It is a runtime boundary, not a proved spec:
   memcpy returns to ra with sp and the callee-saved registers preserved,
   stores the count at the extra-params word, and copies the source bytes
   to the destination. The three separately owned arrays exclude overlap,
   so this covers only the non-overlapping case of ziskMemcpyMemory.
   It uses no stack. Both ZisK system registers return with shape only.
   The tail transfer at 0x800d5da0 reaches it with the caller's ra. *)
Definition memcpyCallSpec2 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte),
      ⌜bv_unsigned (argv !!! 1%nat) = parentHeaderMemcpySource⌝ ∗
      ⌜bv_unsigned (argv !!! 2%nat) = parentHeaderMemcpyLength⌝ ∗
      ⌜parentHeaderMemcpyDomain (bv_unsigned (argv !!! 0%nat))⌝ ∗
      reg_col [(KindReg "zisk_input_end", BitsShape 64);
               (KindReg "zisk_free_input", BitsShape 64)] ∗
      parentHeaderMemcpySource ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? parentHeaderMemcpyLength ∗
      ziskExtraParamsAddress ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = parentHeaderMemcpyLength⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        reg_col [(KindReg "zisk_input_end", BitsShape 64);
                 (KindReg "zisk_free_input", BitsShape 64)] ∗
        parentHeaderMemcpySource ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        ziskExtraParamsAddress ↦ₘ∗ word64Bytes parentHeaderMemcpyLength ∗
        True)))%I.
Global Instance : LithiumUnfold (@memcpyCallSpec2) := I.
Global Typeclasses Opaque memcpyCallSpec2.

(* The trusted runtime premise: the memcpy entry satisfies memcpyCallSpec2. *)
Definition memcpyCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre memcpyCsrPc memcpyCallSpec2)%I.
