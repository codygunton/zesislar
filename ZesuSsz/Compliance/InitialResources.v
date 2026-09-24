Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuMachineMap.Machine.

Definition ValidStartSp (startSp : Z) : Prop :=
  startSp `mod` 16 = 0 /\
  mapRamBase defaultMap + 0xc00 <= startSp /\
  startSp + 0x450 < machineRamEnd defaultMap.

Definition zesuMainArgs (startSp : Z) (input : ByteString) :
    DecodeBoundaryArgs := {|
  decodeReturnAddress := 0x14cfc;
  decodeSavedReturnAddress := 0x1012c;
  decodeInputAddress := mapInputBufferAddress defaultMap;
  decodeInput := input;
  decodeStackPointer := startSp - 896;
  decodeAllocatorStateAddress := mapIoContextAddress defaultMap - 8;
  decodeAllocatorVtableAddress := mapRodataBase defaultMap + 0x5a8;
  decodeSavedRegisters := List.repeat (BV 64 0) 12;
  decodeFramePadding := List.repeat (BV 8 0) 6
|}.

Lemma zesu_main_args_pure startSp input :
  ValidStartSp startSp ->
  InputWithinBound input ->
  decodeReturnAddress (zesuMainArgs startSp input) = 0x14cfc /\
  decodeSavedReturnAddress (zesuMainArgs startSp input) = 0x1012c /\
  decodeInputAddress (zesuMainArgs startSp input) = mapInputBufferAddress defaultMap /\
  decodeAllocatorStateAddress (zesuMainArgs startSp input) =
    mapIoContextAddress defaultMap - 8 /\
  decodeAllocatorVtableAddress (zesuMainArgs startSp input) =
    mapRodataBase defaultMap + 0x5a8 /\
  List.length (decodeSavedRegisters (zesuMainArgs startSp input)) = 12%nat /\
  List.length (decodeFramePadding (zesuMainArgs startSp input)) = 6%nat /\
  decodeStackPointer (zesuMainArgs startSp input) `mod` 16 = 0 /\
  mapRamBase defaultMap + 0x880 <= decodeStackPointer (zesuMainArgs startSp input) /\
  decodeStackPointer (zesuMainArgs startSp input) + 0x7d0 < machineRamEnd defaultMap /\
  List.length (decodeInput (zesuMainArgs startSp input)) <= maxSszInputSize.
Proof.
  intros Hsp Hbound.
  unfold InputWithinBound, maxInputBytes in Hbound.
  destruct Hsp as (Halign & Hlower & Hupper).
  have HalignD : (startSp - 896) `mod` 16 = 0.
  { rewrite Zminus_mod Halign. reflexivity. }
  unfold zesuMainArgs.
  cbn [decodeReturnAddress decodeSavedReturnAddress decodeInputAddress
    decodeAllocatorStateAddress decodeAllocatorVtableAddress
    decodeSavedRegisters decodeFramePadding decodeStackPointer decodeInput
    List.length List.repeat].
  repeat (split; [reflexivity |]).
  split; first exact HalignD.
  split; first lia.
  split; first lia.
  unfold maxSszInputSize. lia.
Qed.
