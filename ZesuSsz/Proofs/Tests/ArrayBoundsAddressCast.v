Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Automation.Switches.ArrayBounds.
From Coq Require Import List Lia.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.

Lemma output_updated_array_bound (args : DecodeItemArgs)
    (locals : DecodeItemReturnLocals)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hlength : length (returnStorage locals) = 40%nat) :
(Z.to_nat (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)) - decodeItemOutputPointer args) + N.to_nat 8 <=
 length
   (take (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args)) (returnStorage locals) ++
    Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8))
    :: Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) :: drop (Z.to_nat (decodeItemOutputPointer args + 32 - decodeItemOutputPointer args) + N.to_nat 2) (returnStorage locals)))%nat.
Proof. zesu_array_bounds_if_enabled. Qed.

Lemma array_cast_reject_unknown_pointer (pointer : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : True.
Proof.
  Fail assert (Hbad : SHELVED_SIDECOND
    (Z.to_nat (bv_unsigned (Z_to_bv 64 pointer) - pointer) + N.to_nat 8 <=
      length storage)%nat) by zesu_array_bounds_if_enabled.
  exact I.
Qed.
