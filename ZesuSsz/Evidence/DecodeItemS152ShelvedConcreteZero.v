Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_shelved_concretezero :
SHELVED_SIDECOND
  (@eq valu (RegVal_Base (Val_Bits (@bv_to_bvn (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) Z0 I))))
     (RegVal_Base
        (Val_Bits (@bv_to_bvn (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) Z0 (definitions.Z_to_bv_obligation_1 (Npos (xO (xO (xO (xO (xO (xO xH))))))) Z0)))))).
Proof.
unshelve_sidecond. apply f_equal. apply f_equal. apply f_equal. apply bv_eq. reflexivity.
Qed.
