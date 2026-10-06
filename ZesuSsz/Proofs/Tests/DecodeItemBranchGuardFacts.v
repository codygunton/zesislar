Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Open Scope Z_scope.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs) (prefix : bv 64) (inputPrefix : byte) (rest : list byte).
Context (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args).
Context (Hhead : decodeItemInputHead args inputPrefix rest).
Context (Hlow : 192 <= bv_unsigned inputPrefix) (Hhigh : bv_unsigned inputPrefix <= 247).
Context (Hvalue : bv_unsigned prefix = bv_unsigned inputPrefix).
Lemma rejected_hint
 (Hguard : bv_signed (bv_zero_extend 128 (bv_and (prefix + 64) 255)) >=
   bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args)))) :
 SimplAnd (decodeItemRejectedFacts args) True.
Proof using All. typeclasses eauto. Qed.
Lemma accepted_hint
 (Hguard : ~ bv_signed (bv_zero_extend 128 (bv_and (prefix + 64) 255)) >=
   bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args)))) :
 SimplAnd (decodeItemAcceptedFacts args true 1 (bv_unsigned inputPrefix - 192)) True.
Proof using All. typeclasses eauto. Qed.
Lemma fault_hint
 (Hnonzero : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0)
 (Hfault : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args) + 0) + 1) <=
   bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd args)))) :
 SimplAnd (bv_unsigned inputPrefix <= 127) True.
Proof using All. typeclasses eauto. Qed.
End Tests.
