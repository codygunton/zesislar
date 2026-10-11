Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import ZArith NArith Lia List.
Open Scope Z_scope.

Lemma s152_shelved_flag (b : bv 64) :
Z.land (bv_unsigned b) 131072 = 0 ->
SHELVED_SIDECOND
  (@eq base_val
     (Val_Bool
        (@bool_decide
           (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH))))))) b
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))) I))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) Z0 I))
           (@decide_rel (bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))) (bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))) (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
              (bv_eq_dec (Npos (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH))))))) b
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))) I))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) Z0 I)))) (Val_Bool true)).
Proof.
intros Hflag. unshelve_sidecond. assert (Hbits : bv_and b 131072 = 0%bv). { apply bv_eq. rewrite bv_and_unsigned. change (Z.land (bv_unsigned b) 131072 = 0). exact Hflag. } rewrite bool_decide_true; [reflexivity | exact Hbits].
Qed.
