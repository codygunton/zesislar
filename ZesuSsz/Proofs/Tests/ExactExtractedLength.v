Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
From Coq Require Import List Lia.
From stdpp Require Import list.
Open Scope nat_scope.

Lemma exact_extracted_length (outputBytes : list byte) (x12 : bv 64)
 (H3 : length outputBytes = 40%nat) :
(length
   (take 24 (<[16:=0%bv]> outputBytes) ++
    Z_to_bv 8 (Z.land (bv_unsigned x12) (Z.ones 8))
    :: Z_to_bv 8 (Z.land (bv_unsigned x12 ≫ 8) (Z.ones 8))
       :: Z_to_bv 8 (Z.land ((bv_unsigned x12 ≫ 8) ≫ 8) (Z.ones 8))
          :: Z_to_bv 8 (Z.land (((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
             :: Z_to_bv 8
                  (Z.land ((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                :: Z_to_bv 8
                     (Z.land (((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                        (Z.ones 8))
                   :: Z_to_bv 8
                        (Z.land
                           ((((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                           (Z.ones 8))
                      :: Z_to_bv 8
                           (Z.land
                              (((((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                                ≫ 8) ≫ 8) (Z.ones 8))
                         :: drop
                              (S
                                 (S
                                    (S
                                       (S
                                          (S
                                             (S
                                                (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (N.to_nat 8)))))))))))))))))))))))))
                              (<[16:=0%bv]> outputBytes)) = 40).
Proof. zesu_finish_contract_arithmetic. Qed.

Lemma exact_extracted_wrong_total (outputBytes : list byte) (x12 : bv 64)
 (H3 : length outputBytes = 40%nat) : True.
Proof.
 Fail assert (Hwrong : (length
   (take 24 (<[16:=0%bv]> outputBytes) ++
    Z_to_bv 8 (Z.land (bv_unsigned x12) (Z.ones 8))
    :: Z_to_bv 8 (Z.land (bv_unsigned x12 ≫ 8) (Z.ones 8))
       :: Z_to_bv 8 (Z.land ((bv_unsigned x12 ≫ 8) ≫ 8) (Z.ones 8))
          :: Z_to_bv 8 (Z.land (((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
             :: Z_to_bv 8
                  (Z.land ((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))
                :: Z_to_bv 8
                     (Z.land (((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                        (Z.ones 8))
                   :: Z_to_bv 8
                        (Z.land
                           ((((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                           (Z.ones 8))
                      :: Z_to_bv 8
                           (Z.land
                              (((((((bv_unsigned x12 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)
                                ≫ 8) ≫ 8) (Z.ones 8))
                         :: drop
                              (S
                                 (S
                                    (S
                                       (S
                                          (S
                                             (S
                                                (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (N.to_nat 8)))))))))))))))))))))))))
                              (<[16:=0%bv]> outputBytes)) = 41)) by zesu_finish_contract_arithmetic.
 exact I.
Qed.

Print Assumptions exact_extracted_length.
Print Assumptions exact_extracted_wrong_total.
