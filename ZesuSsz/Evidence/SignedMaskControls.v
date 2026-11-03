Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch198Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch198Structural.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch199Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachineBranch199Structural.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot322Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot322Structural.
Open Scope Z_scope.

Require Import ZesuSsz.Automation.All.

Lemma signed_mask_exact_0
(Sigma : gFunctors)
(islaG0 : islaG Sigma)
(H : threadG)
(args : DecodeItemArgs)
(K : uPred (iResUR Sigma))
(entry_fact_1 : @eq Z (decodeItemInputLength args)
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemInputBytes args))))
(entry_fact_2 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (decodeItemBeforeStorage args))
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
(entry_fact_3 : Z.le Z0 (decodeItemInputPointer args))
(entry_fact_4 : Z.le Z0 (decodeItemInputLength args))
(entry_fact_5 : Z.le Z0 (decodeItemOutputPointer args))
(entry_fact_6 : Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_7 : Z.lt
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_8 : Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
(entry_fact_9 : Z.lt (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_10 : Z.le
  (Z.add
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
     (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
(entry_fact_11 : Z.le (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_12 : Z.le Z0 (decodeItemReturnAddress args))
(entry_fact_13 : Z.lt (decodeItemReturnAddress args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_14 : @eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
(entry_fact_15 : Z.le
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
  (decodeItemOutputPointer args))
(entry_fact_16 : Z.le
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_17 : Z.le Z0 (decodeItemInputEnd args))
(entry_fact_18 : Z.lt (decodeItemInputEnd args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_19 : Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (decodeItemInputEnd args))
(H0 : Z.lt
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H1 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
(H2 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H3 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H4 : Z.le
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
(H5 : not
  (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))) I)))
(H6 : not
  (@eq Z
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))))
(H7 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H8 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H9 : @eq Z
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H10 : Z.le (decodeItemInputLength args)
  (Zpos
     (xI
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(b : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H11 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b0 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H12 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(H13 : Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))))
(H14 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H15 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H16 : and (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H17 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H18 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
(H19 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))) true)
(H20 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H21 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H22 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
(H23 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))) true)
(H24 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H25 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H26 : Z.le
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H27 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H28 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H29 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H30 : @eq bool
  (@bool_decide
     (Z.le (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H31 : @eq bool
  (@bool_decide
     (@eq Z
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H32 : @eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_sign_extend (Npos (xO (xO (xO xH))))
        (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
  (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
(H33 : @eq bool
  (@bool_decide
     (Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H34 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H35 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))) true)
(H36 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H37 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H38 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))) true)
(H39 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))) true)
(H40 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H41 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H42 : @eq bool
  (@bool_decide
     (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))) true)
(H43 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H44 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputEnd args))) true)
(H45 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H46 : @eq bool
  (@bool_decide
     (Z.le
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))) true)
(H47 : @eq bool
  (@bool_decide
     (@eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0))
  true)
(H48 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H49 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemReturnAddress args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemReturnAddress args))) true)
(H50 : @eq bool
  (@bool_decide
     (Z.le (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H51 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
  true)
(H52 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H53 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
        (decodeItemStackPointer args))) true)
(H54 : @eq bool
  (@bool_decide
     (Z.lt
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H55 : @eq bool
  (@bool_decide
     (Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H56 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemOutputPointer args))) true)
(H57 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputLength args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args))) true)
(H58 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputPointer args))) true)
(H59 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemBeforeStorage args)))
  (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
(H60 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))
  true)
(H61 : @eq bool
  (@bool_decide
     (@eq Z (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))) true)
(H62 : and
  (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
     (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H63 : and (Z.le Z0 (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H64 : and (Z.le Z0 (decodeItemReturnAddress args))
  (Z.lt (decodeItemReturnAddress args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H65 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H66 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H67 : and (Z.le Z0 (decodeItemInputLength args))
  (Z.le (decodeItemInputLength args)
     (Zpos
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H68 : @eq bool
  (andb
     (@bool_decide (Z.le Z0 (decodeItemInputLength args))
        (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args)))
     (@bool_decide
        (Z.le (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H69 : and
  (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H70 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H71 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H72 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H73 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H74 : @eq bool
  (andb
     (@bool_decide
        (Z.le
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H75 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H76 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
           (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H77 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H78 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H79 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))))
(H80 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))) :
Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)).
Proof.
intros.
Fail zesu_signed_mask_branch.
Abort.

Lemma signed_mask_exact_1
(Sigma : gFunctors)
(islaG0 : islaG Sigma)
(H : threadG)
(args : DecodeItemArgs)
(K : uPred (iResUR Sigma))
(entry_fact_1 : @eq Z (decodeItemInputLength args)
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemInputBytes args))))
(entry_fact_2 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (decodeItemBeforeStorage args))
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
(entry_fact_3 : Z.le Z0 (decodeItemInputPointer args))
(entry_fact_4 : Z.le Z0 (decodeItemInputLength args))
(entry_fact_5 : Z.le Z0 (decodeItemOutputPointer args))
(entry_fact_6 : Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_7 : Z.lt
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_8 : Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
(entry_fact_9 : Z.lt (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_10 : Z.le
  (Z.add
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
     (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
(entry_fact_11 : Z.le (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_12 : Z.le Z0 (decodeItemReturnAddress args))
(entry_fact_13 : Z.lt (decodeItemReturnAddress args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_14 : @eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
(entry_fact_15 : Z.le
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
  (decodeItemOutputPointer args))
(entry_fact_16 : Z.le
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_17 : Z.le Z0 (decodeItemInputEnd args))
(entry_fact_18 : Z.lt (decodeItemInputEnd args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_19 : Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (decodeItemInputEnd args))
(H0 : Z.lt
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H1 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
(H2 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H3 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H4 : Z.le
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
(H5 : not
  (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))) I)))
(H6 : not
  (@eq Z
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))))
(H7 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H8 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H9 : @eq Z
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H10 : Z.le (decodeItemInputLength args)
  (Zpos
     (xI
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(b : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H11 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b0 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H12 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(H13 : not
  (Z.ge
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))))
(H14 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H15 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H16 : and (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H17 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H18 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
(H19 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))) true)
(H20 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H21 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H22 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
(H23 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))) true)
(H24 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H25 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H26 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H27 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H28 : @eq bool
  (@bool_decide
     (Z.le (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H29 : @eq bool
  (@bool_decide
     (@eq Z
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H30 : @eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_sign_extend (Npos (xO (xO (xO xH))))
        (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
  (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
(H31 : @eq bool
  (@bool_decide
     (Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H32 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H33 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))) true)
(H34 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H35 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H36 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))) true)
(H37 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))) true)
(H38 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H39 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H40 : @eq bool
  (@bool_decide
     (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))) true)
(H41 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H42 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputEnd args))) true)
(H43 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H44 : @eq bool
  (@bool_decide
     (Z.le
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))) true)
(H45 : @eq bool
  (@bool_decide
     (@eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0))
  true)
(H46 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H47 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemReturnAddress args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemReturnAddress args))) true)
(H48 : @eq bool
  (@bool_decide
     (Z.le (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H49 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
  true)
(H50 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H51 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
        (decodeItemStackPointer args))) true)
(H52 : @eq bool
  (@bool_decide
     (Z.lt
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H53 : @eq bool
  (@bool_decide
     (Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H54 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemOutputPointer args))) true)
(H55 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputLength args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args))) true)
(H56 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputPointer args))) true)
(H57 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemBeforeStorage args)))
  (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
(H58 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))
  true)
(H59 : @eq bool
  (@bool_decide
     (@eq Z (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))) true)
(H60 : and
  (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
     (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H61 : and (Z.le Z0 (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H62 : and (Z.le Z0 (decodeItemReturnAddress args))
  (Z.lt (decodeItemReturnAddress args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H63 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H64 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H65 : and (Z.le Z0 (decodeItemInputLength args))
  (Z.le (decodeItemInputLength args)
     (Zpos
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H66 : @eq bool
  (andb
     (@bool_decide (Z.le Z0 (decodeItemInputLength args))
        (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args)))
     (@bool_decide
        (Z.le (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H67 : and
  (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H68 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H69 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H70 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H71 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H72 : @eq bool
  (andb
     (@bool_decide
        (Z.le
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H73 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H74 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
           (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H75 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H76 : not
  (Z.ge
     (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))))
(H77 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))) :
not
  (Z.ge
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))).
Proof.
intros.
Fail zesu_signed_mask_branch.
Abort.

Local Instance signed_mask_control_enabled : ZesuStepSignedMaskBranch := {}.

Lemma signed_mask_exact_enabled_0
(Sigma : gFunctors)
(islaG0 : islaG Sigma)
(H : threadG)
(args : DecodeItemArgs)
(K : uPred (iResUR Sigma))
(entry_fact_1 : @eq Z (decodeItemInputLength args)
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemInputBytes args))))
(entry_fact_2 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (decodeItemBeforeStorage args))
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
(entry_fact_3 : Z.le Z0 (decodeItemInputPointer args))
(entry_fact_4 : Z.le Z0 (decodeItemInputLength args))
(entry_fact_5 : Z.le Z0 (decodeItemOutputPointer args))
(entry_fact_6 : Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_7 : Z.lt
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_8 : Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
(entry_fact_9 : Z.lt (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_10 : Z.le
  (Z.add
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
     (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
(entry_fact_11 : Z.le (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_12 : Z.le Z0 (decodeItemReturnAddress args))
(entry_fact_13 : Z.lt (decodeItemReturnAddress args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_14 : @eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
(entry_fact_15 : Z.le
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
  (decodeItemOutputPointer args))
(entry_fact_16 : Z.le
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_17 : Z.le Z0 (decodeItemInputEnd args))
(entry_fact_18 : Z.lt (decodeItemInputEnd args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_19 : Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (decodeItemInputEnd args))
(H0 : Z.lt
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H1 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
(H2 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H3 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H4 : Z.le
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
(H5 : not
  (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))) I)))
(H6 : not
  (@eq Z
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))))
(H7 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H8 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H9 : @eq Z
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H10 : Z.le (decodeItemInputLength args)
  (Zpos
     (xI
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(b : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H11 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b0 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H12 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(H13 : Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))))
(H14 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H15 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H16 : and (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H17 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H18 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
(H19 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))) true)
(H20 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H21 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H22 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
(H23 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))) true)
(H24 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H25 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H26 : Z.le
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H27 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H28 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H29 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H30 : @eq bool
  (@bool_decide
     (Z.le (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H31 : @eq bool
  (@bool_decide
     (@eq Z
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H32 : @eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_sign_extend (Npos (xO (xO (xO xH))))
        (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
  (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
(H33 : @eq bool
  (@bool_decide
     (Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H34 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H35 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))) true)
(H36 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H37 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H38 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))) true)
(H39 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))) true)
(H40 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H41 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H42 : @eq bool
  (@bool_decide
     (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))) true)
(H43 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H44 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputEnd args))) true)
(H45 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H46 : @eq bool
  (@bool_decide
     (Z.le
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))) true)
(H47 : @eq bool
  (@bool_decide
     (@eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0))
  true)
(H48 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H49 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemReturnAddress args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemReturnAddress args))) true)
(H50 : @eq bool
  (@bool_decide
     (Z.le (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H51 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
  true)
(H52 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H53 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
        (decodeItemStackPointer args))) true)
(H54 : @eq bool
  (@bool_decide
     (Z.lt
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H55 : @eq bool
  (@bool_decide
     (Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H56 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemOutputPointer args))) true)
(H57 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputLength args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args))) true)
(H58 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputPointer args))) true)
(H59 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemBeforeStorage args)))
  (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
(H60 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))
  true)
(H61 : @eq bool
  (@bool_decide
     (@eq Z (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))) true)
(H62 : and
  (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
     (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H63 : and (Z.le Z0 (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H64 : and (Z.le Z0 (decodeItemReturnAddress args))
  (Z.lt (decodeItemReturnAddress args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H65 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H66 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H67 : and (Z.le Z0 (decodeItemInputLength args))
  (Z.le (decodeItemInputLength args)
     (Zpos
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H68 : @eq bool
  (andb
     (@bool_decide (Z.le Z0 (decodeItemInputLength args))
        (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args)))
     (@bool_decide
        (Z.le (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H69 : and
  (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H70 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H71 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H72 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H73 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H74 : @eq bool
  (andb
     (@bool_decide
        (Z.le
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H75 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H76 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
           (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H77 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H78 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H79 : Z.ge
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))))
(H80 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))) :
Z.ge
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)).
Proof.
intros.
zesu_signed_mask_branch.
Qed.
Print Assumptions signed_mask_exact_enabled_0.

Lemma signed_mask_exact_enabled_1
(Sigma : gFunctors)
(islaG0 : islaG Sigma)
(H : threadG)
(args : DecodeItemArgs)
(K : uPred (iResUR Sigma))
(entry_fact_1 : @eq Z (decodeItemInputLength args)
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemInputBytes args))))
(entry_fact_2 : @eq nat
  (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
     (decodeItemBeforeStorage args))
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))
(entry_fact_3 : Z.le Z0 (decodeItemInputPointer args))
(entry_fact_4 : Z.le Z0 (decodeItemInputLength args))
(entry_fact_5 : Z.le Z0 (decodeItemOutputPointer args))
(entry_fact_6 : Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_7 : Z.lt
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_8 : Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
(entry_fact_9 : Z.lt (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_10 : Z.le
  (Z.add
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
     (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
(entry_fact_11 : Z.le (decodeItemStackPointer args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_12 : Z.le Z0 (decodeItemReturnAddress args))
(entry_fact_13 : Z.lt (decodeItemReturnAddress args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_14 : @eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
(entry_fact_15 : Z.le
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
  (decodeItemOutputPointer args))
(entry_fact_16 : Z.le
  (Z.add (decodeItemOutputPointer args) (Zpos (xO (xO (xO (xI (xO xH)))))))
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
(entry_fact_17 : Z.le Z0 (decodeItemInputEnd args))
(entry_fact_18 : Z.lt (decodeItemInputEnd args)
  (Zpos
     (xO
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(entry_fact_19 : Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
  (decodeItemInputEnd args))
(H0 : Z.lt
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H1 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
(H2 : Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H3 : Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H4 : Z.le
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
  (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
(H5 : not
  (@eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH)))))))) I)))
(H6 : not
  (@eq Z
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))))
(H7 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_sign_extend (Npos (xO (xO (xO xH))))
              (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
(H8 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H9 : @eq Z
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
  (@bv_unsigned (Npos (xO (xO (xO xH))))
     (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
        (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
(H10 : Z.le (decodeItemInputLength args)
  (Zpos
     (xI
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(b : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H11 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(b0 : bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
(H12 : @eq Z
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))
  Z0)
(H13 : not
  (Z.ge
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I)))))
(H14 : and
  (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H15 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H16 : and (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H17 : forall _ : not (@eq N (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0),
and
  (Z.le (Z.opp (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
  (Z.lt (@bv_signed (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
     (bv_half_modulus (Npos (xO (xO (xO (xO (xO (xO xH))))))))))
(H18 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
(H19 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b))) true)
(H20 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H21 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H22 : Z.lt (Zneg xH) (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
(H23 : @eq bool
  (@bool_decide
     (Z.lt (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))
     (@decide_rel Z Z Z.lt Z.lt_dec (Zneg xH)
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0))) true)
(H24 : Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
  (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
(H25 : @eq bool
  (@bool_decide
     (Z.lt (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
        (bv_modulus (Npos (xO (xO (xO (xO (xO (xO xH)))))))))) true)
(H26 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b0)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H27 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) b)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))
        Z0)) true)
(H28 : @eq bool
  (@bool_decide
     (Z.le (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
        (Zpos
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H29 : @eq bool
  (@bool_decide
     (@eq Z
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H30 : @eq (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_sign_extend (Npos (xO (xO (xO xH))))
        (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))
  (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
(H31 : @eq bool
  (@bool_decide
     (Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H32 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_sign_extend (Npos (xO (xO (xO xH))))
                    (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
                 (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))))) true)
(H33 : @eq bool
  (@bool_decide
     (Z.le
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))) true)
(H34 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H35 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))) true)
(H36 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_sign_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH)))))))) Z0 I)))) true)
(H37 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I))
        (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_unsigned (Npos (xO (xO (xO xH))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))) true)
(H38 : Z.lt
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
  (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
(H39 : @eq bool
  (@bool_decide
     (Z.lt
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xO (xI (xI (xO xH)))))))) I)))
        (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
              (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@bv_unsigned (Npos (xO (xO (xO xH))))
                    (@nth (bv (Npos (xO (xO (xO xH))))) O
                       (decodeItemInputBytes args)
                       (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))))) true)
(H40 : @eq bool
  (@bool_decide
     (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (decodeItemInputEnd args))) true)
(H41 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemInputEnd args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H42 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputEnd args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputEnd args))) true)
(H43 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H44 : @eq bool
  (@bool_decide
     (Z.le
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (decodeItemOutputPointer args))) true)
(H45 : @eq bool
  (@bool_decide
     (@eq Z (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0)
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.modulo (decodeItemReturnAddress args) (Zpos (xO (xO xH)))) Z0))
  true)
(H46 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemReturnAddress args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H47 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemReturnAddress args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemReturnAddress args))) true)
(H48 : @eq bool
  (@bool_decide
     (Z.le (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
  true)
(H49 : @eq bool
  (@bool_decide
     (Z.le
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec
        (Z.add
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
           (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
  true)
(H50 : @eq bool
  (@bool_decide
     (Z.lt (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec (decodeItemStackPointer args)
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H51 : @eq bool
  (@bool_decide
     (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
     (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
        (decodeItemStackPointer args))) true)
(H52 : @eq bool
  (@bool_decide
     (Z.lt
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemOutputPointer args)
           (Zpos (xO (xO (xO (xI (xO xH)))))))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H53 : @eq bool
  (@bool_decide
     (Z.lt (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z Z.lt Z.lt_dec
        (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H54 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemOutputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemOutputPointer args))) true)
(H55 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputLength args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args))) true)
(H56 : @eq bool
  (@bool_decide (Z.le Z0 (decodeItemInputPointer args))
     (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputPointer args))) true)
(H57 : @eq Z
  (Z.of_nat
     (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
        (decodeItemBeforeStorage args)))
  (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
(H58 : @eq bool
  (@bool_decide
     (@eq Z
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemBeforeStorage args)))
        (Z.of_nat
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
                                                 (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))
  true)
(H59 : @eq bool
  (@bool_decide
     (@eq Z (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))
     (@decide_rel Z Z (@eq Z) Z.eq_dec (decodeItemInputLength args)
        (Z.of_nat
           (@Datatypes.length (bv (Npos (xO (xO (xO xH)))))
              (decodeItemInputBytes args))))) true)
(H60 : and
  (Z.le (Z.add (decodeItemInputPointer args) (decodeItemInputLength args))
     (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H61 : and (Z.le Z0 (decodeItemInputEnd args))
  (Z.lt (decodeItemInputEnd args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H62 : and (Z.le Z0 (decodeItemReturnAddress args))
  (Z.lt (decodeItemReturnAddress args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H63 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H64 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.lt (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H65 : and (Z.le Z0 (decodeItemInputLength args))
  (Z.le (decodeItemInputLength args)
     (Zpos
        (xI
           (xI
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(H66 : @eq bool
  (andb
     (@bool_decide (Z.le Z0 (decodeItemInputLength args))
        (@decide_rel Z Z Z.le Z.le_dec Z0 (decodeItemInputLength args)))
     (@bool_decide
        (Z.le (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemInputLength args)
           (Zpos
              (xI
                 (xI
                    (xI
                       (xI
                          (xI
                             (xI
                                (xI
                                   (xI
                                      (xI
                                         (xI
                                            (xI
                                               (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI
                                                 (xI (xI (xI (xI (xI xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  true)
(H67 : and
  (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H68 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xI (xI (xI (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H69 : and
  (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
  (Z.le
     (@bv_unsigned (Npos (xO (xO (xO xH))))
        (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
           (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
     (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))
(H70 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I))))
        (@decide_rel Z Z Z.le Z.le_dec
           (Zpos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (@bool_decide
        (Z.le
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))))
        (@decide_rel Z Z Z.le Z.le_dec
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH))))))))))) true)
(H71 : and
  (Z.le
     (Z.add
        (Zpos
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
        (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H72 : @eq bool
  (andb
     (@bool_decide
        (Z.le
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec
           (Z.add
              (Zpos
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xI (xO xH))))))))))))))))))))))))))))))))
              (Zpos (xO (xO (xO (xO xH)))))) (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H73 : and (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
  (Z.le (decodeItemStackPointer args)
     (Zpos
        (xO
           (xO
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH))))))))))))))))))))))))))))))))))
(H74 : @eq bool
  (andb
     (@bool_decide
        (Z.le (Zpos (xO (xO (xO (xO xH))))) (decodeItemStackPointer args))
        (@decide_rel Z Z Z.le Z.le_dec (Zpos (xO (xO (xO (xO xH)))))
           (decodeItemStackPointer args)))
     (@bool_decide
        (Z.le (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))
        (@decide_rel Z Z Z.le Z.le_dec (decodeItemStackPointer args)
           (Zpos
              (xO
                 (xO
                    (xO
                       (xO
                          (xO
                             (xO
                                (xO
                                   (xO
                                      (xO
                                         (xO
                                            (xO
                                               (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO
                                                 (xO (xO (xO (xO (xI xH)))))))))))))))))))))))))))))))))))
  true)
(H75 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_unsigned (Npos (xO (xO (xO xH))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I))))))
(H76 : not
  (Z.ge
     (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (Z_to_bv (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@bv_unsigned (Npos (xO (xO (xO xH))))
              (@nth (bv (Npos (xO (xO (xO xH))))) O
                 (decodeItemInputBytes args)
                 (@BV (Npos (xO (xO (xO xH)))) Z0 I)))))
     (Zpos (xO (xO (xO (xO (xO (xO (xI xH))))))))))
(H77 : Z.lt (Zpos (xI (xI (xI (xO (xI (xI (xO xH))))))))
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
     (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
        (@bv_sign_extend (Npos (xO (xO (xO xH))))
           (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (@nth (bv (Npos (xO (xO (xO xH))))) O (decodeItemInputBytes args)
              (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
        (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I)))) :
not
  (Z.ge
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@bv_zero_extend (Npos (xO (xO (xO (xO (xO (xO xH)))))))
           (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (@bv_and (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@bv_sign_extend (Npos (xO (xO (xO xH))))
                 (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (@nth (bv (Npos (xO (xO (xO xH))))) O
                    (decodeItemInputBytes args)
                    (@BV (Npos (xO (xO (xO xH)))) Z0 I)))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                 (Zpos (xI (xI (xI (xI (xI (xI (xI xH)))))))) I))))
     (@bv_signed (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
        (@BV (Npos (xO (xO (xO (xO (xO (xO (xO xH))))))))
           (Zpos (xO (xO (xO (xO (xO (xO (xI xH)))))))) I))).
Proof.
intros.
zesu_signed_mask_branch.
Qed.
Print Assumptions signed_mask_exact_enabled_1.

Lemma signed_mask_alternate_width (payload view : bv 16)
 (link : bv_and payload (BV 16 255) = view)
 (branch : bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
 bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >= bv_signed (BV 32 17).
Proof. intros. zesu_signed_mask_branch. Qed.
Print Assumptions signed_mask_alternate_width.
Lemma signed_mask_negated_alternate_width (payload view : bv 16)
 (link : bv_and payload (BV 16 255) = view)
 (branch : ~ bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
 ~ bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >= bv_signed (BV 32 17).
Proof. intros. zesu_signed_mask_branch. Qed.
Print Assumptions signed_mask_negated_alternate_width.
Lemma signed_mask_missing_link (payload view : bv 16)
 (branch : bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
 bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >= bv_signed (BV 32 17).
Proof. intros. Fail zesu_signed_mask_branch. Abort.
Lemma signed_mask_wrong_polarity (payload view : bv 16)
 (link : bv_and payload (BV 16 255) = view)
 (branch : ~ bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
 bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >= bv_signed (BV 32 17).
Proof. intros. Fail zesu_signed_mask_branch. Abort.
Lemma signed_mask_symbolic_bound (payload view : bv 16) (bound : bv 32)
 (link : bv_and payload (BV 16 255) = view)
 (branch : bv_signed (bv_zero_extend 32 view) >= bv_signed bound) :
 bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >= bv_signed bound.
Proof. intros. Fail zesu_signed_mask_branch. Abort.
Lemma signed_mask_symbolic_mask (payload view mask : bv 16)
 (link : bv_and payload mask = view)
 (branch : bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
 bv_signed (bv_zero_extend 32 (bv_and payload mask)) >= bv_signed (BV 32 17).
Proof. intros. Fail zesu_signed_mask_branch. Abort.
Lemma signed_mask_nonwidening (payload view : bv 16)
 (link : bv_and payload (BV 16 255) = view)
 (branch : bv_signed (bv_zero_extend 16 view) >= bv_signed (BV 16 17)) :
 bv_signed (bv_zero_extend 16 (bv_and payload (BV 16 255))) >= bv_signed (BV 16 17).
Proof. intros. Fail zesu_signed_mask_branch. Abort.
