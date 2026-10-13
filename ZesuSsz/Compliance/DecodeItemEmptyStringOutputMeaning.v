Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.DecodeItemReturnExitPure.

(* This image is the exact retained five-store output. *)
Definition decodeItemEmptyStringUpdatedImage (locals : DecodeItemReturnLocals) : list byte :=
  (@cons (bv (Npos (xO (xO (xO xH)))))
     (Z_to_bv (Npos (xO (xO (xO xH))))
        (Z.land
           (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
              (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))
           (Z.ones (Zpos (xO (xO (xO xH)))))))
     (@cons (bv (Npos (xO (xO (xO xH)))))
        (Z_to_bv (Npos (xO (xO (xO xH))))
           (Z.land
              (Z.shiftr
                 (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                    (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))
                 (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH)))))))
        (@cons (bv (Npos (xO (xO (xO xH)))))
           (Z_to_bv (Npos (xO (xO (xO xH))))
              (Z.land
                 (Z.shiftr
                    (Z.shiftr
                       (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                          (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                             (Zpos xH) I)) (Zpos (xO (xO (xO xH)))))
                    (Zpos (xO (xO (xO xH)))))
                 (Z.ones (Zpos (xO (xO (xO xH)))))))
           (@cons (bv (Npos (xO (xO (xO xH)))))
              (Z_to_bv (Npos (xO (xO (xO xH))))
                 (Z.land
                    (Z.shiftr
                       (Z.shiftr
                          (Z.shiftr
                             (@bv_unsigned
                                (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                   (Zpos xH) I)) (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH))))) 
                       (Zpos (xO (xO (xO xH)))))
                    (Z.ones (Zpos (xO (xO (xO xH)))))))
              (@cons (bv (Npos (xO (xO (xO xH)))))
                 (Z_to_bv (Npos (xO (xO (xO xH))))
                    (Z.land
                       (Z.shiftr
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (@bv_unsigned
                                      (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                      (@BV
                                         (Npos
                                            (xO (xO (xO (xO (xO (xO xH)))))))
                                         (Zpos xH) I))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Zpos (xO (xO (xO xH)))))
                       (Z.ones (Zpos (xO (xO (xO xH)))))))
                 (@cons (bv (Npos (xO (xO (xO xH)))))
                    (Z_to_bv (Npos (xO (xO (xO xH))))
                       (Z.land
                          (Z.shiftr
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (@bv_unsigned
                                            (Npos
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                            (@BV
                                               (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                               (Zpos xH) I))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Zpos (xO (xO (xO xH)))))
                          (Z.ones (Zpos (xO (xO (xO xH)))))))
                    (@cons (bv (Npos (xO (xO (xO xH)))))
                       (Z_to_bv (Npos (xO (xO (xO xH))))
                          (Z.land
                             (Z.shiftr
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Zpos (xO (xO (xO xH)))))
                             (Z.ones (Zpos (xO (xO (xO xH)))))))
                       (@cons (bv (Npos (xO (xO (xO xH)))))
                          (Z_to_bv (Npos (xO (xO (xO xH))))
                             (Z.land
                                (Z.shiftr
                                   (Z.shiftr
                                      (Z.shiftr
                                         (Z.shiftr
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Zpos (xO (xO (xO xH)))))
                                   (Zpos (xO (xO (xO xH)))))
                                (Z.ones (Zpos (xO (xO (xO xH)))))))
                          (@cons (bv (Npos (xO (xO (xO xH)))))
                             (Z_to_bv (Npos (xO (xO (xO xH))))
                                (Z.land
                                   (@bv_unsigned
                                      (Npos (xO (xO (xO (xO (xO (xO xH)))))))
                                      (@BV
                                         (Npos
                                            (xO (xO (xO (xO (xO (xO xH)))))))
                                         Z0 I))
                                   (Z.ones (Zpos (xO (xO (xO xH)))))))
                             (@cons (bv (Npos (xO (xO (xO xH)))))
                                (Z_to_bv (Npos (xO (xO (xO xH))))
                                   (Z.land
                                      (Z.shiftr
                                         (@bv_unsigned
                                            (Npos
                                               (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                            (@BV
                                               (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                               Z0 I))
                                         (Zpos (xO (xO (xO xH)))))
                                      (Z.ones (Zpos (xO (xO (xO xH)))))))
                                (@cons (bv (Npos (xO (xO (xO xH)))))
                                   (Z_to_bv (Npos (xO (xO (xO xH))))
                                      (Z.land
                                         (Z.shiftr
                                            (Z.shiftr
                                               (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Zpos (xO (xO (xO xH)))))
                                         (Z.ones (Zpos (xO (xO (xO xH)))))))
                                   (@cons (bv (Npos (xO (xO (xO xH)))))
                                      (Z_to_bv (Npos (xO (xO (xO xH))))
                                         (Z.land
                                            (Z.shiftr
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Zpos (xO (xO (xO xH)))))
                                            (Z.ones (Zpos (xO (xO (xO xH)))))))
                                      (@cons (bv (Npos (xO (xO (xO xH)))))
                                         (Z_to_bv 
                                            (Npos (xO (xO (xO xH))))
                                            (Z.land
                                               (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                               (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                         (@cons (bv (Npos (xO (xO (xO xH)))))
                                            (Z_to_bv 
                                               (Npos (xO (xO (xO xH))))
                                               (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                            (@cons
                                               (bv (Npos (xO (xO (xO xH)))))
                                               (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                               (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@app
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (@firstn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S (S (S (S (S (S (S O))))))))
                                                 (@insert nat
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (list
                                                 (bv (Npos (xO (xO (xO xH))))))
                                                 (@list_insert
                                                 (bv (Npos (xO (xO (xO xH))))))
                                                 O
                                                 (@BV
                                                 (Npos (xO (xO (xO xH)))) Z0
                                                 I)
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (N.to_nat
                                                 (Npos (xO (xO (xO xH)))))
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (N.to_nat
                                                 (Npos (xO (xO (xO xH)))))
                                                 (@app
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (@firstn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
                                                 (returnStorage locals))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (@bv_unsigned
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 (@BV
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 Z0 I))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 (@BV
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (N.to_nat (Npos (xO xH)))))))))))))))))))))))))))))))))))
                                                 (returnStorage locals)))))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (@BV
                                                 (Npos
                                                 (xO
                                                 (xO (xO (xO (xO (xO xH)))))))
                                                 (Zpos xH) I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (N.to_nat
                                                 (Npos (xO (xO (xO xH)))))))))))))
                                                 (@insert nat
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (list
                                                 (bv (Npos (xO (xO (xO xH))))))
                                                 (@list_insert
                                                 (bv (Npos (xO (xO (xO xH))))))
                                                 O
                                                 (@BV
                                                 (Npos (xO (xO (xO xH)))) Z0
                                                 I)
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (N.to_nat
                                                 (Npos (xO (xO (xO xH)))))
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (N.to_nat
                                                 (Npos (xO (xO (xO xH)))))
                                                 (@app
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (@firstn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
                                                 (returnStorage locals))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (@bv_unsigned
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 (@BV
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 Z0 I))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@cons
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (Z_to_bv
                                                 (Npos (xO (xO (xO xH))))
                                                 (Z.land
                                                 (Z.shiftr
                                                 (@bv_unsigned
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 (@BV
                                                 (Npos (xO (xO (xO (xO xH)))))
                                                 Z0 I))
                                                 (Zpos (xO (xO (xO xH)))))
                                                 (Z.ones
                                                 (Zpos (xO (xO (xO xH)))))))
                                                 (@skipn
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S
                                                 (S (N.to_nat (Npos (xO xH)))))))))))))))))))))))))))))))))))
                                                 (returnStorage locals)))))))))))))))))))))))))))))))))).

Definition decodeItemEmptyStringOutputFacts
 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
 (inputPrefix : byte) (rest : list byte) : Prop :=
 decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
 length (returnStorage locals) = 40%nat /\
 decodeItemInputHead args inputPrefix rest /\
 bv_unsigned inputPrefix = 128 /\
 returnStorage locals = decodeItemBeforeStorage args /\
 decodeItemAcceptedFacts args false 1 0.

Lemma decodeItemEmptyStringUpdatedMeaning args locals inputPrefix rest :
 decodeItemEmptyStringOutputFacts args locals inputPrefix rest ->
 DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals).
Proof.
intros (Hdomain & HstorageLength & Hinput & Hprefix & HstorageBefore & Haccepted).
destruct Haccepted as [Hcandidate Hsail].
unfold decodeItemEmptyStringUpdatedImage.
lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (returnStorage locals) (bv_to_little_endian 8 8 (bv_unsigned (BV 64 1))) (bv_to_little_endian 8 8 (bv_unsigned (BV 64 0))) (bv_to_little_endian 8 8 (bv_unsigned (BV 64 1))) false) end.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (N.to_nat 2%N).
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (N.to_nat 8%N).
1: generalize HstorageLength; generalize (returnStorage locals); intros before Hlength; clear -before Hlength.
1: do 40 (destruct before as [|? before]; [discriminate |]); destruct before; last (cbn in Hlength; lia).
1: unfold decodeItemOkBytes, bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); rewrite !bv_unsigned_BV.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (2^8)%Z.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (1 / 256)%Z.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (0 / 256)%Z.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (1 mod 256)%Z.
1: ZesuSsz.Automation.Hooks.zesu_stack_reduce_closed (0 mod 256)%Z.
1: cbn [app].
1: cbn [take drop firstn skipn insert list_insert app].
1: assert (Hzero : (0%bv : bv 8) = Z_to_bv 8 0) by (apply (proj2 (bv_eq 8 _ _)); reflexivity).
1: rewrite Hzero; reflexivity.
rewrite HcanonicalImage HstorageBefore.
assert (HbeforeLength : length (decodeItemBeforeStorage args) = 40%nat) by (rewrite <- HstorageBefore; exact HstorageLength).
eapply (DecodeItemReturnExitPure.returnExitEmptyString args inputPrefix rest).
all: try (first [exact Hinput | exact (proj2 Hdomain) | exact Hprefix | exact HbeforeLength | exact Hcandidate | exact Hsail | rewrite length_bv_to_little_endian; lia]).
all: lazymatch goal with |- ?lhs = ?rhs => ZesuSsz.Automation.Hooks.zesu_stack_closed_term lhs; ZesuSsz.Automation.Hooks.zesu_stack_closed_term rhs; vm_compute; reflexivity end.
Qed.

#[export] Instance decodeItemEmptyStringOutputDerivedFacts args locals inputPrefix rest :
 ZesuDerivedFacts (decodeItemEmptyStringOutputFacts args locals inputPrefix rest)
  (DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals)).
Proof. exact (decodeItemEmptyStringUpdatedMeaning args locals inputPrefix rest). Qed.

Lemma decodeItemEmptyStringOutputRegistration args locals inputPrefix rest :
 ZesuDerivedFacts (decodeItemEmptyStringOutputFacts args locals inputPrefix rest)
  (DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals)).
Proof. exact (decodeItemEmptyStringOutputDerivedFacts args locals inputPrefix rest). Qed.

Print Assumptions decodeItemEmptyStringUpdatedMeaning.
Print Assumptions decodeItemEmptyStringOutputDerivedFacts.
Print Assumptions decodeItemEmptyStringOutputRegistration.
