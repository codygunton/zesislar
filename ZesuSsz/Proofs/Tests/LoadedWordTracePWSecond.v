Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.V2Steps.
Require Import ZesuSsz.Automation.Switches.LoadedWordTrace.

Lemma loaded_word_trace_pw_second_exact `{!islaG Sigma} `{!threadG}
    (entrySp frameSp vmem0 : bv 64) (values : list (bv 64)) (tail : spec) :
  take 69 values !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned frameSp + 1032)) `div` 8) = Some vmem0 ->
  (True%I : iProp Sigma) ⊢
  (∃ x : spec *ₗ (),
    ⌜scons_snap (SWriteMem (BV 64 (604086456 + 16)) (BV 8 8))
       (λ snapshot : seq_snapshot,
          read_mem_list (snap_mem snapshot) (bv_unsigned (entrySp - (2000 + 16))) 8 =
          Some
            [Z_to_bv 8 (bv_unsigned vmem0 `mod` 256); Z_to_bv 8 ((bv_unsigned vmem0 `div` 256) `mod` 256); Z_to_bv 8 (((bv_unsigned vmem0 `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((bv_unsigned vmem0 `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((bv_unsigned vmem0 `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((((bv_unsigned vmem0 `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 (((((((bv_unsigned vmem0 `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((((((bv_unsigned vmem0 `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) x.1ₗ
     ⊆ scons_snap (SWriteMem (BV 64 (604086456 + 16)) (BV 8 8))
         (λ snapshot : seq_snapshot,
            read_mem_list (snap_mem snapshot) (bv_unsigned (entrySp - (2000 + 16))) 8 =
            Some
              [Z_to_bv 8
                 (bv_unsigned
                    (default 0%bv (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                  `mod` 256);
               Z_to_bv 8
                 ((bv_unsigned
                     (default 0%bv (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                   `div` 256) `mod` 256);
               Z_to_bv 8
                 (((bv_unsigned
                      (default 0%bv
                         (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                    `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((bv_unsigned
                       (default 0%bv
                          (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                     `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 (((((bv_unsigned
                        (default 0%bv
                           (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                      `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((((bv_unsigned
                         (default 0%bv
                            (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                       `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 (((((((bv_unsigned
                          (default 0%bv
                             (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                        `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((((((bv_unsigned
                           (default 0%bv
                              (take 69 (values) !! Z.to_nat ((bv_unsigned (frameSp + 1144) - (bv_unsigned (frameSp) + 1032)) `div` 8)))
                         `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) tail⌝ ∗ True)%I.
Proof.
  intros Hlookup.
  iStartProof.
  iIntros "_".
  Time zesu_rule_set_v2_steps.
  iExists (tail, tt)ₗ.
  iSplit; last done.
  iPureIntro; spec_solver.
Qed.
Print Assumptions loaded_word_trace_pw_second_exact.
