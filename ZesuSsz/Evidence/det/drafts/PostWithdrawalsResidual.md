# Post-withdrawals draft residual

Module: `WriteSuccessExactPostWithdrawalsSegment.v`.
Lemma: `write_success_exact_post_withdrawals_segment`.
Source: frozen main-track draft with its segment proof replaced by `zesu_block.`.
Rules: `ZesuSsz.Automation.Sets.v2` and `InterfacesCoverage`.
Hand proof lines: 0 after `Proof.`.

`make probe` result: residual, class C2, one goal, 34.6 seconds, 1404 MiB.
Full goal: `_build/agents/seg-pw/residuals/293cb048e8e5e8d0bbbce46364b9418b87302f6fd739f49c5ec318325a3b0a67.txt`.
Residual conclusion:

```coq
∃ y : bv 64 *ₗ (),
  (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗
  ⌜bv_unsigned (writeSuccessFrameSp witness) `mod` 8 = 0⌝ ∗
  ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) + 1136 < 0 + 1073741824⌝ ∗
  instr_pre (87784 + 4)
    (reg_col zesu_ram_sys_regs ∗
     "x10" ↦ᵣ RVal_Bits y.1ₗ ∗
     "x2" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness) ∗
     (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗ True)
```

Direct compile result: fail, 23.3 seconds, 1409 MiB, line 168.
The error is `Attempt to save an incomplete proof`.
The draft is frozen under rule 21.
