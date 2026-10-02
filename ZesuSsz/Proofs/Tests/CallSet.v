Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import ZesuSsz.Automation.Sets.call.

Section tests.
Context `{!islaG Sigma} `{!threadG}.

(* The 0x15754 block calls writeOutput through this auipc/jalr target. *)
Lemma call_set_concrete_instr_pre (P : iProp Sigma) :
  instr_pre 0x10190 P -∗
  find_in_context
    (FindInstrKind
      (bv_unsigned (bv_or
        (bv_and ((BV 64 0x158cc + BV 64 0xffffffffffffb000 +
          BV 64 0xfffffffffffff8c4)%bv) (BV 64 0xfffffffffffffffe))
        (BV 64 0))) true)
    (fun kind => match kind with IKPre _ _ => True | IKInstr _ => False end).
Proof.
  iIntros "Hpre".
  repeat liAStep.
Qed.

Lemma call_set_symbolic_address_guard (address : Z) (bits : positive) : True.
Proof using All.
  assert (FindInContext (FindInstrKind (address + 0) true) FICSyntactic).
  { Fail zesu_reduce_instr_pre_address. typeclasses eauto. }
  assert (FindInContext (FindInstrKind (Zpos bits + 0) true) FICSyntactic).
  { Fail zesu_reduce_instr_pre_address. typeclasses eauto. }
  assert (FindInContext (FindInstrKind (Zneg bits + 0) true) FICSyntactic).
  { Fail zesu_reduce_instr_pre_address. typeclasses eauto. }
  exact I.
Qed.

Lemma call_set_return_bundle_wp (value sp ret : bv 64) (tail : spec) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ spec_trace tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    ((encoderBooleanClosedReturn value sp ret tail -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iMatchHyp ltac:(fun H body => lazymatch body with spec_trace _ => iRename H into "Htrace" end).
  iIntros "HPC".
  iApply ("Hcontinue" with "Hsys Htrace HPC").
Qed.

Lemma call_set_zesu_call_ret_wp (stack_size : Z) (regs : list valu)
    (ret sp : bv 64) (Q : list (bv 64) -> iProp Sigma) (t : isla_trace) :
  ⊢ ((reg_col zesu_ram_sys_regs -∗ "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) -∗
    ((zesu_call_ret stack_size regs ret sp Q -∗
      "PC" ↦ᵣ RVal_Bits ret -∗ WPasm t) ∗ True))%I.
Proof.
  iIntros "Hcontinue".
  zesu_rule_set_v2_steps.
  iMatchHyp ltac:(fun H body => lazymatch body with reg_col zesu_ram_sys_regs => iRename H into "Hsys" end).
  iIntros "HPC".
  iApply ("Hcontinue" with "Hsys HPC").
Qed.

End tests.
Print Assumptions call_set_concrete_instr_pre.
Print Assumptions call_set_symbolic_address_guard.
Print Assumptions call_set_return_bundle_wp.
Print Assumptions call_set_zesu_call_ret_wp.
