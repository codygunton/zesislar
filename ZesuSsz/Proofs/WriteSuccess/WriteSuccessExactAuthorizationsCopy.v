Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Calls.
Import FramedContinuations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessMemcpyWholePublic.
From IslaTraces.write_success_75 Require Import instrs.
Local Remove Hints IslaTraces.write_success_75.a155a0_spec.a155a0_spec_inst : typeclass_instances.

Definition authorizationCopyFrame `{!islaG Sigma} `{!threadG}
    (sp src : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x9" ↦ᵣ RVal_Bits src ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCopyFrame) := I.

Definition authorizationCopyPost `{!islaG Sigma} `{!threadG}
    (sp src : bv 64) (base : Z) (start : nat) (bytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (∃ final13 final14 : bv 64,
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x155a4) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗ "x11" ↦ᵣ RVal_Bits src ∗
   "x12" ↦ᵣ RVal_Bits (BV 64 144) ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
   "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits (BV 64 144) ∗
   base ↦ₘ∗ bytes ∗ bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ take 144 (drop start bytes) ∗
   authorizationCopyFrame sp src P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCopyPost) := I.

Definition authorizationCopyEntry `{!islaG Sigma} `{!threadG}
    (sp src oldra : bv 64) (base : Z) (start : nat) (bytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x9" ↦ᵣ RVal_Bits src ∗ "x1" ↦ᵣ RVal_Bits oldra ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   ⌜bv_unsigned src = (base + Z.of_nat start)%Z⌝ ∗
   ⌜(start + 144 <= length bytes)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗ ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
   instr_pre 0x155a4 (authorizationCopyPost sp src base start bytes P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCopyEntry) := I.

Lemma authorization_copy_correct `{!islaG Sigma} `{!threadG}
    sp src oldra base start bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_75.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15590 (authorizationCopyEntry sp src oldra base start bytes P).
Proof.
  iStartProof. iIntros "#Hcaller #Hmemcpy".
  iPoseProof (memcpy_whole_public_correct base start bytes src
    (sp + BV 64 1744)%bv (BV 64 144) (BV 64 0x155a4)
    (authorizationCopyFrame sp src P) with "Hmemcpy") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_75.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & _)".
  zesu_run. Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
Qed.
Print Assumptions authorization_copy_correct.
