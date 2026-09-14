Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_09 Require Import instrs.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessPrologueSpec WriteSuccessCalls.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactNativeLoadSpec.
Definition exactNativeCopyPost `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) (object : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  exactNativeLoadState (sp - BV 64 2000)%bv decoded object
    (((bv_unsigned (sp - BV 64 2000)%bv) + 312) ↦ₘ∗ take 720 object ∗
     ((bv_unsigned (sp - BV 64 2000)%bv) + 1032) ↦ₘ? 864 ∗
     writeSuccessSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P).
Global Instance : LithiumUnfold (@exactNativeCopyPost) := I.
Lemma exact_native_copy_correct `{!islaG Sigma} `{!threadG}
    sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 object tail (P : iProp Sigma) :
  bv_unsigned decoded = (bv_unsigned sp + 32)%Z ->
  bv_unsigned sp `mod` 16 = 0 ->
  (mapRamBase defaultMap + 0x880 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + 0x7d0 < machineRamEnd defaultMap)%Z ->
  ([∗ list] instruction ∈ IslaTraces.write_success_09.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  instr_body 0x14d80 (exactNativeCopyPost sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 object tail P) -∗
  instr_body 0x14d7c
    (write_success_prologue_exit sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      (((bv_unsigned sp - 2000) ↦ₘ? 1896 ∗
       bv_unsigned decoded ↦ₘ∗ object ∗
       mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗
       ⌜length object = 848%nat⌝ ∗ ⌜mapRamBase defaultMap <= bv_unsigned decoded⌝ ∗
       ⌜bv_unsigned decoded + 848 < machineRamEnd defaultMap⌝ ∗ True)%I)).
Proof.
  intros Hdecoded Halign Hmin Hmax.
  iStartProof; simpl;
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (∃ _ : unit, _)%I => idtac end).
  all: liShow; zesu_instantiate_tuple; liFromSyntaxGoal.
  all: zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ zesuMemcpyCallSpec => idtac end).
  all: iEval (unfold zesuMemcpyCallSpec, zesu_c_call).
  all: zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (@bi_exist _ (list (bv 8)) _) => idtac end).
  all: zesu_pack object.
  all: zesu_run.
  all: zesu_finish.
Unshelve. all: zesu_finish.
Qed.
Print Assumptions exact_native_copy_correct.
