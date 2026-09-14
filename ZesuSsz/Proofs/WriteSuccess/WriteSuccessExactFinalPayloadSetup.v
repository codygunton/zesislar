Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessByteLists.
Require Import ZesuSsz.Contracts.IslarisMachine.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactFinalPayloadCall.
Open Scope Z_scope.
Definition writeSuccessExactFinalPayloadSetupEntry `{!islaG Sigma} `{!threadG}
    (savedReturn : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp + 88 < machineRamEnd defaultMap⌝ ∗
    instr_pre 0x159d4 (writeSuccessExactPost159d4PayloadCallEntrySpec savedReturn
      ((bv_unsigned sp + 88) ↦ₘ count ∗ Q)) ∗
    writeSuccessExactFinalPayloadCallEntryFrame sp pointer count items tail savedReturn
      ((bv_unsigned sp + 88) ↦ₘ count ∗ Q))%I.
Global Instance : LithiumUnfold (@writeSuccessExactFinalPayloadSetupEntry) := I.
Lemma write_success_exact_final_payload_setup_correct `{!islaG Sigma} `{!threadG}
    (savedReturn : bv 64) (Q : iProp Sigma) :
  instr_lookup_resources lookup -∗ instr_body 0x159c8 (writeSuccessExactFinalPayloadSetupEntry savedReturn Q).
Proof.
  iStartProof; simpl;
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (∃ _ : unit, _)%I => idtac end).
  liShow; zesu_instantiate_tuple; liFromSyntaxGoal.
  zesu_run.
  iExists (tail, items, tt)ₗ. cbn.
  zesu_run.
  iExists (s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,s0,b17,b16,b15,b14,b13,b12,tt)ₗ. cbn.
  have HcountAddress : bv_unsigned (sp + BV 64 88)%bv = bv_unsigned sp + 88 by (clear -H2; bv_solve).
  iEval (rewrite ?HcountAddress) in "∗".
  rewrite /WriteSuccessEpilogueBlock.writeSuccessEpilogueSavedSlots.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions write_success_exact_final_payload_setup_correct.
