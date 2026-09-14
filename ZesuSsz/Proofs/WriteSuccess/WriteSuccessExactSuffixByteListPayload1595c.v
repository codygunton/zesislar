Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactPrefixCalls
  WriteSuccessByteLists WriteSuccessExactByteLists WriteSuccessExactByteListsSpec
  WriteSuccessObservation WriteSuccessOutputSemantic.
Import ListNotations.
Open Scope Z_scope.
Definition exactSuffixByteListOtherShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
  ["x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18";
   "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].
Definition exactSuffixByteListReturn `{!islaG Sigma} `{!threadG}
    (returnPc : Z) (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (items : list ByteListItem) (tail : spec)
      (saved : list valu),
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun value => valu_has_shape value (BitsShape 64)) saved⌝ ∗
    zesu_c_call_ret 80 saved (Z_to_bv 64 returnPc) sp (fun _ =>
      byteListItemResources (bv_unsigned pointer) items ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True) ∗ Q)%I.
Global Instance : LithiumUnfold (@exactSuffixByteListReturn) := I.
Definition exactSuffix1595cEntry `{!islaG Sigma} `{!threadG}
    (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col exactSuffixByteListOtherShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15958) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits count ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (Z.of_nat (length items))))
      (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail)) ∗
    ⌜bv_unsigned count = Z.of_nat (length items)⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < machineRamEnd defaultMap⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 80 /\
      bv_unsigned sp < machineRamEnd defaultMap⌝ ∗ Q)%I.
Global Instance : LithiumUnfold (@exactSuffix1595cEntry) := I.
Lemma exact_suffix_1595c_payload `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15960 (exactSuffixByteListReturn 0x15960 Q) -∗
  instr_body 0x1595c (exactSuffix1595cEntry Q).
Proof.
  iIntros "#Hnative #Hnext".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#Hcopy & #Houtput & #Hint & #Hbytes)".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & HoutCode & HcopyCode & HboolCode & HoptCode & Hlists & HbytesCode & HintCode & Hu256 & Hu128)".
  iAssert (□ instr_pre 0x15c10 encoderByteListsExactCallSpec)%I with "[]" as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (byte_lists_exact_correct with "Hlists Hint Hbytes"). }
  iStartProof; simpl.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (∃ _ : li_prod spec (li_prod (list ByteListItem) unit), _)%I => idtac
    end).
  iExists (tail, items, tt)ₗ.
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (instr_pre _ _) => idtac
    end).
  liShow.
  iApply (instr_pre_wand 0x15960 (bv_unsigned LET) true true with "Hnext");
    [done | subst LET; bv_solve |].
  iIntros "Hpost".
  rewrite /exactSuffixByteListReturn.
  iExists sp, pointer, items, tail,
    [RVal_Bits b6; RVal_Bits b7; RVal_Bits b8; RVal_Bits b9;
     RVal_Bits b10; RVal_Bits b11; RVal_Bits b12; RVal_Bits b13;
     RVal_Bits b14; RVal_Bits b15; RVal_Bits b16; RVal_Bits b17].
  iSplit; [done |]. iSplit; [iPureIntro; repeat constructor |].
  iFrame "Hpost". iFrame.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions exact_suffix_1595c_payload.
