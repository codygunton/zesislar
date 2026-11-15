Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation2.All.

Lemma plain_register_selection_array_first `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list byte) (shape : valu_shape)
    (T : reg_mapsto_kind -> iProp Sigma) :
  reg_col [(KindReg "test_reg", shape)] -∗
  address ↦ₘ∗ bytes -∗
  (address ↦ₘ∗ bytes -∗ T (RKCol [(KindReg "test_reg", shape)])) -∗
  find_in_context (FindRegMapsTo "test_reg") T.
Proof.
  iStartProof. iIntros "Hregs Harray HT".
  zesu_register_collection_selection_if_enabled.
  iApply "HT". iExact "Harray".
Qed.

Lemma plain_register_selection_skips_wrong_keys `{!islaG Sigma} `{!threadG}
    (shape field_shape other_shape : valu_shape) :
  reg_col [(KindReg "test_reg", shape)] -∗
  reg_col [(KindField "test_reg" "field", field_shape)] -∗
  reg_col [(KindReg "other_reg", other_shape)] -∗
  find_in_context (FindRegMapsTo "test_reg") (fun _ => True).
Proof.
  iStartProof. iIntros "Hregs Hfield Hother".
  zesu_register_collection_selection_if_enabled.
  done.
Qed.

Lemma plain_register_selection_rejects_field (shape : valu_shape) : True.
Proof.
  Fail let index := zesu_plain_register_collection_index "test_reg"
    [(KindField "test_reg" "field", shape)] in idtac.
  exact I.
Qed.

Lemma plain_register_selection_nonselection_alias `{!islaG Sigma} : True.
Proof.
  pose (Henv := @Envs (iPropI Sigma) Enil Enil 1%positive).
  Fail zesu_register_collection_selection_if_enabled.
  let value := eval unfold Henv in Henv in
  lazymatch value with Envs _ _ _ => idtac end.
  exact I.
Qed.

(* The FP301 entry at 0x800d6ae0 owns the decoder system registers and the
   caller's output storage (`fp_machineAt0180`). *)
Lemma plain_register_selection_captured_6ae0 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (T : reg_mapsto_kind -> iProp Sigma) :
  reg_col (decodeItemSysRegs args) -∗
  decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args -∗
  (decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args -∗
    T (RKCol (decodeItemSysRegs args))) -∗
  find_in_context (FindRegMapsTo "rv_enable_pmp") T.
Proof.
  iStartProof. iIntros "Hregs Harray HT".
  zesu_register_collection_selection_if_enabled.
  iApply "HT". iExact "Harray".
Qed.

Lemma plain_register_selection_medeleg `{!islaG Sigma} `{!threadG} :
  reg_col zesu_sys_regs -∗
  find_in_context (FindRegMapsTo "medeleg") (fun _ => True).
Proof.
  iStartProof. iIntros "Hregs".
  zesu_register_collection_selection_if_enabled. done.
Qed.

Lemma plain_register_selection_mideleg `{!islaG Sigma} `{!threadG} :
  reg_col zesu_sys_regs -∗
  find_in_context (FindRegMapsTo "mideleg") (fun _ => True).
Proof.
  iStartProof. iIntros "Hregs".
  zesu_register_collection_selection_if_enabled. done.
Qed.
