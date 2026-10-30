Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From iris.proofmode Require Import environments.

Lemma plain_register_selection_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRegisterCollectionSelection) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.RegisterCollectionSelection.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.

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

Lemma plain_register_selection_captured_6ae0 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (T : reg_mapsto_kind -> iProp Sigma) :
  reg_col (decodeItemSysRegs args) -∗
  decodeItemOutputPointer args ↦ₘ∗
    (take 32 (returnStorage locals) ++
     bv_to_little_endian 8 8 (bv_unsigned (4 : bv 64)) ++
     drop 40 (returnStorage locals)) -∗
  (decodeItemOutputPointer args ↦ₘ∗
    (take 32 (returnStorage locals) ++
     bv_to_little_endian 8 8 (bv_unsigned (4 : bv 64)) ++
     drop 40 (returnStorage locals)) -∗ T (RKCol (decodeItemSysRegs args))) -∗
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
