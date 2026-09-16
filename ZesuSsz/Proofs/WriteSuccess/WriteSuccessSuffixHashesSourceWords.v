Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.

Definition writeSuccessHashesSourceRest : list (reg_kind * valu_shape) :=
  [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
   (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
   (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
   (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
   (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
   (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64);
   (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64);
   (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64);
   (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64);
   (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64);
   (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
   (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)].

Lemma write_success_suffix_hashes_source_words
    `{!islaG Sigma} `{!threadG} (sp : bv 64) :
  reg_col
      writeSuccessHashesSourceRest -∗
  "x1" ↦ᵣ RVal_Bits (BV 64 0x15750) -∗
  "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) -∗
  "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv -∗
  "x11" ↦ᵣ RVal_Bits (BV 64 8) -∗
  reg_col writeSuccessHashesOtherRegShapes.
Proof.
  iIntros "Hrest H1 H5 H10 H11".
  rewrite /writeSuccessHashesOtherRegShapes /writeSuccessHashesOtherRegisters.
  rewrite (reg_col_lookup
    [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64);
     (KindReg "x4", BitsShape 64); (KindReg "x5", BitsShape 64);
     (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
     (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
     (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64);
     (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64);
     (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64);
     (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64);
     (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)]
    0%nat (KindReg "x1", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (BV 64 0x15750)). iFrame "H1".
  iSplit; [iPureIntro; cbn; constructor |].
  rewrite (reg_col_lookup
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64);
     (KindReg "x7", BitsShape 64); (KindReg "x10", BitsShape 64);
     (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64);
     (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64);
     (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64);
     (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64);
     (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64);
     (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64);
     (KindReg "x27", BitsShape 64); (KindReg "x28", BitsShape 64);
     (KindReg "x29", BitsShape 64); (KindReg "x30", BitsShape 64);
     (KindReg "x31", BitsShape 64)]
    2%nat (KindReg "x5", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (BV 64 (mapIoContextAddress defaultMap))). iFrame "H5".
  iSplit; [iPureIntro; cbn; constructor |].
  rewrite (reg_col_lookup
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
     (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
     (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64);
     (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64);
     (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64);
     (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64);
     (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)]
    4%nat (KindReg "x10", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (sp - BV 64 16)%bv). iFrame "H10".
  iSplit; [iPureIntro; cbn; constructor |].
  rewrite (reg_col_lookup
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64);
     (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64);
     (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64);
     (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64);
     (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64);
     (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64);
     (KindReg "x27", BitsShape 64); (KindReg "x28", BitsShape 64);
     (KindReg "x29", BitsShape 64); (KindReg "x30", BitsShape 64);
     (KindReg "x31", BitsShape 64)]
    4%nat (KindReg "x11", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (BV 64 8)). iFrame "H11 Hrest".
  iPureIntro. cbn. constructor.
Qed.
