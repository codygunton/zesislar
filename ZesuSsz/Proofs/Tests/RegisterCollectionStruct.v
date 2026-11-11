Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Strings.String.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.
Import ListNotations.

(* At a call the caller's system-register collection meets the callee's. The
   struct entry is the same on both sides; one exact value is widened to its
   width. The library condition has no struct case and becomes False. *)
Lemma register_collection_same_struct `{!islaG Sigma} `{!threadG} (x : bv 64) (R : iProp Sigma) :
  R -∗
  reg_col [(KindReg "misa", ExactShape (RVal_Bits (BV 64 0x8000000000001100)));
           (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
           (KindReg "mtvec", ExactShape (RVal_Bits x))] -∗
  (reg_col [(KindReg "misa", ExactShape (RVal_Bits (BV 64 0x8000000000001100)));
            (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
            (KindReg "mtvec", BitsShape 64)] ∗ R).
Proof. iIntros "HR Hregs". zesu_block2. Qed.
