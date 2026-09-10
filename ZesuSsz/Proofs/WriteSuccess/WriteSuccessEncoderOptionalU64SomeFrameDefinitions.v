Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.

Import ListNotations.

Definition optionalU64SomePublicFrame `{!islaG Sigma} `{!threadG}
    (r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64) : iProp Sigma :=
  (reg_col
     [(KindReg "x7", BitsShape 64); (KindReg "x28", BitsShape 64);
      (KindReg "x29", BitsShape 64); (KindReg "x30", BitsShape 64);
      (KindReg "x31", BitsShape 64)] ∗
   reg_col
     [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
      (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
      (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64)] ∗
   reg_col
     [(KindReg "x9", ExactShape (RVal_Bits r9));
      (KindReg "x18", ExactShape (RVal_Bits r18));
      (KindReg "x19", ExactShape (RVal_Bits r19));
      (KindReg "x20", ExactShape (RVal_Bits r20));
      (KindReg "x21", ExactShape (RVal_Bits r21));
      (KindReg "x22", ExactShape (RVal_Bits r22));
      (KindReg "x23", ExactShape (RVal_Bits r23));
      (KindReg "x24", ExactShape (RVal_Bits r24));
      (KindReg "x25", ExactShape (RVal_Bits r25));
      (KindReg "x26", ExactShape (RVal_Bits r26));
      (KindReg "x27", ExactShape (RVal_Bits r27))])%I.

Global Instance : LithiumUnfold (@optionalU64SomePublicFrame) := I.
