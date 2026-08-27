From isla Require Import opsem.

Definition a14ccc : isla_trace :=
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "misa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DefineConst 4%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 5%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x24005000%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "x10" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 4%Z)) Mk_annot :t:
  tnil
.
