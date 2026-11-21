(* Step 2.4 M1, amendment 14: the walk obligations of decodeParentHeader's
   success path, fields 0 to 8 (the outer item, then the nine skipped
   fields). Owner: compliance proof (hand-written). Each generated
   declaration `fp_edge<call block>_<return site>_Walk`
   (Generated/DecodeParentHeader/FP301/EdgeObligations.v) states: the call
   block's history and visible facts imply the walk fact of the call's
   window (Contracts/ParentHeaderWalkFact.v), which the return site's
   history then holds. Every proof is `ph_edge_walk`
   (ParentHeaderWalkTactic.v). *)
Require Import ZesuSsz.Compliance.ParentHeaderWalkTactic.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.EdgeObligations.

(* field 0: the outer item's payload *)
Lemma fp_edge0068_0080_Walk_holds : fp_edge0068_0080_Walk.
Proof. ph_edge_walk. Qed.

(* fields 1 to 8: after a skipped field *)
Lemma fp_edge00ec_0108_Walk_holds : fp_edge00ec_0108_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0118_0134_Walk_holds : fp_edge0118_0134_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0144_0160_Walk_holds : fp_edge0144_0160_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0170_018c_Walk_holds : fp_edge0170_018c_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge019c_01b8_Walk_holds : fp_edge019c_01b8_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge01c8_01e4_Walk_holds : fp_edge01c8_01e4_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge01f4_0210_Walk_holds : fp_edge01f4_0210_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0220_023c_Walk_holds : fp_edge0220_023c_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0244_0264_Walk_holds : fp_edge0244_0264_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge02e4_0300_Walk_holds : fp_edge02e4_0300_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0348_0368_Walk_holds : fp_edge0348_0368_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge03e8_0400_Walk_holds : fp_edge03e8_0400_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge041c_0438_Walk_holds : fp_edge041c_0438_Walk.
Proof. ph_edge_walk. Qed.
Lemma fp_edge0448_0464_Walk_holds : fp_edge0448_0464_Walk.
Proof. ph_edge_walk. Qed.
