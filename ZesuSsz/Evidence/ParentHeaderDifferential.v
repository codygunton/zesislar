From Coq Require Import List String ZArith Bool.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.ProjectionParentHeader ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Contracts.RlpDecodeItem ZesuSsz.Contracts.Candidates.ParentHeaderDomain.

Import ListNotations.
Open Scope Z_scope.

(* ethereum/tests commit c67e485ff8b5be9abc8ad15345ec21aa22e290d9,
   BlockchainTests/ValidBlocks/bcValidBlockTest/SimpleTx.json,
   SHA256 d4e5acbc323640e68dae68162243f7946c32276bb17bc6710d6266590d50e69f.
   Each header is the first RLP item in its block RLP. *)
Definition vectorBytes (values : list Z) : list byte := map (Z_to_bv 8) values.
Definition cancunHeader : list byte := vectorBytes [
    249; 2; 59; 160; 140; 188; 105; 227; 59; 216; 91; 31; 141; 123; 198; 202;
    232; 241; 212; 80; 43; 116; 207; 208; 205; 95; 36; 165; 88; 192; 208; 194;
    87; 198; 157; 170; 160; 29; 204; 77; 232; 222; 199; 93; 122; 171; 133; 181;
    103; 182; 204; 212; 26; 211; 18; 69; 27; 148; 138; 116; 19; 240; 161; 66;
    253; 64; 212; 147; 71; 148; 136; 136; 241; 241; 149; 175; 161; 146; 207; 238;
    134; 6; 152; 88; 76; 3; 15; 76; 157; 177; 160; 195; 141; 136; 18; 25;
    167; 16; 206; 248; 186; 2; 180; 150; 249; 33; 28; 101; 127; 190; 140; 24;
    222; 57; 9; 211; 83; 205; 193; 168; 212; 225; 111; 160; 43; 47; 161; 210;
    225; 59; 221; 100; 83; 148; 144; 111; 210; 115; 126; 250; 31; 143; 94; 0;
    122; 115; 230; 1; 230; 219; 44; 228; 225; 129; 125; 6; 160; 5; 107; 35;
    251; 186; 72; 6; 150; 182; 95; 229; 165; 155; 143; 33; 72; 161; 41; 145;
    3; 196; 245; 125; 248; 57; 35; 58; 242; 207; 76; 162; 210; 185; 1; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    128; 1; 131; 47; 239; 216; 130; 82; 8; 132; 84; 201; 144; 105; 66; 160;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0;
    136; 0; 0; 0; 0; 0; 0; 0; 0; 14; 160; 86; 232; 31; 23; 27;
    204; 85; 166; 255; 131; 69; 230; 146; 192; 248; 110; 91; 72; 224; 27; 153;
    108; 173; 192; 1; 98; 47; 181; 227; 99; 180; 33; 128; 128; 160; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition pragueHeader : list byte := vectorBytes [
    249; 2; 92; 160; 239; 222; 187; 5; 33; 135; 223; 47; 109; 24; 122; 180;
    29; 235; 90; 116; 21; 121; 229; 138; 173; 72; 47; 168; 65; 209; 196; 239;
    157; 131; 196; 42; 160; 29; 204; 77; 232; 222; 199; 93; 122; 171; 133; 181;
    103; 182; 204; 212; 26; 211; 18; 69; 27; 148; 138; 116; 19; 240; 161; 66;
    253; 64; 212; 147; 71; 148; 136; 136; 241; 241; 149; 175; 161; 146; 207; 238;
    134; 6; 152; 88; 76; 3; 15; 76; 157; 177; 160; 251; 96; 123; 132; 219;
    217; 23; 145; 76; 180; 201; 85; 102; 151; 80; 198; 85; 166; 201; 26; 248;
    97; 87; 235; 38; 144; 155; 186; 65; 35; 158; 31; 160; 43; 47; 161; 210;
    225; 59; 221; 100; 83; 148; 144; 111; 210; 115; 126; 250; 31; 143; 94; 0;
    122; 115; 230; 1; 230; 219; 44; 228; 225; 129; 125; 6; 160; 5; 107; 35;
    251; 186; 72; 6; 150; 182; 95; 229; 165; 155; 143; 33; 72; 161; 41; 145;
    3; 196; 245; 125; 248; 57; 35; 58; 242; 207; 76; 162; 210; 185; 1; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    128; 1; 131; 47; 239; 216; 130; 82; 8; 132; 84; 201; 144; 105; 66; 160;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0;
    136; 0; 0; 0; 0; 0; 0; 0; 0; 14; 160; 86; 232; 31; 23; 27;
    204; 85; 166; 255; 131; 69; 230; 146; 192; 248; 110; 91; 72; 224; 27; 153;
    108; 173; 192; 1; 98; 47; 181; 227; 99; 180; 33; 128; 128; 160; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
    0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 160; 227;
    176; 196; 66; 152; 252; 28; 20; 154; 251; 244; 200; 153; 111; 185; 36; 39;
    174; 65; 228; 100; 155; 147; 76; 164; 149; 153; 27; 120; 82; 184; 85].

Definition headerFitsObserved (bytes : list byte) : bool :=
  match bytes with
  | [] => true
  | prefix :: rest =>
      let width := longLengthWidth (bv_unsigned prefix) in
      (width =? 0) ||
      (Z.of_nat (List.length rest) <? width) ||
      (1 + width + bigEndian (firstn (Z.to_nat width) rest) <? word64Modulus)
  end.

Lemma headerFitsObservedCorrect bytes :
  headerFitsObserved bytes = true <-> headerFits bytes.
Proof.
  destruct bytes as [|prefix rest]; simpl; [tauto|].
  repeat rewrite Bool.orb_true_iff.
  repeat rewrite Z.eqb_eq.
  repeat rewrite Z.ltb_lt.
  tauto.
Qed.

Definition candidateFitObserved (bytes : list byte) : bool :=
  headerFitsObserved bytes &&
  match fieldSlices bytes with
  | None => false
  | Some slices => forallb (fun call => headerFitsObserved (snd call)) slices
  end.

Lemma candidateFitObservedCorrect bytes :
  candidateFitObserved bytes = true <-> allContiguousHeadersFit bytes.
Proof.
  unfold candidateFitObserved, allContiguousHeadersFit.
  rewrite Bool.andb_true_iff.
  rewrite headerFitsObservedCorrect.
  split.
  - intros [Hfit Hwalk].
    destruct (fieldSlices bytes) as [slices|] eqn:Hslices; [|discriminate].
    split; [exact Hfit|]. exists slices. split; [reflexivity|].
    rewrite List.forallb_forall in Hwalk.
    apply List.Forall_forall. intros call Hin.
    apply headerFitsObservedCorrect. apply Hwalk. exact Hin.
  - intros [Hfit [slices [Hslices Hfits]]].
    split; [exact Hfit|]. rewrite Hslices.
    rewrite List.forallb_forall. intros call Hin.
    apply headerFitsObservedCorrect.
    apply List.Forall_forall with (x := call) in Hfits; assumption.
Qed.

Definition sailHeaderTag (bytes : list byte) : nat :=
  let n := Z.of_nat (List.length bytes) in
  match sailParentHeaderRun bytes (@Build_StatelessInputSliceFields 0 n 0 n) with
  | Success _ => 0%nat
  | Reject _ => 1%nat
  | UnsupportedOrInternalFailure _ => 2%nat
  end.

Definition rewrapPayload (payload : list byte) : list byte :=
  let n := Z.of_nat (List.length payload) in
  if n <=? 55 then
    Z_to_bv 8 (192 + n) :: payload
  else if n <=? 255 then
    Z_to_bv 8 248 :: Z_to_bv 8 n :: payload
  else
    Z_to_bv 8 249 :: Z_to_bv 8 (n / 256) ::
      Z_to_bv 8 (n mod 256) :: payload.

Definition cancunPayload : list byte := skipn 3 cancunHeader.
Definition fieldBoundaryLengths : list nat :=
  [33%nat; 66%nat; 87%nat; 120%nat; 153%nat; 186%nat; 445%nat; 446%nat; 447%nat; 451%nat;
   454%nat; 459%nat; 460%nat; 493%nat; 502%nat; 503%nat; 536%nat; 537%nat; 538%nat; 571%nat].
Definition boundaryTruncations : list (nat * list byte) :=
  map (fun n => (n, rewrapPayload (firstn n cancunPayload)))
    fieldBoundaryLengths.

(* The selected ELF tests the remaining length before each of the nine
   required skip calls. The branch at 0x800d5d1c guards the first call.
   Later equality branches at 0x800d5dcc through 0x800d5ed4 guard
   the next calls. The 0x800d5f18 required uint64 call has no empty
   guard. This matches the selected Zig source at rlp_decode.zig:120-130. *)
Definition firstBoundaryCalls : option (list Z) :=
  option_map (map fst)
    (fieldSlices (rewrapPayload (firstn 33%nat cancunPayload))).
Definition ninthBoundaryCalls : option (list Z) :=
  option_map (map fst)
    (fieldSlices (rewrapPayload (firstn 447%nat cancunPayload))).
Definition twelfthBoundaryCalls : option (list Z) :=
  option_map (map fst)
    (fieldSlices (rewrapPayload (firstn 459%nat cancunPayload))).

(* Replace a required integer or optional integer field with a wrapped
   eight-byte length. The nested RLP header overflows a 64-bit sum. *)
Definition nestedWrapAt (start finish : nat) : list byte :=
  rewrapPayload
    (firstn start cancunPayload ++
     vectorBytes (191 :: List.repeat 255 8) ++
     skipn finish cancunPayload).
Definition requiredNestedWrap : list byte := nestedWrapAt 447%nat 451%nat.
Definition optionalNestedWrap : list byte := nestedWrapAt 536%nat 537%nat.

Definition headerVectorResults : list (string * nat * bool * bool) :=
  [("Cancun"%string, sailHeaderTag cancunHeader,
      headerFitsObserved cancunHeader, candidateFitObserved cancunHeader);
   ("Prague"%string, sailHeaderTag pragueHeader,
      headerFitsObserved pragueHeader, candidateFitObserved pragueHeader);
   ("required wrap"%string, sailHeaderTag requiredNestedWrap,
      headerFitsObserved requiredNestedWrap,
      candidateFitObserved requiredNestedWrap);
   ("optional wrap"%string, sailHeaderTag optionalNestedWrap,
      headerFitsObserved optionalNestedWrap,
      candidateFitObserved optionalNestedWrap)].

Definition boundaryVectorResults : list (nat * nat * bool * bool) :=
  map (fun item =>
    let '(n, bytes) := item in
    (n, sailHeaderTag bytes,
      headerFitsObserved bytes, candidateFitObserved bytes))
    boundaryTruncations.

Definition expectedHeaderVectorResults : list (string * nat * bool * bool) :=
  [("Cancun"%string, 0%nat, true, true);
   ("Prague"%string, 0%nat, true, true);
   ("required wrap"%string, 1%nat, true, false);
   ("optional wrap"%string, 1%nat, true, false)].
Definition expectedBoundaryVectorResults : list (nat * nat * bool * bool) :=
  map (fun n => (n, 0%nat, true, true)) fieldBoundaryLengths.

Example headerVectorResultsPinned :
  headerVectorResults = expectedHeaderVectorResults.
Proof. vm_compute. reflexivity. Qed.

Example boundaryVectorResultsPinned :
  boundaryVectorResults = expectedBoundaryVectorResults.
Proof. vm_compute. reflexivity. Qed.

Example firstBoundaryGuardPinned :
  firstBoundaryCalls = Some [0x800d5cf4; 0x800d5d34].
Proof. vm_compute. reflexivity. Qed.

Example ninthBoundaryUint64Pinned :
  ninthBoundaryCalls = Some
    [0x800d5cf4; 0x800d5d34; 0x800d5dbc; 0x800d5de8;
     0x800d5e14; 0x800d5e40; 0x800d5e6c; 0x800d5e98;
     0x800d5ec4; 0x800d5ef0; 0x800d5f18].
Proof. vm_compute. reflexivity. Qed.

Example twelfthBoundaryOptionalStopPinned :
  twelfthBoundaryCalls = Some
    [0x800d5cf4; 0x800d5d34; 0x800d5dbc; 0x800d5de8;
     0x800d5e14; 0x800d5e40; 0x800d5e6c; 0x800d5e98;
     0x800d5ec4; 0x800d5ef0; 0x800d5f18; 0x800d5fb4;
     0x800d601c].
Proof. vm_compute. reflexivity. Qed.
