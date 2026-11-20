Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A store whose pointer is a closed offset on an integer root under
   `Z_to_bv`, into an uninitialised region on the same root: the address is
   the integer `z - 8` and Lithium's own lookup splits the region. *)
Lemma store_integer_root `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  repeat liStep.
Qed.

(* The stack pointer register holds a word on another root: the step fires. *)
Lemma store_integer_root_other_stack `{!islaG Sigma} `{!threadG} (z sp : Z) :
  4096 <= z < 4294967296 ->
  "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 sp) -∗
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hsp Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  repeat liStep.
Qed.

(* The root is the stack pointer's root: frame accesses belong to the
   stack-address steps, the step refuses. *)
Lemma store_integer_root_refuses_stack `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  "x2" ↦ᵣ RVal_Bits (bv_add (Z_to_bv 64 z) (BV 64 18446744073709551520)) -∗
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hsp Hregion".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  idtac "STACK_ROOT_REFUSAL_EXECUTED".
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKUninit (z - 16) 16). cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

(* No region or cell on the root owns the address: the step refuses. *)
Lemma store_integer_root_refuses_outside `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  (z - 32) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hregion".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  idtac "OUTSIDE_REFUSAL_EXECUTED".
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKUninit (z - 32) 16). cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

(* A pointer chain on a word root (a record field) owned by a region on that
   root spelled through `bv_unsigned (r + c)`: off the stack pointer's root the
   resources first read `bv_unsigned r + s`, then the address takes the
   owner's spelling and Lithium's lookup splits the region. *)
Lemma store_word_root `{!islaG Sigma} `{!threadG} (rp : bv 64) :
  2684354560 <= bv_unsigned rp -> bv_unsigned rp + 80 <= 3221225472 ->
  bv_unsigned (bv_add rp (BV 64 64)) ↦ₘ (BV 64 0) -∗
  (bv_unsigned (bv_add rp (BV 64 64)) + 8)
    ↦ₘ? (bv_unsigned rp + 80 - (bv_unsigned (bv_add rp (BV 64 64)) + 8)) -∗
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add rp (BV 64 72))))
    (fun _ => (bv_unsigned rp + 64) ↦ₘ (BV 64 0))%I.
Proof.
  intros H1 H2. iIntros "Hcell Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  iFrame.
Qed.

(* On the stack pointer's root the resources keep their spelling (the saved
   cell below is asked for as written); the address takes the spelling of
   the integer-spelled frame region. *)
Lemma store_word_root_stack `{!islaG Sigma} `{!threadG} (sp : bv 64) (v : bv 64) :
  2684355072 <= bv_unsigned sp -> bv_unsigned sp < 3221225472 ->
  "x2" ↦ᵣ RVal_Bits (bv_add sp (BV 64 18446744073709551216)) -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 320)) ↦ₘ v -∗
  (bv_unsigned sp - 400 + 48) ↦ₘ? 16 -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216))
      (BV 64 400)) (BV 64 18446744073709551272))))
    (fun mk => match mk with
      | MKUninit a n => ⌜(a = bv_unsigned sp - 400 + 48)%Z⌝ ∗
          bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 320)) ↦ₘ v
      | _ => False end)%I.
Proof.
  intros H1 H2. iIntros "Hsp Hsaved Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  iFrame. done.
Qed.

(* A resource at exactly the address: Lithium's own lookup matches it, the
   step refuses. *)
Lemma store_word_root_refuses_owned `{!islaG Sigma} `{!threadG} (rp : bv 64) (v : bv 64) :
  2684354560 <= bv_unsigned rp -> bv_unsigned rp + 80 <= 3221225472 ->
  bv_unsigned (bv_add rp (BV 64 72)) ↦ₘ v -∗
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add rp (BV 64 72)))) (fun _ => True)%I.
Proof.
  intros H1 H2. iIntros "Hcell".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_lookup_word_root).
  idtac "OWNED_REFUSAL_EXECUTED".
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKMapsTo 64 v). cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

(* No resource on the root holds the address: the step refuses. *)
Lemma store_word_root_refuses_outside `{!islaG Sigma} `{!threadG} (rp : bv 64) :
  2684354560 <= bv_unsigned rp -> bv_unsigned rp + 80 <= 3221225472 ->
  (bv_unsigned rp + 8) ↦ₘ? 8 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add rp (BV 64 72)))) (fun _ => True)%I.
Proof.
  intros H1 H2. iIntros "Hregion".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  idtac "WORD_OUTSIDE_REFUSAL_EXECUTED".
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKUninit (bv_unsigned rp + 8) 8). cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

(* Guard: an access inside a byte array on the root is Lithium's array lookup
   (it reads the array's elements); the step refuses that owner. *)
Lemma store_word_root_refuses_array `{!islaG Sigma} `{!threadG} (rp : bv 64) (l : list (bv 8)) :
  2684354560 <= bv_unsigned rp -> bv_unsigned rp + 80 <= 3221225472 ->
  length l = 16%nat ->
  (bv_unsigned rp + 8) ↦ₘ∗ l -∗
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add rp (BV 64 16)))) (fun _ => True)%I.
Proof.
  intros H1 H2 Hl. iIntros "Harray".
  assert_fails (idtac; ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_lookup_word_root).
  idtac "WORD_ARRAY_REFUSAL_EXECUTED".
  rewrite /find_in_context /FindMemMapsTo.
  iExists (MKArray 8 (bv_unsigned rp + 8) l). cbn [fic_Prop mem_mapsto_kind_prop]. iFrame.
Qed.

(* Same root with a byte array beside the owner: the access inside the
   region is still taken (the array is skipped, not the step). *)
Lemma store_word_root_beside_array `{!islaG Sigma} `{!threadG} (rp : bv 64) (l : list (bv 8)) :
  2684354560 <= bv_unsigned rp -> bv_unsigned rp + 80 <= 3221225472 ->
  length l = 16%nat ->
  (bv_unsigned rp + 8) ↦ₘ∗ l -∗
  (bv_unsigned rp + 64) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (bv_add rp (BV 64 72))))
    (fun _ => (bv_unsigned rp + 8) ↦ₘ∗ l)%I.
Proof.
  intros H1 H2 Hl. iIntros "Harray Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_lookup_word_root.
  iFrame.
Qed.

Print Assumptions store_integer_root.
Print Assumptions store_integer_root_other_stack.
Print Assumptions store_integer_root_refuses_stack.
Print Assumptions store_integer_root_refuses_outside.
Print Assumptions store_word_root.
Print Assumptions store_word_root_stack.
Print Assumptions store_word_root_refuses_owned.
Print Assumptions store_word_root_refuses_outside.
Print Assumptions store_word_root_refuses_array.
Print Assumptions store_word_root_beside_array.
