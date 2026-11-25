Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Automation2.All.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

(* Accesses whose address equals a place of an owned region only through
   register equations (Automation2/HeapAddress.v, Hooks.zesu_heap_write). *)
Section tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* The spare region of an array list of 40-byte items, stored to through
     pointer + 32 * length + 8 * length (txAccessList +0x460). *)
  Lemma heap_write_spare (p len cap : Z) (x11 x12 x16 : bv 64) :
    bv_unsigned x11 = p -> bv_unsigned x12 = 8 * len -> bv_unsigned x16 = 32 * len ->
    len < cap ->
    (p + len * 40) ↦ₘ? ((cap - len) * 40) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + (x16 + x12))%bv + 0))
      (fun mk : mem_mapsto_kind => match mk with
        | MKUninit start count => ⌜start = (p + len * 40)%Z⌝ ∗ (start ↦ₘ? count -∗ True)
        | _ => False end)%I.
  Proof.
    intros. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_heap_write.
    iSplit; [done | iIntros "_"; done].
  Qed.

  (* The next word of the same record: offset 8 in the region. *)
  Lemma heap_write_spare_offset (p len cap : Z) (x11 x12 x16 : bv 64) :
    bv_unsigned x11 = p -> bv_unsigned x12 = 8 * len -> bv_unsigned x16 = 32 * len ->
    len < cap ->
    (p + len * 40) ↦ₘ? ((cap - len) * 40) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + (x16 + x12))%bv + 8))
      (fun mk : mem_mapsto_kind => match mk with
        | MKUninit start count => ⌜start = (p + len * 40)%Z⌝ ∗ (start ↦ₘ? count -∗ True)
        | _ => False end)%I.
  Proof.
    intros. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_heap_write.
    iSplit; [done | iIntros "_"; done].
  Qed.

  (* After the first store: the region left starts 8 bytes later, and the
     address's own offset 8 meets the region start (txAccessList +0x464). *)
  Lemma heap_write_after_store (p len cap : Z) (x11 x12 x16 : bv 64) :
    bv_unsigned x11 = p -> bv_unsigned x12 = 8 * len -> bv_unsigned x16 = 32 * len ->
    40 <= (cap - len) * 40 ->
    (p + len * 40 + 8) ↦ₘ? (p + len * 40 + (cap - len) * 40 - (p + len * 40 + 8)) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + (x16 + x12))%bv + 8))
      (fun mk : mem_mapsto_kind => match mk with
        | MKUninit start _ => ⌜start = (p + len * 40 + 8)%Z⌝
        | _ => False end)%I.
  Proof.
    intros. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_heap_write. done.
  Qed.

  (* Casts and a shift, no register equation (txAccessList +0x204). *)
  Lemma heap_write_cast_shift (p len cap : Z) :
    0 <= p -> 0 <= len -> len < cap ->
    (p + len * 32) ↦ₘ? ((cap - len) * 32) -∗
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 p + bv_shiftl (Z_to_bv 64 len) (BV 64 5))))
      (fun mk : mem_mapsto_kind => match mk with
        | MKUninit start _ => ⌜start = (p + len * 32)%Z⌝
        | _ => False end)%I.
  Proof.
    intros. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_heap_write. done.
  Qed.

  (* A load from an owned array at its second word. *)
  Lemma heap_read_array (p : Z) (x : bv 64) (items : list (bv 64)) :
    bv_unsigned x = p -> length items = 3%nat ->
    p ↦ₘ∗ items -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x + BV 64 8)%bv))
      (fun mk : mem_mapsto_kind => match mk with
        | MKArray _ start _ => ⌜start = p⌝
        | _ => False end)%I.
  Proof.
    intros. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_heap_write. done.
  Qed.

  (* Refused: the address and the region start differ by a non-constant. *)
  Lemma heap_write_other_place (p len cap : Z) (x11 x12 : bv 64) :
    bv_unsigned x11 = p -> bv_unsigned x12 = 8 * len -> len < cap ->
    (p + len * 40) ↦ₘ? ((cap - len) * 40) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + x12)%bv)) (fun _ => True)%I.
  Proof.
    intros. iIntros "H".
    Fail ZesuSsz.Automation2.Hooks.zesu_heap_write.
    iExists (MKUninit (p + len * 40) ((cap - len) * 40)).
    iSplitL "H"; [iExact "H" | done].
  Qed.

  (* Refused: a register without an equation. *)
  Lemma heap_write_no_fact (p len cap : Z) (x11 x12 x16 : bv 64) :
    bv_unsigned x11 = p -> bv_unsigned x12 = 8 * len -> len < cap ->
    (p + len * 40) ↦ₘ? ((cap - len) * 40) -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + (x16 + x12))%bv)) (fun _ => True)%I.
  Proof.
    intros. iIntros "H".
    Fail ZesuSsz.Automation2.Hooks.zesu_heap_write.
    iExists (MKUninit (p + len * 40) ((cap - len) * 40)).
    iSplitL "H"; [iExact "H" | done].
  Qed.

  (* Refused: the constant lies past the region (k < count fails). *)
  Lemma heap_write_past_region (p : Z) (x11 : bv 64) :
    bv_unsigned x11 = p ->
    p ↦ₘ? 8 -∗
    find_in_context (FindMemMapsTo (bv_unsigned (x11 + BV 64 8)%bv)) (fun _ => True)%I.
  Proof.
    intros. iIntros "H".
    Fail ZesuSsz.Automation2.Hooks.zesu_heap_write.
    iExists (MKUninit p 8). iSplitL "H"; [iExact "H" | done].
  Qed.

  (* Refused: a load continues with `False` on an uninitialized region. *)
  Lemma heap_read_uninit_refused (p : Z) (x11 : bv 64) :
    bv_unsigned x11 = p ->
    p ↦ₘ? 16 -∗
    find_in_context (FindMemMapsTo (bv_unsigned x11))
      (fun mk : mem_mapsto_kind => match mk with
        | MKUninit _ _ => False
        | _ => True end)%I.
  Proof.
    intros. iIntros "H".
    Fail ZesuSsz.Automation2.Hooks.zesu_heap_write.
  Abort.
End tests.
