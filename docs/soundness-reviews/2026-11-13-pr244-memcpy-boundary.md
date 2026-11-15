# Soundness review record: PR #244 / #251 memcpy boundary (2026-11-13/14)

Outcome (round 2): **Decision: approve with the conditions below. No further approval is required after the agent satisfies them.**

The remaining fix (pin `memcpyCsrPc` to `0x800e06c0` by a literal in `ZesuSsz/Evidence/SignatureGates.v`) lands in PR #251 with this record.

## Round 1: review

## Soundness review: PR #244 (2026-11-13), round 1

(Restored by the coordinator from its read of the file before the reviewer replaced it with the round-2 re-review,
which supersedes it. Text as read at 2026-11-13 ~14:42 local.)

**Decision: do not move the reviewed baseline to include this change. Choose C pending a corrected A.**

The code bundle is complete. The result predicate keeps its meaning. However, the complete contract changes its input domain and machine guarantees.
The new memcpy premise also exceeds the old trust boundary. Option A cannot derive the current premise merely by fixing its source and length.

### Scope and evidence

Reviewed Git objects: baseline `d73a7a5a5`; PR commit `813c2991d`; merge `8bd15c29c`; #220 head `0cc6f0ad0`;
pinned ZisK source `fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3`. File references refer to `8bd15c29c`.

### Findings

#### 1. High: the new memcpy premise omits runtime permissions

`memcpyCallSpec2` (ParentHeaderMemcpyService.v:24; SignatureGates.v:175) accepts arbitrary source and destination
addresses with separate byte resources. It requires no readable section for the source and no writable section for the
destination. `machine_call` does not supply these permissions. The pinned runtime requires them
(`core/src/mem.rs:906-927` readable source in one populated section; `mem.rs:877-903` destination not read-only and
inside writable memory; `mem.rs:930-967`). Byte ownership (Islaris `theories/ghost_state.v:184-214`) does not supply
section permissions. The old boundary includes `ziskMemcpyEntry` and its `ziskMemcpyDomain` conditions; the new one
neither includes them nor derives its result from `ziskMemcpyAllows`.
Required action: restrict the service to the reached copy and establish its runtime domain, or review a general
service contract with the required permissions. Option B as written not approved.

#### 2. High: option A cannot recover exact `zisk_input_end` preservation from the old premise

The old entry and exit own `reg_col zesu_sys_regs` (BitsShape 64, no link between entry and exit values). The new spec
returns the same `inputEndBits` it receives: a stronger guarantee. Both specs return only BitsShape 64 for
`zisk_free_input`. Required action: identify the additional guarantee explicitly; derive an adapter with the old
guarantees or obtain separate review for the stronger one.

#### 3. Medium: the complete contract does not cover the same inputs

The new entry adds: input between `0x40000000` and `0x80000000` ending before `zisk_input_end`; result and stack in
RAM; 16-byte stack alignment and 112 extra bytes for callees; extra separation conditions. The record adds saved
x25-x27 and an explicit input length; the projection sets `headerBeforeFrame` to `[]`; the exit permits arbitrary x1
and returns more resources. `parentHeaderArgsWellFormed_domain` proves only new domain implies old layout.
`Check (@ParentHeaderContractCorrect : Prop)` checks only the type.
Required action: record explicit approval of the restricted domain and changed guarantees; provide a bridge if equal
coverage is required; pin the complete expected statement.

### Answers

- Selected code: the bundle contains every required callee resource and no extra callee code (17 decodeItem calls,
  3 nextUint64 calls, one memcpy tail; nextUint64 contains one further decodeItem call). Shape follows F55/F57.
- Result meaning: unchanged after renames (mechanical text equality); semantic definitions match the baseline. Output
  meaning unchanged on the new domain, not equivalence of the complete statements.
- Runtime behavior: the pinned sources support the nonoverlapping copy under valid permissions (`memcpy.s:8-11`,
  `riscv2zisk_context.rs:1003-1042,2508-2537`, `dma_memcpy.rs:15-23`); no stack use; integer registers preserved.

### Conditions for a later baseline update

1. Correct the memcpy boundary and resolve exact `zisk_input_end` preservation.
2. Prove any claimed adapter from the retained reviewed premise.
3. Record the accepted contract domain and pin the complete statement.
4. Review the resulting signature and allowlist changes.
5. Run the existing soundness gate on the exact candidate head.

## Round 2: re-review request

## Round 2: re-review request (2026-11-14)

### What is asked

Re-review the corrected trust boundary in PR #251 (branch `orch/memcpy-boundary`, exact head `a011136d3`, which is
main `c11ef0c6e` plus the PR). Decide whether the soundness gate's reviewed baseline may move to the commit that merges
it. Your first-round review is `docs/ai/SOUNDNESS_REVIEW_2026-11-13.md` (decision: C pending a corrected A). The
detailed answer to each finding is `docs/ai/SOUNDNESS_REVIEW_REQUEST_2026-11-13b.md`; this section summarizes it.

Files changed by #251 against main:
`ZesuSsz/Contracts/ParentHeaderMemcpyService.v`, `ZesuSsz/Contracts/ParentHeaderContract.v`,
`ZesuSsz/Evidence/SignatureGates.v`, `ZesuSsz/Evidence/MemcpyBaselinePremiseDegenerate.v` (new),
`ZesuSsz/Evidence/spec_shape_inventory.json`. On `a011136d3`: proof hygiene, release-import and spec-shape checks
pass; check-fast and check-iris exit 0.

### New finding 0: the baseline premise was vacuous, so option A as specified is not possible

Your required action asked for an adapter from the retained baseline premise. That premise,
`memcpyServicePremise = □ instr_pre memcpyCsrPc ziskMemcpyServiceInstrSpec` (at `d73a7a5a5`), is degenerate:
`instr_pre` is contravariant in its precondition, the precondition is the wand `∀ .., Entry -∗ instr_pre ret Exit`, and
`Entry` owns x10. Any resource that owns x10 proves the wand by register exclusivity. 
`MemcpyBaselinePremiseDegenerate.v` copies the baseline definitions verbatim and proves:

- `baselineMemcpyServicePremise_degenerate`: the baseline premise implies `□ instr_pre memcpyCsrPc ("x10" ↦ᵣ v)`
  (reaching memcpy holding only x10, with no return continuation, counts as safe);
- `baselineMemcpyServicePremise_implies_any_call`: it implies the corrected premise, by register exclusivity only.

An adapter from it would carry no evidence, so none is offered. No proved theorem ever used the baseline premise
(decodeItem has no memcpy; the old parent statement was never proved). We ask you to review the corrected premise
directly against the ZisK sources you already checked (pinned commit `fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3`).

### The corrected premise (finding 1 and finding 2)

`ParentHeaderMemcpyService.v` at `a011136d3`. It stays the single trusted runtime premise
(`approved_runtime_premises = [memcpyCallPremise]`, `memcpyCallPremise = □ instr_pre memcpyCsrPc memcpyCallSpec2`).

```coq
Definition stockZiskPermissions : ZiskRuntimePermissions :=
  {| ziskReadableSection := fun address count =>
       Exists (fun section =>
         sectionReadable section = true /\
         sectionBase section <= address /\
         address + count <= sectionEnd section)
         (mapPopulatedSections defaultMap);
     ziskWritableSection := fun address count =>
       mapRamBase defaultMap <= address /\
       address + count <= machineRamEnd defaultMap /\
       Forall (fun section =>
         sectionWritable section = true \/
         address + count <= sectionBase section \/
         sectionEnd section <= address)
         (mapPopulatedSections defaultMap) |}.

Definition parentHeaderMemcpyDomain (destination : Z) : Prop :=
  ziskMemcpyRange destination parentHeaderMemcpyLength /\
  ziskReadableSection stockZiskPermissions parentHeaderMemcpySource parentHeaderMemcpyLength /\
  ziskWritableSection stockZiskPermissions destination parentHeaderMemcpyLength /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8.

Definition memcpyCallSpec2 : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte),
      ⌜bv_unsigned (argv !!! 1) = parentHeaderMemcpySource⌝ ∗          (* 0x80114fb8 *)
      ⌜bv_unsigned (argv !!! 2) = parentHeaderMemcpyLength⌝ ∗          (* 80 *)
      ⌜parentHeaderMemcpyDomain (bv_unsigned (argv !!! 0))⌝ ∗
      reg_col [(KindReg "zisk_input_end", BitsShape 64);
               (KindReg "zisk_free_input", BitsShape 64)] ∗
      parentHeaderMemcpySource ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0) ↦ₘ? parentHeaderMemcpyLength ∗
      ziskExtraParamsAddress ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = parentHeaderMemcpyLength⌝ ∗
      ⌜length scratch = 8⌝ ∗
      RET (fun _ =>
        reg_col [(KindReg "zisk_input_end", BitsShape 64);
                 (KindReg "zisk_free_input", BitsShape 64)] ∗
        parentHeaderMemcpySource ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0) ↦ₘ∗ source ∗
        ziskExtraParamsAddress ↦ₘ∗ word64Bytes parentHeaderMemcpyLength ∗
        True)))%I.
```

- Finding 1 (permissions): only the reached copy (source `0x80114fb8`, length 80); the source must lie inside one
  populated readable section and the destination and extra-params word must be writable RAM overlapping no populated
  non-writable section (`mem.rs:877-927`). Lemma `parentHeaderMemcpyDomain_runtime` proves this gives the full
  `ziskMemcpyDomain` for any 4-aligned 64-bit return address.
- Finding 2 (`zisk_input_end`): both ZisK registers are owned and returned with `BitsShape 64` only; no exact
  preservation is promised. Consequence in the parent contract: on the memcpy-tail path, decodeParentHeader's exit
  returns `zisk_input_end` with shape only (`parentHeaderExitSysRegs`); the direct path keeps the exact value.

### Finding 3

- The complete statement of `ParentHeaderContractCorrect` is now pinned in `SignatureGates.v` with `eq_refl` against
  reviewed copies (call projection, well-formedness predicate, system-register lists, entry and exit resources, the
  scratch-after function, resources, model, statement), layout constants as literals.
- The restricted domain and changed machine guarantees (the 8 items listed in the 13b file): the user approved them
  as intended on 2026-11-14 (maintainer approval). No bridge to the old domain is offered.

### Questions

1. Is the corrected premise acceptable as the trusted runtime boundary for this reached copy?
2. Reads are bounded by `sectionEnd`, not `sectionFileEnd`. Is that right for the stock image?
3. Is the writable section the whole RAM range?
4. Is the shape-only `zisk_input_end` on the memcpy-tail exit acceptable, or do the sources justify exact preservation
   (the runtime never writes that register)?

Please end the review with one line: approve / approve with conditions (list them) / reject.

## Round 2: re-review

## Soundness re-review: PR #251

**Decision: approve with the conditions below. No further approval is required after the agent satisfies them.**

This review supersedes the first review of PR #244.
I reviewed `a011136d3a1248a13b882e78ce69cb7f8fb4d79e` against main `c11ef0c6e` and baseline `d73a7a5a5`.
I checked the runtime sources at `fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3` in `/home/cody/zisk`.

### Remaining fix

Pin the memcpy entry address to `0x800e06c0` in `SignatureGates.v`.
At line 227, both the actual premise and the reviewed premise use `memcpyCsrPc`.
A change to that notation therefore changes both sides of their equality check.
The file contains no independent literal check for that address.

Add this check:

```coq
Check (eq_refl : memcpyCsrPc = 0x800e06c0%Z).
```

Alternatively, use `0x800e06c0` directly in `ReviewedMemcpyCallPremise`.
Either fix closes this finding.
The agent does not need another review for this exact fix.

### Answers to the re-review questions

#### 1. The corrected runtime premise is acceptable

`ParentHeaderMemcpyService.v` now restricts the copy to source `0x80114fb8` and length 80.
The caller cannot select arbitrary permissions.
The domain requires a readable source, a writable destination, and a writable scratch word.
The separate resources exclude overlap between these three nonempty arrays.

The pinned runtime supports the stated result:

- `memcpy.s:8–11` supplies the marker, argument instruction, and return.
- `riscv2zisk_context.rs:1003–1042,2508–2537` stores the count before the copy.
- `dma_memcpy.rs:15–23` invokes `Mem::memcpy` with that count.
- `mem.rs:877–968` checks the sections and copies the source bytes.
- `zisk_inst_builder.rs:185–193` discards the write to x0.

The service uses no stack and preserves the architectural integer registers.
Those guarantees support the weaker guarantees in `machine_call`.
Its aligned return address also agrees with the runtime's clearing of bit zero.

`parentHeaderMemcpyDomain_runtime` connects the new domain to `ziskMemcpyDomain`.
That lemma does not prove the runtime implementation.
I accept `memcpyCallPremise` as the single reviewed runtime premise for this reached copy.
The library axiom list remains empty.

#### 2. `sectionEnd` is correct for this stock copy

The source interval is `[0x80114fb8, 0x80115008)`.
It lies inside the readable segment `[0x8010fd80, 0x80118678)`.
For that segment, `sectionEnd` and `sectionFileEnd` are equal.
Thus, the choice does not admit additional source bytes for this premise.

The distinction matters for zero-filled writable segments.
The runtime initializes the whole RAM section, including bytes beyond an ELF segment's file data.
`sectionFileEnd` would incorrectly exclude those bytes.

`stockZiskPermissions` supplies sufficient permissions for this restricted premise.
It does not enumerate every readable runtime range.
For example, the runtime also permits RAM reads outside the listed ELF segments.
That conservative restriction causes no problem for the fixed source.

#### 3. The writable section covers the whole RAM range

`emulator/src/emu_context.rs:70–71` calls `add_write_section(RAM_ADDR, RAM_SIZE)`.
`mem.rs:300–331` allocates that complete section.
The constants select `[0xa0000000, 0xc0000000)`.
The writable section is not limited to the ELF's writable segments or the heap.

The new predicate also excludes overlap with populated non-writable sections.
All such sections in this stock map lie outside RAM.
The scratch interval `[0xa0400f00, 0xa0400f08)` lies inside RAM.

#### 4. Shape-only `zisk_input_end` is acceptable

The new premise returns both ZisK registers with `BitsShape 64` only.
The parent contract applies that guarantee on the memcpy-tail exit.
The direct exit retains the exact input-end value.
This closes the stronger-guarantee finding from the first review.

The runtime sources show no write that requires changing the input-end value.
That observation does not require a stronger trusted claim.
Keep the weaker guarantee in this PR.
No further preservation proof or approval is required.

### Closure of the first review

The permission changes close finding 1.
The shape-only return closes finding 2.
The reviewed statement copies close the missing statement check from finding 3, subject to the entry-address fix above.
The output meaning and callee inventory remain accepted.

The appended Round 2 request records maintainer approval of all eight domain and machine changes.
That record supersedes the pending-approval text in the earlier follow-up request.
No bridge to the old domain is required.
This review creates no further approval requirement for those eight items.

My first review missed the orientation defect in the baseline premise.
The diagnostic copies preserve its definitions after renaming and whitespace changes.
The exclusivity argument proves the old wand from ownership of x10 alone.
Consequently, the old premise implies the corrected premise without evidence about copying.
I withdraw the requirement to derive a meaningful adapter from that premise.

The corrected precondition instead owns the call resources together with the return continuation.
The old diagnostic premise must remain outside the trusted boundary.
The allowlist contains only `memcpyCallPremise`.
No Rocq source imports the diagnostic module at the reviewed head.

### Conditions and authorization

The agent must complete these mechanical steps:

1. Add the literal check above or use the literal in the reviewed premise.
2. Compile the affected signature and contract modules with the normal proof checks.
3. Pass check-fast and check-iris on the final PR head before integration.
4. Integrate #251 and set `BASELINE` to its exact merge commit on main and #220.
5. Pass the existing PUBLIC soundness gate on the final #220 candidate, including its negative controls.

This review supplies approval for the listed fix, #251 integration, baseline updates, and gate reruns.
After the conditions pass, the agent proceeds without another reviewer or maintainer approval request.
The conditions require successful checks, not another discretionary decision.
The agent must retain the existing release gates.

### Verification record

I inspected the exact Git sources and compared the baseline definitions mechanically.
The other three protected contexts remain identical to `d73a7a5a5`.
The request reports passing hygiene, import, shape, check-fast, and check-iris checks on `a011136d3`.
I did not independently rerun those checks or compile the proofs during this review.
I changed only this review file.

approve with conditions: pin the memcpy entry literal and pass the listed compilation, integration, and soundness checks. No further approval is required.
