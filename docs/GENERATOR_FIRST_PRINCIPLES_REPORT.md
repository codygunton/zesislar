# Is the generator a reasonable thing to build? A first-principles report

2026-11-22. Written for the question: our measure-unblock loop on the generator is not clearly
converging; is full automation a reasonable goal, and if not, what is the optimal and the best
practical agent-assisted design? Sources are linked at the end; numbers about our own system come
from the repository and the held-out runs (`docs/BLOCK_AUTOMATION_REBUILD_PLAN.md`, Status).

## TLDR

1. **What we built is an invariant-inference engine, and that is the hard half of program
   verification.** The generator must produce a correct, strong-enough assertion at every
   basic-block boundary of compiled code, from a contract and a disassembly alone. Inferring such
   assertions is undecidable in general, and fifty years of work automate it only for weak
   properties, bounded code, or one narrow family of programs at a time.
2. **That is why it is not "already solved", and AI did not change that part.** What AI changed is
   the price of the other half: writing specifications, invariants and proofs, which a checker then
   validates. The field's successful tools all take that shape (the user or a compiler supplies the
   invariants; the tool checks). Islaris itself does.
3. **Full automation of our generator is not a reasonable goal.** A generator that needs zero
   per-function input on arbitrary functions of this binary is a research programme, not an
   engineering task. Our held-out results (3 of 255 blocks) are what theory predicts when the
   inference domain was fitted to one family of functions.
4. **The optimal design is "agents propose, the kernel checks".** Mechanical parts stay mechanical:
   symbolic execution of straight-line code, frame inference, arithmetic side conditions,
   composition. Everything that needs invention is proposed by an agent and checked: internal
   contracts, loop and join invariants, data-structure predicates, callee specifications. A wrong
   proposal cannot produce a false theorem; it only fails to check.
5. **We already work this way on the functions we proved, and measured the opposite on the held-out
   ones.** decodeParentHeader's proof rests on 51 KB of hand-written profile data and 9,500 lines of
   hand-written Coq. The held-out protocol forbade exactly that input, so it measured unassisted
   inference, which is not the product we need.
6. **docs/GENERATOR_FIRST_PRINCIPLES_REPORT.mdBest practical next step: stop widening inference;
   turn every generator stop into a typed request for an annotation; give agents the source code as
   an untrusted hint; and measure agent effort per function to a checked proof.** A pilot on five
   held-out functions would tell us the marginal cost per function and whether it falls. That is the
   convergence metric that matters.
7. **Blind spots that no amount of generator repair addresses:** indirect jumps (125 of 527
   functions), platform instructions the decoder refuses, 203 functions that call callees with no
   contract, functions of up to 2,690 blocks, proof stability when the guest is recompiled, and the
   fact that our rule library has still not met multiplication, division or register shifts on
   unseen code.

## 1. What we are actually building

For each function the pipeline needs:

- a **contract** (hand-written): what the function owns, requires and guarantees;
- an **entry statement for every basic block** (generated): the registers' values and the memory
  owned when control reaches that block, strong enough that the block's own proof establishes each
  successor's entry statement;
- a **proof per block** (rule library, `zesu_block2`) and a composition.

The generator therefore computes an _inductive invariant map over the whole control-flow graph_. At
straight-line boundaries that is mechanical (strongest postcondition). At joins and loop heads it is
not: the generator must _generalise_, i.e. decide which facts all incoming paths share, which to
drop, and how to phrase what varies. Every family of generator defect we met is a generalisation
defect: a join drops a linking fact; a wide join's guard is quadratic; paths multiply until a
budget; a loop needs a design; an indexed access cannot be placed in an array.

In the classical inductive-assertion method an assertion is needed only at one cut point per cycle;
the code between cut points yields verification conditions mechanically. We chose a finer grain, an
assertion at every block, because a block's proof already costs minutes in Rocq. The price of that
choice is that every join became an inference problem.

Our effective inference vocabulary today is: a register equals a contract-level term; memory is a
set of owned regions addressed as _base plus closed offset_; a loop cursor advances by a stride;
alternatives are a disjunction of path guards. Everything outside it stops the generator.

Scale, from the census of the pinned binary:

|                                                            |                                                         |
| ---------------------------------------------------------- | ------------------------------------------------------- |
| Functions in the binary                                    | 527                                                     |
| Functions our pipeline can decode today                    | 300                                                     |
| Basic blocks (413 functions with a CFG)                    | 35,011                                                  |
| Instructions                                               | 232,288                                                 |
| Blocks proved (decodeItem, nextUint64, decodeParentHeader) | 132 (0.4%)                                              |
| Functions with indirect jumps                              | 125                                                     |
| Functions with loops; nested                               | 98; 22                                                  |
| Functions with calls; calling a callee without a contract  | 259; 203                                                |
| Leaf functions with no loop and no indirect jump           | 123                                                     |
| Blocks per function: median, 90th percentile, largest      | 15, 103, 2,690                                          |
| Generator code; rule library                               | 70,500 lines of Python; 31,600 lines of Coq             |
| Hand-written for decodeParentHeader                        | 51 KB profile (3 loop designs, 10 join designs, 20 call |
|                                                            | rows); 9,562 lines of Coq                               |

## 2. Why this is not already solved

**Theory.** Inferring an inductive invariant strong enough for a given specification is undecidable;
any fixed inference vocabulary is incomplete for some program. Cousot states the practical
consequence: "A finite abstraction can always be found for a given program and specification but
discovering this abstraction amounts to making the proof", and automatic verifiers avoid false
alarms by considering "families of programs for which generic, precise and efficient abstractions
can be found" [Cousot05]. Astrée proves absence of run-time errors with no false alarms only for one
family (synchronous control and command code, with restrictions such as no recursion), and was
adapted by specialists as new idioms appeared. That is the same measure-and-unblock loop we are in;
it converged for them because the family was fixed and narrow.

**What is automated at scale, and for which property.**

| Approach                            | Property                                     | Why it can be automatic                                   |
| ----------------------------------- | -------------------------------------------- | --------------------------------------------------------- |
| Bi-abduction (Infer) [Biabduction]  | memory safety                                | infers pre/post specifications, but only about heap shape |
| Verified binary lifting [Verbeek22] | return-address integrity, calling convention | an invariant at every vertex, but only "sanity" facts     |
| Astrée [Cousot05]                   | no run-time errors                           | one program family; domains added by specialists          |
| Serval, Hyperkernel [Serval]        | functional refinement                        | only *finite* code: every operation has bounded traces    |
| SAW on AWS-LC [AWSLC]               | functional, cryptography                     | bounded loops and straight-line code, with hand-written   |
|                                     |                                              | specifications and overrides per function                 |

Nobody has automatic inference for _functional correctness of unbounded, pointer-rich code_. That
needs invariants about content and data-structure representation, which is where every tool takes
input from a person or a compiler.

**What the field does instead of post-hoc binary inference.**

- _Annotate and check._ Islaris, the logic we build on, has the user write the specification and the
  loop invariant: for `memcpy` "the main task is to find a loop invariant"; its case studies "are
  not large in instruction count" [Islaris]. RefinedC, CN, VST and Verus are the same shape at
  source level [RefinedC] [CN].
- _Let the compiler supply the invariants._ Proof-carrying code and typed assembly work because a
  certifying compiler emits the loop invariants and types it already knows [CertComp] [FPCC]. A
  stripped binary has lost exactly that information; recovering variables and types from executables
  is its own research field [WYSINWYX].
- _Carry a source-level proof down._ seL4's binary verification validates the compiler's output
  against the verified C, using the C program's structure to find loop correspondences. It covers
  all functions at -O1 except 21 machine-interface functions, 3 with nested loops and 2 others, and
  at -O2 extracts a model for 98% but proves mainly loop-free functions; the authors also changed
  the source to help the tool [seL4TV].
- _Build it correct._ The Ethereum Foundation's own EVM track says it "has ultimately focused on the
  feasibility of implementing an execution guest program with natively verified RISC-V assembly,
  either via the use of a proof assistant as macro assembler or via verified compilation" [EFtrack];
  the post-hoc route (revm compiled to RISC-V against KEVM [RVharness]) is one grant among four.

**Where a zkVM guest sits.** It is an unusually favourable target for binary-level proof: the binary
is the trusted artefact, there is no concurrency, no operating system, a fixed compiler, an
authoritative ISA model, and an executable specification of the top-level function. It is
unfavourable in two ways that general theory predicts: an interpreter is built on indirect dispatch,
and the code is ordinary optimised compiler output, not code written to be verified.

## 3. Did AI change it?

It changed the cost of the _checked_ half, not the decidability of the _inferred_ half.

- **The historical cost was human effort per line.** seL4 took 11 person-years plus 9 for tools and
  libraries; a 2025 Rust kernel took 1.5 person-years of verification for 6,000 lines at a
  proof-to-code ratio of 3.32 to 1 [Atmosphere]. Proof effort, not theory, kept verification out of
  ordinary software.
- **Agents now supply much of that effort.** On seL4's Isabelle proofs, GPT-4 alone proved 20% of a
  benchmark; a 2026 neuro-symbolic system proves 77.6% and cuts expert proof-writing effort by 79.8%
  in a collaboration setting [NeuroSym]. Our own project is evidence too: agents wrote the rule
  library and closed 98 blocks.
- **Invariant invention is where models are still weak without feedback.** On loop invariants for
  memory-manipulating programs, baselines including GPT-4 passed under 15% in one attempt [LIGMM].
  With a verifier's errors fed back in a loop, a Verus proof agent closes more than 90% of 150 small
  proof tasks [AutoVerus].
- **So the design lesson is guess-and-check.** An agent proposing an invariant is cheap and
  fallible; a kernel checking it is sound. A generator that must _infer_ the same invariant with no
  proposals gets no benefit from AI at all.

## 4. Is our generator a reasonable thing to build?

Split it into its two roles.

- **As a mechanical statement and obligation generator: yes.** Computing strongest postconditions
  through straight-line code, tracking owned regions, rendering entries, edges and certificates, and
  composing a function proof is exactly what a tool should do, and it worked for three functions.
- **As an inference engine expected to need no per-function input: no.** Extending the vocabulary
  one idiom at a time (indexed access, links, masked indices, nested cursors, wide joins,
  conditional pointers) is rebuilding a binary-level abstract interpreter with relational numeric
  domains, array-segment domains [ArraySeg] and shape analysis, strong enough for functional
  correctness. No one has that. Each held-out batch found a new layer because the space of idioms in
  35,000 blocks of compiler output is large and our vocabulary was fitted to a few hundred.

Two facts about our own results support the split:

- The functions we proved were _not_ proved by inference alone. decodeParentHeader needed loop
  designs, join designs, visibility lists, call rows and thousands of lines of contract-side Coq.
- The held-out protocol asked for "zero function-specific data". It measured the role we should not
  be building, and said nothing about the role we should.

## 5. The optimal agent-assisted design

Trusted base, unchanged: the Sail model and Isla traces, the Islaris logic, the Rocq kernel, and the
public contract (the specification of the guest's top-level function).

Everything else is _untrusted input that is checked_:

| Item                                                        | Who produces it                       | Why                                                |
| ----------------------------------------------------------- | ------------------------------------- | -------------------------------------------------- |
| Internal function contracts, callee specifications          | agent                                 | needs design; many valid choices                   |
| Invariants at cut points (loop heads, chosen joins)         | agent                                 | undecidable to infer; cheap to check               |
| Data-structure representation predicates (hash map, array   | agent, once per structure             | not inferable from code; reusable across functions |
| list, arena, tagged union)                                  |                                       |                                                    |
| Which facts stay visible, which are hidden                  | agent, defaulted by tool              | affects proof cost, not soundness                  |
| Straight-line symbolic execution, frames, region placement, | tool                                  | decidable and mechanical                           |
| composition                                                 |                                       |                                                    |
| Arithmetic and bitvector side conditions                    | decision procedures, agent on failure | mostly decidable; nonlinear cases need help        |
| Proof repair when automation stalls                         | agent                                 | the leftover goal is the feedback                  |

Properties of the optimum:

1. **No refusals, only requests.** When the tool cannot place an access or generalise a join it
   emits a typed question ("which region does this address lie in, and why?"; "what holds at this
   loop head?") and the agent's answer becomes an obligation the predecessor block proves.
2. **Source and debug information as hints.** The Zig and Rust source, struct layouts and variable
   locations give most invariants directly. They need no trust: the proof is still against the
   binary. Our pipeline uses none of it; seL4's binary proof shows how much source structure helps
   [seL4TV].
3. **A fast inner loop.** Guess-and-check needs seconds per attempt. A block costs 1 to 30 minutes
   today and a forward pass up to minutes and gigabytes; that, not CPU supply, limits iteration.
4. **Annotations where theory says they are needed.** One per loop and per function boundary is the
   minimum; more only where a join is too wide to enumerate.
5. **Effort is the metric.** Agent time and attempts per function to a checked proof, and its trend
   as libraries of predicates and conventions accumulate.

## 6. The best practical version

1. **Freeze inference at today's coverage.** Keep the merged repairs; fix outright bugs (the
   renderer crash). Do not add indexed-access or shape domains to the generator.
2. **One annotation mechanism.** Generalise the existing profile keys (`loop_designs`,
   `join_designs`, `return_facts`, `hist_visible`, call rows) into a single form: an assertion
   supplied for any boundary, plus region-placement facts for an access. Every stop in the forward
   pass maps to a request in that form.
3. **Contract conventions and a predicate library.** The two conventions the held-out runs exposed
   (data pointers in valid memory; an instance exposing ranges and links to the prover), and
   representation predicates for the handful of data structures this codebase uses.
4. **Source hints.** Give the agent the source function, the struct layouts and the symbol and line
   tables next to the disassembly.
5. **Pilot, about a week.** Five held-out functions of different kinds (one from each batch-two
   group). An agent may write any function-specific contract, annotation or lemma, and no generic
   rule or generator change. Record per function: time, attempts, lines written, where it had to
   stop for a generic gap. Repeat on five more and compare. Falling cost per function is
   convergence; flat or rising cost says the per-block architecture itself is the problem.
6. **Decide the scope with the census in hand.** 125 functions have indirect jumps and others use
   instructions the decoder refuses; these need a design decision (prove dispatch targets by table;
   axiomatise platform calls; or exclude and document), not generator work.

## 7. Blind-spot checklist

Each row: what a complete treatment needs, and where we stand. "Untested" means no block of that
kind has reached the prover on unseen code.

| Component               | Needs                                                       | Status                                                       |
| ----------------------- | ----------------------------------------------------------- | ------------------------------------------------------------ |
| **Arithmetic**          | 64-bit modular reasoning; multiply, divide, remainder;      | rules cover the decoder's add, compare and                   |
|                         | shifts by a register; signed compares; multi-limb carries;  | shift-by-constant; everything else untested                  |
|                         | nonlinear side conditions                                   |                                                              |
| **Memory: regions**     | owned regions of symbolic size; read-only data;             | works for base plus closed offset; device-input region makes |
|                         | uninitialised memory; a platform memory map                 | loads two-valued unless the contract excludes it             |
| **Memory: indexing**    | `base + scale * index + offset` with the index bounded by a | not supported; next stop in all five batch-two groups        |
|                         | guard, length or mask                                       |                                                              |
| **Memory: indirection** | struct fields, pointer chains, null-or-pointer, recursive   | one level of 64-bit links only, since this week              |
|                         | structures                                                  |                                                              |
| **Memory: views**       | the same bytes as words, bytes, arrays; partial overlap     | handled case by case for the decoder; a recurring source of  |
|                         |                                                             | open goals                                                   |
| **Control: joins**      | which facts survive; disjunction management                 | repaired guard form; still the main inference burden         |
| **Control: loops**      | invariants; nesting; several exits; cursors tied to arrays  | structural part inferred; invariants about content must be   |
|                         |                                                             | supplied                                                     |
| **Control: indirect**   | jump tables, function pointers, interpreter dispatch        | not supported; 125 functions                                 |
| **Calls**               | a contract per callee; conventions per compiler; recursion; | works for the decoder's callees; 203 functions call a callee |
|                         | variable-size outputs                                       | with no contract                                             |
| **Platform**            | zkVM system instructions and precompiles as specified       | decoder refuses them; no model                               |
|                         | operations                                                  |                                                              |
| **Data structures**     | representation predicates and their lemmas                  | none outside the decoder                                     |
| **Meaning**             | functional specifications for internal functions            | exists only for the three proved functions                   |
| **Scale**               | proof cost per block; very long blocks; statement size      | minutes per block; 157- and 413-instruction blocks do not    |
|                         |                                                             | finish                                                       |
| **Maintenance**         | proofs that survive recompilation of the guest              | certificates are keyed to addresses of one binary; not       |
|                         |                                                             | addressed                                                    |
| **Termination**         | separate argument                                           | planned, not started                                         |

## 8. What this means for the decision in front of us

- A second generator-repair round in the current style would add vocabulary for indexed access and
  more link forms. It would move the held-out counts, and the next batch would again find what it
  lacks. I would not do it as the main line.
- I would run the pilot of section 6 instead. It tests the architecture we actually need, costs
  about what one repair round cost, and its result is interpretable either way.
- Separately, the scope question (indirect dispatch, platform calls, recompilation) deserves an
  explicit decision, because it bounds what "the guest is verified" can mean for this binary, and
  because the Foundation's own track has moved toward construction over post-hoc proof.

## Sources

- [Islaris] Sammler et al., "Islaris: Verification of Machine Code Against Authoritative ISA
  Semantics", PLDI 2022. https://people.mpi-sws.org/~dg/papers/pldi2022.pdf
- [seL4TV] Sewell, Myreen, Klein, "Translation Validation for a Verified OS Kernel", PLDI 2013.
  https://www.cl.cam.ac.uk/~mom22/pldi13.pdf
- [Cousot05] Cousot, "The Verification Grand Challenge and Abstract Interpretation", VSTTE 2005.
  http://dl.ifip.org/db/conf/vstte/vstte2005/Cousot05.pdf
- [Biabduction] Calcagno, Distefano, O'Hearn, Yang, "Compositional Shape Analysis by Means of
  Bi-Abduction", JACM 2011. https://dl.acm.org/doi/10.1145/2049697.2049700
- [Verbeek22] Verbeek, Bockenek, Fu, Ravindran, "Formally Verified Lifting of C-Compiled x86-64
  Binaries", PLDI 2022. https://www.ssrg.ece.vt.edu/papers/pldi22.pdf
- [Serval] Nelson et al., "Scaling symbolic evaluation for automated verification of systems code
  with Serval", SOSP 2019. https://dl.acm.org/doi/10.1145/3341301.3359641
- [AWSLC] AWS libcrypto verification (SAW, Cryptol). https://github.com/awslabs/aws-lc-verification
- [WYSINWYX] Balakrishnan, Reps, "WYSINWYX: What You See Is Not What You eXecute".
  https://research.cs.wisc.edu/wpis/papers/wysinwyx.final.pdf
- [CertComp] Necula, Lee, "The Design and Implementation of a Certifying Compiler" (retrospective).
  https://people.eecs.berkeley.edu/~necula/Papers/certcomp_retrospective.pdf
- [FPCC] Appel, Foundational Proof-Carrying Code. https://www.cs.princeton.edu/~appel/fpcc.html
- [RefinedC] Sammler et al., "RefinedC", PLDI 2021. https://plv.mpi-sws.org/refinedc/paper.pdf
- [CN] Pulte et al., "CN: Verifying Systems C Code with Separation-Logic Refinement Types",
  POPL 2023. https://www.cl.cam.ac.uk/~cp526/popl23.html
- [ArraySeg] Cousot, Cousot, Logozzo, "A Parametric Segmentation Functor for Fully Automatic and
  Scalable Array Content Analysis", POPL 2011.
  https://pcousot.github.io/publications/CousotCousotLogozzo-POPL11-ACM-p105-118-2011.pdf
- [Atmosphere] "Atmosphere: Practical Verified Kernels with Rust and Verus", SOSP 2025.
  https://mars-research.github.io/doc/2025-sosp-atmo.pdf
- [NeuroSym] "Neuro-Symbolic Proof Generation for Scaling Systems Software Verification", OSDI 2026.
  https://www.usenix.org/system/files/osdi26-he-baoding.pdf
- [LIGMM] Liu et al., "Towards General Loop Invariant Generation: A Benchmark of Programs with
  Memory Manipulation", NeurIPS 2024.
  https://proceedings.neurips.cc/paper_files/paper/2024/file/e93b673c55d6768cdd39ce90de8c4d4c-Paper-Datasets_and_Benchmarks_Track.pdf
- [AutoVerus] Yang et al., "AutoVerus: Automated Proof Generation for Rust Code".
  https://arxiv.org/html/2409.13082
- [EFtrack] Verified zkEVMs, EVM track. https://verified-zkevm.org/project/evm
- [RVharness] Runtime Verification, zkevm-harness.
  https://github.com/runtimeverification/zkevm-harness
