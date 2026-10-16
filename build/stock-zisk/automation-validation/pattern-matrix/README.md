# Pattern coverage matrix

This matrix records decodeItem observations, free measurements, and nextUint64 predictions.
A residual cell describes the cited automation experiment.
It does not reopen a completed production proof.
The free column separates the frozen hold-out from training.
The alloc column remains null.
Every nextUint64 cell has status `predicted`.

| Pattern | decodeItem | free HOLD-OUT 0/43 | free BEST TRAINING run3 ON 16 VERIFIED | nextUint64 | alloc |
|---|---|---|---|---|---|
| propagate | closed: nine Auto blocks | 0/12; literal/register equalities | 4/12 verified; cast buffer-range conjunctions | predicted close:62b8,62c0,6304,6310 | null |
| introduce | residual: two closures, other obligations remain | 0/28; equalities and pure conjunctions | 12/28 verified; XOR/literal/subtraction, alignment, and class conjunctions | predicted residual/hand:62cc,632c | null |
| store-literal | residual: R2 stops at region/index selection | 0/1; list witness | 0/1; list witness | predicted residual/hand:6274,62d8,632c | null |
| store-symbolic | null: no native sample | 0/1; memory selection | 0/1; memory selection | predicted absent in bound classification | null |
| return-with-frame | residual: R3 suffix comparison | 0/2; memory selection | 0/2; memory selection | predicted residual/hand:62e4 | null |
| return-without-frame | null: no native sample | no sample | no sample | predicted absent in bound classification | null |
| loop | residual: fold-step equation | no sample | no sample | predicted residual/hand:6318 | null |
| call | null: no native sample | no sample | no sample | predicted residual/hand:6274 | null |

`MATRIX.json` binds the source snapshots and each issue comment.
It lists exact sites, rule names, stopping findings, and scope limits.
Rows overlap, so their site counts are not additive.

R1a plus both mask forms closes `6a08` and `6aa8`.
R1c assigns the correct witnesses at `6a38` and `6ad8`.
Their pure side conditions remain open after the failed R1d comparison.
R2 leaves the eight-byte store at `outputPointer+24` open in `6b08`.
R3 leaves five completed suffixes at the masked-return trace existential.
Both `6b08` suffix arms fail during their common setup.
The two loop blocks retain their fold-step equations.

E3 and the compositional contract changed later production interfaces.
This skeleton does not infer new rule-on results from those changes.
No new proof, comparison, or hold-out execution ran.
No alloc source was read.


## Free measurement scope

The frozen hold-out remains final at0/43.
Training run3 ON has16 verified closures after the uncapped verification supplement.
The original comparison records8 verified closures and8 compile timeouts.
The supplement verifies those8 unchanged sources.
The candidate remains unmerged because two decodeItem Auto controls regress.

The original counts are propagate4/12, introduce12/28, store0/2, and return0/2.
The store rows refine the original store label.
Block42160 has store and return labels.
The44 labels cover43 blocks.
Do not sum the denominators.
Residual classes describe the recorded first goals, not their causes.
The checkpoints retain complete goal counts.
This metadata update ran no proof or native comparison.

## nextUint64 prediction scope

The source is the exact posted prediction at issue13 comment6191876275.
The inventory has53 instructions and10 blocks.
Its criterion labels overlap.
The counts are propagate4, introduce2, store3, return1, loop1, and call1.
There are12 labels across10 blocks.
Block6274 has store and call labels.
Block632c has store and introduce labels.
The return instruction is6300 inside block62e4.

The four propagate-only blocks are predicted to close.
The other six blocks retain the posted residual/hand prediction.
The two absent-pattern cells are also explicitly predicted.
No cell reports a measured native result.
All native time, memory, result, and residual fields remain null.
Later checked data lemmas do not revise the accepted predictions.
Their existence does not establish native selection or closure.
The exact comment, inventory, criterion, and source pin are bound in MATRIX.json.
