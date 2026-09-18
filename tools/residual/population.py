"""Which population a probed proof belongs to.

Section 9 of the plan fixes the denominator of the gate: the harness targets
Iris lemmas. Three groups sit outside it and stay in the corpus only as
records.

- `unfold`: a `..._unfold` lemma whose proof is `done`. It states a
  definitional equality, and the automation is not meant to find it.
- `pure`: a lemma that is not an Iris entailment at all, either because
  `iStartProof` refused it or because it lives in a Model, Facts, Layout or
  Trace module.
- `iris`: everything else, the population the harness must serve.
"""

from __future__ import annotations

import re

PURE_MODULE = re.compile(r"(Model|Facts|Layout|Trace)\.v$")
TRIVIAL = ({"done."}, {"done"}, set())


def population(module: str, lemma: str, hand_lines: list[str],
               error_kind: str = "") -> str:
    hand = {line.strip() for line in hand_lines if line.strip()}
    if lemma.endswith("_unfold") and hand in TRIVIAL:
        return "unfold"
    if error_kind == "not_bi" or PURE_MODULE.search(module):
        return "pure"
    return "iris"
