### Pre-full-run hand-line prediction: nextUint64

This prediction preserves [the posted ten-block forecasts](https://github.com/codygunton/zesislar/issues/13#issuecomment-6191876275).
It uses the historical decodeItem audit and [the accepted free calibration](https://github.com/codygunton/zesislar/issues/13#issuecomment-6188076869).
It precedes the full ten-block run. The caller-first experiment remains separate.
I inspected no current caller-first residual or result for this prediction.

| Block | Posted class | Predicted hand lines or component proxy |
|---|---|---|
|6274|store, call|Unknown call budget. Frame component1–13 is non-additive.|
|62b8|propagate|0 predicted, not measured.|
|62c0|propagate|0 predicted, not measured.|
|62cc|introduce|29–66 historical whole-body proxy.|
|62d8|store|5–36 output-store component proxy.|
|62e4|return|5–20 return component proxy. Frame1–13 is non-additive.|
|6304|propagate|0 predicted, not measured.|
|6310|propagate|0 predicted, not measured.|
|6318|loop|160–171 historical physical proof lines.|
|632c|store, introduce|Store5–36 and introduction29–66 overlap. Whole-block budget unknown.|

The eight rows excluding6274 and632c give an arithmetic proxy subtotal of199–293lines.
This subtotal mixes transferred whole-body and component counts. It is not a complete budget or a hard bound.
The call budget and the full hand-line budget remain null.

The measured decodeItem component rates are output130/6, return100/6, and frame67/7.
The loop audit counts160 and171physical Proof-through-Qed lines, with mean331/2.
The study's20-line loop target is an unverified aspiration. It supplies no measured reduction.
The existing four-close/six-residual-or-hand forecast remains unchanged.
The twelve original labels cover ten blocks. The6274 and632c overlaps remain explicit.

The installed bridge contains42composition lines. Its registration and export add8interface lines.
These are per-function text. They are not handwritten block lines or evidence of caller closure.
The integrated interface totals5174lines.

Source Root: 1caa440a0f98488e978f4ac13f046383fb26289b. Calibration Root:6e08631942efd13d229ff7a46a01ab6a3c42384a.
Frozen forecast SHA256:d7ee30a8ba45d30f6d1f5ec3a6ac1eb580049aa75c37096d87f23d6aec418d2a.
This item ran no proof or native execution. No alloc source was read.
