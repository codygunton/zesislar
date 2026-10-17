# nextUint64: nine-block result

The run verified no closure. Four entries had Pet failures. Three entries stopped without a response. Two entries retained open residuals.

The frozen Root is `f58fde97947c16d1f8a4eebb9d3761ac1a066524`. The caller entry `0x800d6274` is excluded.

| Entry | Prediction | Observed result | CPU seconds | Counter scope |
|---|---|---|---:|---|
| 0x800d62b8 | close | Pet runtime failure | unavailable | Aggregate CPU unavailable. |
| 0x800d62c0 | close | Pet runtime failure | unavailable | Aggregate CPU unavailable. |
| 0x800d62cc | residual/hand | bound stop; no response | 15856.670000 | Pet CPU only; final aggregate CPU unavailable. |
| 0x800d62d8 | residual/hand | open residual | 100.665730 | Parent-first tree sampling and final wait4. |
| 0x800d62e4 | residual/hand | bound stop; no response | 7200.084654 | Hierarchical accounting slice plus monitor and reaped controller CPU. |
| 0x800d6304 | close | bound stop; no response | 7200.507358 | Hierarchical accounting slice plus monitor and reaped controller CPU. |
| 0x800d6310 | close | Pet runtime failure | 398.576871 | Hierarchical accounting slice plus monitor and reaped controller CPU. |
| 0x800d6318 | residual/hand | Pet runtime failure | 87.229117 | Last retained aggregate observation; final CPU unavailable. |
| 0x800d632c | residual/hand | open residual | 101.680515 | Hierarchical accounting slice plus monitor and reaped controller CPU. |

The prediction expected four propagate-only closures. No closure received final verification. Runtime failures and missing responses limit this comparison.

The two residual exports contain three active goals each. Their stack, shelf, and given-up groups are empty.

The first residuals request `FindMemMapsTo` for `x9` and `x18`. The other goals request `FindStructRegMapsTo` for `medeleg/bits`.

The 62cc stop record says "no response within 4.2 CPU-hours". Its final Pet measurement was 15,856.67 seconds (4.404631 hours).

Normal cancellation stopped 62e4 at 7,200.084654 CPU seconds. It stopped 6304 at 7,200.507358 CPU seconds.

The 6318 monitor entered permanent observe-only mode after an ownership error. The proof process then closed naturally without monitor signals.

No result establishes an instruction completion count. No final compile or verification call ran.

The original startup failures remain separate from these nine outcomes. The record preserves their sources and prior reports.
