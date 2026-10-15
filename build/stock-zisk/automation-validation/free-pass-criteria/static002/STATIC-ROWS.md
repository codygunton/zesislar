# Static Phase 2 ratios

These rows compare checked source counts. They do not report a native result.

| Criterion | Free exact fraction | Free display | decodeItem exact fraction | decodeItem display | Static result |
|---|---|---:|---|---:|---|
| introductions_per_registered_quantity | `113/1` | 113.000000 | `3688/4` | 922.000000 | Pass: free <= decodeItem |
| interface_lines_per_block | `1105/43` | 25.697674 | `16888/24` | 703.666667 | Pass: free <= decodeItem |

The introduction numerator counts only the introductions category.
Its denominator counts one guarded class for free and four quantities for decodeItem.
The block ratio counts all six scored interface categories.
Exact cross-products decide both comparisons. Display values round to six decimal places.

The accepted free package is `0a6f495e83f814eb5a2f02db867239bc245e1a04`.
Its 1,105 lines include 121 new module lines and one umbrella export line.
Historical counts remain separate. All native fields remain null.
