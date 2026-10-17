# Training 4 comparison

Both arms verified 12 boundaries. Both arms retained 31 residuals.
The OFF prediction was 12. The ON prediction was 30. The comparison has zero gains and zero losses.

| PC | Group | Predicted OFF | Predicted ON | Actual OFF | Actual ON | ON/OFF compile CPU |
|---|---|---|---|---|---|---:|
| 0x80041f38 | hand | residual | residual | native-residual | native-residual | — |
| 0x80041f58 | verified control | residual | closed | native-residual | native-residual | — |
| 0x80041f60 | verified control | residual | closed | native-residual | native-residual | — |
| 0x80041f68 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80041f7c | verified control | closed | closed | verified | verified | 0.964726 |
| 0x80041f80 | range | residual | residual | native-residual | native-residual | — |
| 0x80041f8c | range | residual | residual | native-residual | native-residual | — |
| 0x80041f98 | range | residual | residual | native-residual | native-residual | — |
| 0x80041fa4 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80041fb4 | verified control | closed | closed | verified | verified | 0.889407 |
| 0x80041fb8 | verified control | residual | closed | native-residual | native-residual | — |
| 0x80041fc0 | verified control | residual | closed | native-residual | native-residual | — |
| 0x80041fc8 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80041fd8 | verified control | closed | closed | verified | verified | 0.985424 |
| 0x80041fdc | range | residual | residual | native-residual | native-residual | — |
| 0x80041fe8 | range | residual | residual | native-residual | native-residual | — |
| 0x80041ff4 | leaf | residual | closed (conditional LUI spelling) | native-residual | native-residual | — |
| 0x80042010 | verified control | closed | closed | verified | verified | 1.015874 |
| 0x80042014 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80042028 | verified control | closed | closed | verified | verified | 0.894444 |
| 0x8004202c | range | residual | residual | native-residual | native-residual | — |
| 0x80042038 | leaf | residual | closed (conditional LUI spelling) | native-residual | native-residual | — |
| 0x80042054 | verified control | closed | closed | verified | verified | 0.990166 |
| 0x80042058 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80042070 | verified control | closed | closed | verified | verified | 1.167224 |
| 0x80042074 | range | residual | residual | native-residual | native-residual | — |
| 0x80042080 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80042090 | verified control | closed | closed | verified | verified | 1.053010 |
| 0x80042094 | leaf | residual | closed (conditional LUI spelling) | native-residual | native-residual | — |
| 0x800420b0 | verified control | closed | closed | verified | verified | 1.065849 |
| 0x800420b4 | leaf | residual | closed | native-residual | native-residual | — |
| 0x800420cc | verified control | closed | closed | verified | verified | 1.011853 |
| 0x800420d0 | leaf | residual | closed (conditional LUI spelling) | native-residual | native-residual | — |
| 0x800420ec | verified control | closed | closed | verified | verified | 1.019639 |
| 0x800420f0 | leaf | residual | closed (conditional LUI spelling) | native-residual | native-residual | — |
| 0x8004210c | verified control | closed | closed | verified | verified | 1.033799 |
| 0x80042110 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80042130 | leaf | residual | closed | native-residual | native-residual | — |
| 0x80042134 | range | residual | residual | native-residual | native-residual | — |
| 0x8004213c | range | residual | residual | native-residual | native-residual | — |
| 0x80042144 | hand | residual | residual | native-residual | native-residual | — |
| 0x80042154 | range | residual | residual | native-residual | native-residual | — |
| 0x80042160 | hand | residual | residual | native-residual | native-residual | — |

All nine Auto pairs verified. The largest Auto compiler regression was 4.935584 percent.
No Auto ratio meets the authorized median window. No repeat is required.
The original startup failures and authorized restart remain separate records within this run.
DETAILS.json retains all goal groups, exact raw evidence references, and actual compiler receipts.
This audit makes no rule-cause claim and no full-function closure claim.
