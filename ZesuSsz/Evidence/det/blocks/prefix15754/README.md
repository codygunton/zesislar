# 15754 prefix probes

The prefix probes use the explicit SplitState_15754 entry at revision f15b0e67.
The three prefixes run in parallel within the 48-job wave.
The stop addresses are 15774 (k=8), 15794 (k=16), and 157b4 (k=24).
Each probe has a 300-second cap and a 6-GiB memory fence.

| Prefix | Seconds | Peak MiB | Outcome | Residual class |
| --- | ---: | ---: | --- | --- |
| k=8 | 66.1 | 6186 | memory | unavailable |
| k=16 | 66.1 | 6187 | memory | unavailable |
| k=24 | 65.0 | 6186 | memory | unavailable |

The k=8 prefix already exceeds the memory limit.
The output contains no final residual before the kill.
These probes do not identify the instruction where memory first increases.
No unchanged prefix will be repeated.
