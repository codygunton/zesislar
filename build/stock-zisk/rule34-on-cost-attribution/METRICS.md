The measurements cover one compiler process per native arm. Each compiler uses one worker. CPU and RSS do not measure aggregate machine use.

| Observation | Bound | CPU seconds | Peak RSS KiB | Raw final goals |
| --- | ---: | ---: | ---: | ---: |
| Full recorder |128|269.358679|1938544|3|
| Light observer |128|8.681301|1063972|3|
| Light observer |1024|208.550661|2517040|25|
| Targeted observer |1280|455.129625|2733584|32|
| Targeted observer |1408|556.896081|2793132|34|
| Targeted observer |1536|801.247475|2852924|36|
| Scoped profiler |1296|519.237614|2727776|33|
| Terminal observation |2048|1332.186865|3311484|49|

The profiler total is 23.179 CPU seconds. Printed percentages use 0.1 percent precision. The nominal RAM-fault inclusive time is 22.715420 seconds. The nominal stack-arithmetic inclusive time is 22.692241 seconds. Its nominal local time is 1.112592 seconds. The nominal closed-term local time is 9.642464 seconds. These derived values retain percentage rounding error.

The compiler records separate elapsed time from CPU time. Marker timestamps measure output arrival. Buffering can delay output. The sampler records one compiler PID and its start ticks. It samples RSS every 25 milliseconds. Samples include observer allocation. The complete machine utilization history is unavailable.

The final gate passed with six workers in 596.351812 seconds. Its `RUSAGE_CHILDREN` peak is 3037236 KiB. Its elapsed time includes admission waits. `RUSAGE_CHILDREN` can exclude guarded compiler scopes. These measurements do not measure aggregate machine memory.

Token totals remain unavailable. The report makes no token estimate.
