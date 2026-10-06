The memory jump occurs in zesu_finish at diagnostic step266.
The adjacent bound265 uses1994192KiB. Step266 reaches the12GiB limit.

| Bound | Last step | CPU s | Compiler wall s | Peak KiB | Limit |
|---:|---:|---:|---:|---:|---|
| 257 | 257 | 96.953 | 97.225 | 1994164 | none |
| 263 | 263 | 112.408 | 112.735 | 1996236 | none |
| 265 | 265 | 125.529 | 125.885 | 1994192 | none |
| 280 | 266 | 312.176 | 313.005 | 12591308 | memory |

Step265 processes an index equality. Step266 processes the index bound against returnStorage.
Both goals contain unresolved nat evars. The JSON report contains their exact printed text.
The evidence identifies the outer finishing handler. Its internal allocating sub-tactic remains unknown.
No closure claim applies. Production Hooks.v and Finish.v remain unchanged.
