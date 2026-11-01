These files supply unit tests. They never supply admission evidence.

`MANIFEST.json` records each authentic input's origin, SHA256, size, mode, and recovery source.
The `authentic` directory stores the exact bytes with deterministic gzip compression.
The fixture loader checks the original size and SHA256 before deriving a file.

Derived JSON changes typed paths and dependent container hashes.
It preserves measurements, outcomes, and source bodies.
The loader writes derived files into a private temporary directory.
Original path strings identify fixture origins. Tests do not read those original locations.

Orch authorized replacement of the lost ledger fixture.
The lost SHA256 is `68c9d98f07889e777a1236ed7b0e599b81d39e9013e72158b29f9738027e0aac`.
The replacement SHA256 is `529f4cea33ec1487ea900d87f8058a1facfa4b6d9e782582642887d9d277d111`.
The replacement contains exact bytes from a locked snapshot of the real ledger.
All 25 legacy claim amounts are zero.
All 25 legacy release records match the original assertions.
The derived ledger relocates only those consumed release records.
Other ledger records remain unchanged.

The manifest records this explicit replacement separately from authentic hashes.
The dependency hash index maps the lost reference to the approved replacement.
The replacement does not claim the lost file's hash.

The Evidence tests use the same authentic bundle.
The test helper copies current tracked Evidence sources into a separate derived repository.
It copies source bodies and statement files exactly.
It preserves existing missing-history statuses and their hashes.
The `.worktrees` directory component preserves the production historical-file checks.
The restored reports and kernel exports match their original ledger hashes.
The release backup lacked the remaining-sites report.
Its exact local archive copy supplies the authentic bytes.
