# Function-text schema 2

The counter reads a committed manifest. It does not execute proof bodies.
Schema 1 keeps its historical decodeItem scope and counting rules.
Schema 2 requires an explicit `scope_id` for each function.
Comparisons with different scope identities report no delta.

Each `files` row declares:

- `path`: a tracked source path inside the tree.
- `category`: an existing function-text group.
- `scope`: `whole_file` or `mixed_file`.
- `line_ranges`: one-based inclusive ranges for a mixed file.
- `text_kind`: `hand_written`, `generated`, or `data_table`.

The counter rejects overlapping selections within one function.
The counter never selects a text kind from a filename or extension.
Each group reports all three kinds with physical and nonblank counts.
Physical counts include blank lines. Nonblank counts exclude whitespace-only lines.
Hand suffix counts retain their nonblank unit.
The scored totals exclude composition, tests, call-spec capability, and generic automation.
The primary nonblank total adds hand suffix lines to hand-written block support.
Generated support and data tables remain separate.
The physical compatibility total uses physical support lines and nonblank hand suffix lines.
This mixed historical unit remains explicit in `counting_rules`.

Per-function inventories can select shared source ranges.
The `--function all` report lists shared attribution.
Per-function totals do not define a unique project total.
The native block counter currently covers decodeItem only.
Other functions report `coverage: not_measured`.

## Generated credit

A generated row names its `generator`.
The manifest defines that generator in `generators`:

```json
{
  "support": {
    "tool": "tools/block/render_support.py",
    "command": ["python3", "tools/block/render_support.py", "--design", "design.json", "--function", "decodeItem", "--check"],
    "inputs": ["tools/block/render_support.py", "design.json"],
    "outputs": ["ZesuSsz/Generated/DecodeItem/Entries.v", "ZesuSsz/Generated/DecodeItem/Registrations.v"]
  }
}
```

The inputs must include the generator tool and every required source input.
The outputs must include each generated row.
The caller supplies `--freshness RECORD.json` after the real check succeeds.
The record has this structure:

```json
{
  "schema_version": 1,
  "tree": "exact Git tree SHA",
  "checks": {
    "support": {
      "command": ["the exact manifest command"],
      "exit_code": 0,
      "inputs": {"each declared input path": "its SHA256"},
      "outputs": {"each declared output path": "its SHA256"}
    }
  }
}
```

The counter checks the tree, command, exit code, and every declared hash.
The counter does not infer freshness from a generated header.
Without a freshness record, generated text counts as hand-written.
An invalid supplied record causes an error.
The report binds the parsed record with a canonical JSON hash.
This hash is not the hash of the original JSON file bytes.
The caller must retain the actual check log and its execution record.
The record format does not replace that execution evidence.

## Inventory-only functions

`inventory_only: true` permits a function inventory without a hint umbrella.
The hint checker still checks every declared list and Compliance source.
An existing umbrella still needs complete hint coverage.
The data-only checker still checks declarations and forbidden machine references.
The native launcher rejects `inventory_only`, even when an umbrella exists.
An ordinary manifest without an umbrella also cannot launch native proofs.
