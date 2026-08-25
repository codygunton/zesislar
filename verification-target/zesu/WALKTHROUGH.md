# Zesu SSZ decoder — walkthrough

Status: template. No proofs yet.

## 1. Obtain the binary

The Zesu SSZ decoder binary is built by nix in `~/binary-fv-experiment`:

```sh
cd ~/binary-fv-experiment
nix build -L .#zesuRv64Object
```

The linked ELF is the same one that `binary-fv-experiment` verifies via the Lean route.

TODO: add a make target or nix derivation that produces the ELF and copies it here.

## 2. Disassemble

```sh
make PROG=zesu disasm
```

TODO: determine the load address (check `binary-fv-experiment/runtime/riscv64/link.ld`).

## 3. Annotate the dump

Start with:
- `//@isla-config: riscv64_zesu.toml` at the top
- No per-instruction constraints initially
- Run `make trace-one OP=<first opcode>` and see what fails

The first failures will tell you what constraints are missing. Add them iteratively.

**Strategy at scale:** do not annotate the entire binary at once. Pick one function, annotate it,
generate its traces, prove its contract. Then move to the next.

## 4. Generate traces

```sh
make PROG=zesu traces
```

At 100k+ instructions this takes hours. Use `-j` for parallelism. Consider splitting the dump into
per-function chunks.

## 5. Write specs and contracts

Follow the max2 pattern from `islaris-tutorial`:
- Specification in `ZesislarProofs/Specs/`
- Contract and proof in `ZesislarProofs/Zesu/Contracts/`

Start with the simplest function in the binary — a leaf with no loops. Get it green, then scale.

## 6. Build the instruction-spec library

The 20 most common RV64IM instructions should have specs in `InstrSpecs/`. Each spec is proved once
against the Isla trace of that opcode and reused everywhere via `//@spec:` annotations.

Priority order:
1. `mv` (addi rd, rs, 0)
2. `li` (lui + addi)
3. `ld`, `sd`, `lw`, `sw`
4. `add`, `sub`, `and`, `or`, `xor`
5. `slli`, `srli`, `srai`
6. `mul`, `mulh`
