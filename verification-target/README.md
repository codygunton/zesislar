# Verification target

Run `make target-source` from the repository root.
The command creates `verification-target/zesu` as a link to the pinned Nix source.

Git ignores the link. Nix builds the ELF and the instruction dump from the same source pin.
