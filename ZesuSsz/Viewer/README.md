# Zesislar viewer data

This directory converts Zesislar evidence into shared viewer data.
It also checks the generated profiles and proof-map payload.

Build the data with `nix build .#level1-viewer-data`.
Run the local checks with `make check-viewer`.

The application lives in `codygunton/binary-fv-viewer`.
That repository selects this Nix package through its Zesislar provider.
Contract status is review data and is not a Rocq assumption.
