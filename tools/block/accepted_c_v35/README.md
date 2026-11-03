# Accepted C sources for v3.5

This directory transfers exact accepted sources to the release owner.
It does not install tactics or change the production import graph.
The manifest binds each file to its original source and acceptance packet.
It records shared ownership and caller-specific limits.

Run `python3 tools/block/accepted_c_v35/verify.py` to check the transferred bytes.
The release owner must compile selected sources against the release dependency closure.
Historical control aliases keep their original names and imports.
Do not globally export the diagnostic fragments.
No compiled objects are included.
