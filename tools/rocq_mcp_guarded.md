# MCP writer fence

Start the unchanged MCP server through `rocq_mcp_guarded.sh` under the pinned opam switch.
The server scope limits memory to 6 GiB and disables swap.
Pet inherits that scope.
The server sets its pet watchdog to 6144 MiB.

The server uses the supported `ROCQ_COQC_BINARY` setting.
That setting names `rocq_coqc_guarded.sh`.
The compiler wrapper waits for the resource guard.
It then starts the pinned compiler in a registered 6-GiB scope.
The compiler scope disables swap.
The wrapper keeps the hold threshold at 180 GiB.
The server scope uses a separate prefix because an idle server must not block a gate.

Replace only the server executable in the existing Codex configuration:

```toml
[mcp_servers.rocq-mcp]
command = "opam"
args = ["exec", "--switch=/home/cody/islaris", "--", "/path/to/reviewed/worktree/tools/rocq_mcp_guarded.sh"]
```

Use the reviewed integration path after merge.
Restart the MCP client after this configuration change.
The wrapper does not change an existing shared server or its cgroup.
It supplies the standard user bus paths when the MCP client omits those environment variables.
It fails if systemd cannot create the scope.
It does not continue with an unlimited process.

Run the focused script tests with `python3 tools/test_rocq_guarded.py`.
The tests check the server settings, compiler routing, and health probe.
The live validation checked an inherited child limit of 6442450944 bytes and zero swap.
An isolated MCP health call resolved the pinned compiler version through the wrapper.
The initial validation did not run a proof, a gate, or an arm.
A later isolated proof test used health, start, check, step_multi, compile_file, and verify.
The proof compiled closed and verified with no assumptions.
The live pet and both compiler processes used 6-GiB cgroups with swap disabled.
No gate or arm ran.
