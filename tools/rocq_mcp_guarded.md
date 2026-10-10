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
The wrapper retains the normal resource guard.
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

## Private artifact refresh

Validated issue-10 probes use 64 GiB and unlimited CPU time.
Atomic compiler admission permits at most two probes machine-wide.
Other compiler scopes use 6 GiB.
Gates exclude validated probe records only when they drain earlier work.
Probes still count toward compiler limits and memory holds.
A launch requires MemAvailable to equal its job limit plus 20 GiB or more.
The guard holds below 20 GiB available.
The guard kills at or below 10 GiB available.
A probe therefore requires 84 GiB available.
The interim used-memory policy uses launch 200 GiB, hold 215 GiB, and kill 230 GiB.
Interim controllers set at most six compiler slots after environment cleaning.
The guard binds each probe tag to its reservation owner and scope.

Use this command for one target before a new MCP session:

```sh
python3 tools/refresh_artifact.py --build-dir _build/agents/worker-name default/ZesuSsz/Automation/All.vo
```

The refresh converts default targets to source-relative Dune targets.
The private build directory receives their compiler outputs.
The refresh rejects installed artifact paths.
The refresh takes a private lock for that build directory.
It does not request a global gate.
It checks workspace Pets before the lock and inside the lock.
A Pet in an independent workspace does not block the refresh.
It releases the private lock when admission changes.
The normal batch guard checks memory, compiler slots, and actual gate holds.
The root, child, and preview gate classes remain unchanged.
Use the full Make lock for project gates.
