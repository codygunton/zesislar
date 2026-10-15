# Native trace

Trace completeness: true.

Proof closure: true.

## identity

```
{
  "root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "source": "Fixture.v",
  "source_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "statement_sha256": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
  "switches": {
    "actual_instances": [
      "ReturnRoute.enabled"
    ],
    "requested": [
      "ReturnRoute"
    ]
  }
}
```

## session

```
{
  "id": "trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6",
  "runtime": "evidence/SESSION.json#/ownership/pet"
}
```

## pet_start_tick

```
"evidence/SESSION.json#/ownership/pet/start_ticks"
```

## request

```
{
  "block_pc": "0x1000",
  "rule_set": [
    {
      "enabled": true,
      "name": "ReturnRoute"
    }
  ],
  "scope": {
    "root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "source": "Fixture.v",
    "source_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "statement_sha256": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
  },
  "stop": {
    "kind": "rule",
    "value": "ReturnRoute"
  }
}
```

## coverage

```
{
  "captured_events": {
    "ReturnRoute": 1
  },
  "entry_events": {
    "ReturnRoute": 1
  },
  "missing_event_ids": [],
  "requested_trigger": "occurred",
  "requested_trigger_instruction_list": [
    {
      "kind": "jalr",
      "program_counter": "0x1000"
    }
  ],
  "required_complete": true,
  "traversal": "proof-closed",
  "unobserved_regions": []
}
```

## instruction_visits

```
[
  {
    "kind": "jalr",
    "program_counter": "0x1000"
  }
]
```

## snapshots

```
{
  "entry": {
    "completeness": {
      "hidden_frames_required": false,
      "missing_observations": [],
      "required_fields_complete": true
    },
    "current_goals": [
      {
        "goal": "LiTactic (normalize_instr_addr target) continuation",
        "goal_nonotation": "LiTactic (normalize_instr_addr target) continuation",
        "hyps": [
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "target"
            ],
            "type": "bv 64",
            "type_nonotation": "bv 64"
          },
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "Halign"
            ],
            "type": "bv_unsigned target mod 4 = 0",
            "type_nonotation": "bv_unsigned target mod 4 = 0"
          }
        ]
      }
    ],
    "evars": {
      "availability": "complete",
      "entries": [
        {
          "body": null,
          "body_nonotation": null,
          "context": [
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "target"
              ],
              "type": "bv 64",
              "type_nonotation": "bv 64"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "Halign"
              ],
              "type": "bv_unsigned target mod 4 = 0",
              "type_nonotation": "bv_unsigned target mod 4 = 0"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "LiTactic (normalize_instr_addr target) continuation",
          "type_nonotation": "LiTactic (normalize_instr_addr target) continuation"
        },
        {
          "body": "S n",
          "body_nonotation": "S n",
          "context": [
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "n"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            }
          ],
          "id": "?defined19",
          "status": "defined",
          "type": "nat",
          "type_nonotation": "nat"
        }
      ],
      "show_existentials": "Existential 17 remains open.\nExistential 19 := S n.\n"
    },
    "given_up": [],
    "goal": "LiTactic (normalize_instr_addr target) continuation",
    "goal_nonotation": "LiTactic (normalize_instr_addr target) continuation",
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "target"
        ],
        "type": "bv 64",
        "type_nonotation": "bv 64"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Halign"
        ],
        "type": "bv_unsigned target mod 4 = 0",
        "type_nonotation": "bv_unsigned target mod 4 = 0"
      }
    ],
    "session_id": "trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6",
    "shelf": []
  },
  "trial": {
    "completeness": {
      "hidden_frames_required": false,
      "missing_observations": [],
      "required_fields_complete": true
    },
    "current_goals": [],
    "evars": {
      "availability": "complete",
      "entries": [
        {
          "body": null,
          "body_nonotation": null,
          "context": [
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "target"
              ],
              "type": "bv 64",
              "type_nonotation": "bv 64"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "Halign"
              ],
              "type": "bv_unsigned target mod 4 = 0",
              "type_nonotation": "bv_unsigned target mod 4 = 0"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "LiTactic (normalize_instr_addr target) continuation",
          "type_nonotation": "LiTactic (normalize_instr_addr target) continuation"
        },
        {
          "body": "S n",
          "body_nonotation": "S n",
          "context": [
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "n"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            }
          ],
          "id": "?defined19",
          "status": "defined",
          "type": "nat",
          "type_nonotation": "nat"
        }
      ],
      "show_existentials": "Existential 17 remains open.\nExistential 19 := S n.\n"
    },
    "given_up": [],
    "goal": null,
    "goal_nonotation": null,
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [],
    "session_id": "trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6",
    "shelf": []
  }
}
```

## completion

```
{
  "closure_check": {
    "accepted": true,
    "command": "Qed.",
    "unresolved_evars": false
  },
  "final_obligations": {
    "availability": "complete",
    "counts": {
      "given_up": 0,
      "goals": 0,
      "shelf": 0,
      "stack": 0
    },
    "evidence": "evidence/SESSION.json#/final_snapshot",
    "session": "trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6",
    "undefined_evars": 0
  },
  "proof_closed": true,
  "reasons": [],
  "trace_complete": true
}
```

## verdict

```
{
  "evidence": "#/completion/closure_check",
  "kind": "proof_closure",
  "reason": "The owned session accepted Qed.",
  "scope": "whole-proof",
  "session": "trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6",
  "status": "actual-success"
}
```

## points/0

### id

TRACE.json#/points/0/id

```
point-0000
```

### session_id

TRACE.json#/points/0/session_id

```
trace-session-45aa0f60fc7768503a7fe7902bd41a5bb80b54b67fa923a882626f4d96c289a6
```

### trigger

TRACE.json#/points/0/trigger

```
{
  "branch": "native/0",
  "entry": "existing_ReturnRoute",
  "kind": "rule-entry",
  "matches_stop": true,
  "ordinal": 0,
  "program_counter": "0x1000",
  "rule": "ReturnRoute"
}
```

### goal

TRACE.json#/points/0/goal

```
LiTactic (normalize_instr_addr target) continuation
```

### goal_nonotation

TRACE.json#/points/0/goal_nonotation

```
LiTactic (normalize_instr_addr target) continuation
```

### hyps

TRACE.json#/points/0/hyps

```
[
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "target"
    ],
    "type": "bv 64",
    "type_nonotation": "bv 64"
  },
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "Halign"
    ],
    "type": "bv_unsigned target mod 4 = 0",
    "type_nonotation": "bv_unsigned target mod 4 = 0"
  }
]
```

### evars

TRACE.json#/points/0/evars

```
{
  "availability": "complete",
  "entries": [
    {
      "body": null,
      "body_nonotation": null,
      "context": [
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "target"
          ],
          "type": "bv 64",
          "type_nonotation": "bv 64"
        },
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "Halign"
          ],
          "type": "bv_unsigned target mod 4 = 0",
          "type_nonotation": "bv_unsigned target mod 4 = 0"
        }
      ],
      "id": "?goal17",
      "status": "undefined",
      "type": "LiTactic (normalize_instr_addr target) continuation",
      "type_nonotation": "LiTactic (normalize_instr_addr target) continuation"
    },
    {
      "body": "S n",
      "body_nonotation": "S n",
      "context": [
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "n"
          ],
          "type": "nat",
          "type_nonotation": "nat"
        }
      ],
      "id": "?defined19",
      "status": "defined",
      "type": "nat",
      "type_nonotation": "nat"
    }
  ],
  "show_existentials": "Existential 17 remains open.\nExistential 19 := S n.\n"
}
```

### hint_log

TRACE.json#/points/0/hint_log

```
{
  "availability": "complete",
  "events": [
    "entry ReturnRoute",
    "trial logging suppressed"
  ],
  "filter": [
    "ReturnRoute"
  ]
}
```

### hand_call

TRACE.json#/points/0/hand_call

```
[
  {
    "after_trial": "trial",
    "before": "entry",
    "clause": null,
    "command": "existing_ReturnRoute.",
    "commands": [
      {
        "after": "#/snapshots/trial",
        "before": "#/snapshots/entry",
        "command": "existing_ReturnRoute.",
        "outcome": "accepted",
        "refusal": null
      }
    ],
    "feedback": "advanced",
    "outcome": "accepted",
    "rollback": "entry",
    "rollback_equal": true
  }
]
```

### refusal

TRACE.json#/points/0/refusal

```
[]
```

### current_goals

TRACE.json#/points/0/current_goals

```
[
  {
    "goal": "LiTactic (normalize_instr_addr target) continuation",
    "goal_nonotation": "LiTactic (normalize_instr_addr target) continuation",
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "target"
        ],
        "type": "bv 64",
        "type_nonotation": "bv 64"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Halign"
        ],
        "type": "bv_unsigned target mod 4 = 0",
        "type_nonotation": "bv_unsigned target mod 4 = 0"
      }
    ]
  }
]
```

### shelf

TRACE.json#/points/0/shelf

```
[]
```

### given_up

TRACE.json#/points/0/given_up

```
[]
```

### hidden_focus_frames

TRACE.json#/points/0/hidden_focus_frames

```
{
  "availability": "unavailable",
  "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
}
```

### completeness

TRACE.json#/points/0/completeness

```
{
  "hidden_frames_required": false,
  "missing_observations": [],
  "required_fields_complete": true
}
```

## residual

No residual capture is present. See the completion record.
