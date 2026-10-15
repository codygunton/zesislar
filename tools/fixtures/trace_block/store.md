# Native trace

Trace completeness: true.

Proof closure: false.

## identity

```
{
  "root": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "source": "Fixture.v",
  "source_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "statement_sha256": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
  "switches": {
    "actual_instances": [
      "MemoryAccess.enabled"
    ],
    "requested": [
      "MemoryAccess"
    ]
  }
}
```

## session

```
{
  "id": "trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61",
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
      "name": "MemoryAccess"
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
    "value": "MemoryAccess"
  }
}
```

## coverage

```
{
  "captured_events": {
    "MemoryAccess": 1
  },
  "entry_events": {
    "MemoryAccess": 1
  },
  "missing_event_ids": [],
  "requested_trigger": "occurred",
  "requested_trigger_instruction_list": [
    {
      "kind": "WriteMem",
      "program_counter": "0x1000"
    }
  ],
  "required_complete": true,
  "traversal": "first-residual",
  "unobserved_regions": []
}
```

## instruction_visits

```
[
  {
    "kind": "WriteMem",
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
        "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
        "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
        "hyps": [
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "base"
            ],
            "type": "Z",
            "type_nonotation": "Z"
          },
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "bytes"
            ],
            "type": "list byte",
            "type_nonotation": "list byte"
          },
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "Hextent"
            ],
            "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
            "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
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
                "base"
              ],
              "type": "Z",
              "type_nonotation": "Z"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "bytes"
              ],
              "type": "list byte",
              "type_nonotation": "list byte"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "Hextent"
              ],
              "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
              "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
          "type_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind"
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
    "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "base"
        ],
        "type": "Z",
        "type_nonotation": "Z"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "bytes"
        ],
        "type": "list byte",
        "type_nonotation": "list byte"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Hextent"
        ],
        "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
        "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
      }
    ],
    "session_id": "trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61",
    "shelf": []
  },
  "trial": {
    "completeness": {
      "hidden_frames_required": false,
      "missing_observations": [],
      "required_fields_complete": true
    },
    "current_goals": [
      {
        "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
        "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
        "hyps": [
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "base"
            ],
            "type": "Z",
            "type_nonotation": "Z"
          },
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "bytes"
            ],
            "type": "list byte",
            "type_nonotation": "list byte"
          },
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "Hextent"
            ],
            "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
            "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
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
                "base"
              ],
              "type": "Z",
              "type_nonotation": "Z"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "bytes"
              ],
              "type": "list byte",
              "type_nonotation": "list byte"
            },
            {
              "body": null,
              "body_nonotation": null,
              "names": [
                "Hextent"
              ],
              "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
              "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
          "type_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind"
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
    "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "base"
        ],
        "type": "Z",
        "type_nonotation": "Z"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "bytes"
        ],
        "type": "list byte",
        "type_nonotation": "list byte"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Hextent"
        ],
        "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
        "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
      }
    ],
    "session_id": "trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61",
    "shelf": []
  }
}
```

## completion

```
{
  "proof_closed": false,
  "reasons": [],
  "trace_complete": true
}
```

## verdict

```
{
  "evidence": null,
  "kind": null,
  "reason": "No terminal named-rule evidence, accepted Qed, or unsatisfiability certificate was established.",
  "scope": "session",
  "session": "trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61",
  "status": "unresolved"
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
trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61
```

### trigger

TRACE.json#/points/0/trigger

```
{
  "branch": "native/0",
  "entry": "existing_MemoryAccess",
  "kind": "rule-entry",
  "matches_stop": true,
  "ordinal": 0,
  "program_counter": "0x1000",
  "rule": "MemoryAccess"
}
```

### goal

TRACE.json#/points/0/goal

```
find_in_context (FindMemMapsTo (base + 32)) ?kind
```

### goal_nonotation

TRACE.json#/points/0/goal_nonotation

```
find_in_context (FindMemMapsTo (base + 32)) ?kind
```

### hyps

TRACE.json#/points/0/hyps

```
[
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "base"
    ],
    "type": "Z",
    "type_nonotation": "Z"
  },
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "bytes"
    ],
    "type": "list byte",
    "type_nonotation": "list byte"
  },
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "Hextent"
    ],
    "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
    "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
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
            "base"
          ],
          "type": "Z",
          "type_nonotation": "Z"
        },
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "bytes"
          ],
          "type": "list byte",
          "type_nonotation": "list byte"
        },
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "Hextent"
          ],
          "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
          "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
        }
      ],
      "id": "?goal17",
      "status": "undefined",
      "type": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
      "type_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind"
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
    "entry MemoryAccess",
    "trial logging suppressed"
  ],
  "filter": [
    "MemoryAccess"
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
    "clause": "owned-array",
    "command": "existing_MemoryAccess.",
    "commands": [
      {
        "after": "#/snapshots/trial",
        "before": "#/snapshots/entry",
        "command": "existing_MemoryAccess.",
        "outcome": "refused",
        "refusal": "The complete extent fact is absent."
      }
    ],
    "feedback": "The complete extent fact is absent.",
    "outcome": "refused",
    "rollback": "entry",
    "rollback_equal": true
  }
]
```

### refusal

TRACE.json#/points/0/refusal

```
[
  {
    "clause": "owned-array",
    "exposure": "exposed",
    "hand_call_index": 0,
    "message": "The complete extent fact is absent."
  }
]
```

### current_goals

TRACE.json#/points/0/current_goals

```
[
  {
    "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "base"
        ],
        "type": "Z",
        "type_nonotation": "Z"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "bytes"
        ],
        "type": "list byte",
        "type_nonotation": "list byte"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Hextent"
        ],
        "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
        "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
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

### session_id

TRACE.json#/residual/session_id

```
trace-session-df11591559bc54dc5a300c9f61b1160d0a633a72e77ac5b69c45cbe04df40f61
```

### trigger

TRACE.json#/residual/trigger

```
{
  "branch": "native/0",
  "entry": "existing_MemoryAccess",
  "kind": "residual",
  "matches_stop": false,
  "ordinal": 1,
  "program_counter": "0x1000",
  "rule": "MemoryAccess"
}
```

### goal

TRACE.json#/residual/goal

```
find_in_context (FindMemMapsTo (base + 32)) ?kind
```

### goal_nonotation

TRACE.json#/residual/goal_nonotation

```
find_in_context (FindMemMapsTo (base + 32)) ?kind
```

### hyps

TRACE.json#/residual/hyps

```
[
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "base"
    ],
    "type": "Z",
    "type_nonotation": "Z"
  },
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "bytes"
    ],
    "type": "list byte",
    "type_nonotation": "list byte"
  },
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "Hextent"
    ],
    "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
    "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
  }
]
```

### evars

TRACE.json#/residual/evars

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
            "base"
          ],
          "type": "Z",
          "type_nonotation": "Z"
        },
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "bytes"
          ],
          "type": "list byte",
          "type_nonotation": "list byte"
        },
        {
          "body": null,
          "body_nonotation": null,
          "names": [
            "Hextent"
          ],
          "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
          "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
        }
      ],
      "id": "?goal17",
      "status": "undefined",
      "type": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
      "type_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind"
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

TRACE.json#/residual/hint_log

```
{
  "availability": "complete",
  "events": [
    "entry MemoryAccess",
    "trial logging suppressed"
  ],
  "filter": [
    "MemoryAccess"
  ]
}
```

### hand_call

TRACE.json#/residual/hand_call

```
[]
```

### refusal

TRACE.json#/residual/refusal

```
[]
```

### current_goals

TRACE.json#/residual/current_goals

```
[
  {
    "goal": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "goal_nonotation": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "base"
        ],
        "type": "Z",
        "type_nonotation": "Z"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "bytes"
        ],
        "type": "list byte",
        "type_nonotation": "list byte"
      },
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "Hextent"
        ],
        "type": "0 <= base /\\ base + 40 <= 2 ^ 64",
        "type_nonotation": "0 <= base /\\ base + 40 <= 2 ^ 64"
      }
    ]
  }
]
```

### shelf

TRACE.json#/residual/shelf

```
[]
```

### given_up

TRACE.json#/residual/given_up

```
[]
```

### hidden_focus_frames

TRACE.json#/residual/hidden_focus_frames

```
{
  "availability": "unavailable",
  "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
}
```

### completeness

TRACE.json#/residual/completeness

```
{
  "hidden_frames_required": false,
  "missing_observations": [],
  "required_fields_complete": true
}
```

### show_proof

TRACE.json#/residual/show_proof

```
{
  "availability": "complete",
  "text": "fun n => ?goal17\n"
}
```
