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
      "ConjunctMatch.enabled"
    ],
    "requested": [
      "ConjunctMatch"
    ]
  }
}
```

## session

```
{
  "id": "trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a",
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
      "name": "ConjunctMatch"
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
    "value": "ConjunctMatch"
  }
}
```

## coverage

```
{
  "captured_events": {
    "ConjunctMatch": 1
  },
  "entry_events": {
    "ConjunctMatch": 1
  },
  "missing_event_ids": [],
  "requested_trigger": "occurred",
  "requested_trigger_instruction_list": [
    {
      "kind": "entry",
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
    "kind": "entry",
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
        "goal": "exists n : nat, key n /\\ n = cached",
        "goal_nonotation": "exists n : nat, key n /\\ n = cached",
        "hyps": [
          {
            "body": null,
            "body_nonotation": null,
            "names": [
              "n"
            ],
            "type": "nat",
            "type_nonotation": "nat"
          },
          {
            "body": "S n",
            "body_nonotation": "S n",
            "names": [
              "cached"
            ],
            "type": "nat",
            "type_nonotation": "nat"
          }
        ]
      },
      {
        "goal": "True",
        "goal_nonotation": "True",
        "hyps": []
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
                "n"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            },
            {
              "body": "S n",
              "body_nonotation": "S n",
              "names": [
                "cached"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "exists n : nat, key n /\\ n = cached",
          "type_nonotation": "exists n : nat, key n /\\ n = cached"
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
    "goal": "exists n : nat, key n /\\ n = cached",
    "goal_nonotation": "exists n : nat, key n /\\ n = cached",
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "n"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      },
      {
        "body": "S n",
        "body_nonotation": "S n",
        "names": [
          "cached"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      }
    ],
    "session_id": "trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a",
    "shelf": [
      {
        "goal": "nat",
        "goal_nonotation": "nat",
        "hyps": []
      }
    ]
  },
  "trial": {
    "completeness": {
      "hidden_frames_required": false,
      "missing_observations": [],
      "required_fields_complete": true
    },
    "current_goals": [
      {
        "goal": "True",
        "goal_nonotation": "True",
        "hyps": []
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
                "n"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            },
            {
              "body": "S n",
              "body_nonotation": "S n",
              "names": [
                "cached"
              ],
              "type": "nat",
              "type_nonotation": "nat"
            }
          ],
          "id": "?goal17",
          "status": "undefined",
          "type": "exists n : nat, key n /\\ n = cached",
          "type_nonotation": "exists n : nat, key n /\\ n = cached"
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
    "goal": "True",
    "goal_nonotation": "True",
    "hidden_focus_frames": {
      "availability": "unavailable",
      "reason": "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. The public observer API does not expose those ordered frames."
    },
    "hyps": [],
    "session_id": "trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a",
    "shelf": [
      {
        "goal": "nat",
        "goal_nonotation": "nat",
        "hyps": []
      }
    ]
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
  "session": "trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a",
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
trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a
```

### trigger

TRACE.json#/points/0/trigger

```
{
  "branch": "native/0",
  "entry": "existing_ConjunctMatch",
  "kind": "rule-entry",
  "matches_stop": true,
  "ordinal": 0,
  "program_counter": "0x1000",
  "rule": "ConjunctMatch"
}
```

### goal

TRACE.json#/points/0/goal

```
exists n : nat, key n /\ n = cached
```

### goal_nonotation

TRACE.json#/points/0/goal_nonotation

```
exists n : nat, key n /\ n = cached
```

### hyps

TRACE.json#/points/0/hyps

```
[
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "n"
    ],
    "type": "nat",
    "type_nonotation": "nat"
  },
  {
    "body": "S n",
    "body_nonotation": "S n",
    "names": [
      "cached"
    ],
    "type": "nat",
    "type_nonotation": "nat"
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
            "n"
          ],
          "type": "nat",
          "type_nonotation": "nat"
        },
        {
          "body": "S n",
          "body_nonotation": "S n",
          "names": [
            "cached"
          ],
          "type": "nat",
          "type_nonotation": "nat"
        }
      ],
      "id": "?goal17",
      "status": "undefined",
      "type": "exists n : nat, key n /\\ n = cached",
      "type_nonotation": "exists n : nat, key n /\\ n = cached"
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
    "entry ConjunctMatch",
    "trial logging suppressed"
  ],
  "filter": [
    "ConjunctMatch"
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
    "command": "existing_ConjunctMatch.",
    "commands": [
      {
        "after": "#/snapshots/trial",
        "before": "#/snapshots/entry",
        "command": "existing_ConjunctMatch.",
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
    "goal": "exists n : nat, key n /\\ n = cached",
    "goal_nonotation": "exists n : nat, key n /\\ n = cached",
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "n"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      },
      {
        "body": "S n",
        "body_nonotation": "S n",
        "names": [
          "cached"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      }
    ]
  },
  {
    "goal": "True",
    "goal_nonotation": "True",
    "hyps": []
  }
]
```

### shelf

TRACE.json#/points/0/shelf

```
[
  {
    "goal": "nat",
    "goal_nonotation": "nat",
    "hyps": []
  }
]
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
trace-session-cdf014675f6699e883a0c793ebba1d29bd469d7fc37718298f94184cea0c809a
```

### trigger

TRACE.json#/residual/trigger

```
{
  "branch": "native/0",
  "entry": "existing_ConjunctMatch",
  "kind": "residual",
  "matches_stop": false,
  "ordinal": 1,
  "program_counter": "0x1000",
  "rule": "ConjunctMatch"
}
```

### goal

TRACE.json#/residual/goal

```
exists n : nat, key n /\ n = cached
```

### goal_nonotation

TRACE.json#/residual/goal_nonotation

```
exists n : nat, key n /\ n = cached
```

### hyps

TRACE.json#/residual/hyps

```
[
  {
    "body": null,
    "body_nonotation": null,
    "names": [
      "n"
    ],
    "type": "nat",
    "type_nonotation": "nat"
  },
  {
    "body": "S n",
    "body_nonotation": "S n",
    "names": [
      "cached"
    ],
    "type": "nat",
    "type_nonotation": "nat"
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
            "n"
          ],
          "type": "nat",
          "type_nonotation": "nat"
        },
        {
          "body": "S n",
          "body_nonotation": "S n",
          "names": [
            "cached"
          ],
          "type": "nat",
          "type_nonotation": "nat"
        }
      ],
      "id": "?goal17",
      "status": "undefined",
      "type": "exists n : nat, key n /\\ n = cached",
      "type_nonotation": "exists n : nat, key n /\\ n = cached"
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
    "entry ConjunctMatch",
    "trial logging suppressed"
  ],
  "filter": [
    "ConjunctMatch"
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
    "goal": "exists n : nat, key n /\\ n = cached",
    "goal_nonotation": "exists n : nat, key n /\\ n = cached",
    "hyps": [
      {
        "body": null,
        "body_nonotation": null,
        "names": [
          "n"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      },
      {
        "body": "S n",
        "body_nonotation": "S n",
        "names": [
          "cached"
        ],
        "type": "nat",
        "type_nonotation": "nat"
      }
    ]
  },
  {
    "goal": "True",
    "goal_nonotation": "True",
    "hyps": []
  }
]
```

### shelf

TRACE.json#/residual/shelf

```
[
  {
    "goal": "nat",
    "goal_nonotation": "nat",
    "hyps": []
  }
]
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
