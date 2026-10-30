# Phone and server
Owner: the plan run (changes go through a plan PR).

### order_in
```json
{"type": "object", "properties": {"drink": {"type": "string"}, "size": {"type": "string", "enum": ["S", "M", "L"]}}, "required": ["drink", "size"], "additionalProperties": false}
```

### order_view
```json
{"type": "object", "properties": {"id": {"type": "string"}, "status": {"type": "string", "enum": ["Ordered", "Ready", "Refused"]}, "reason": {"oneOf": [{"type": "string"}, {"type": "null"}]}}, "required": ["id", "status", "reason"], "additionalProperties": false}
```
