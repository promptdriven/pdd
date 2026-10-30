# Server and barista
Owner: the plan run (changes go through a plan PR).

### ticket
```json
{"type": "object", "properties": {"id": {"type": "string"}, "drink": {"type": "string"}, "size": {"type": "string", "enum": ["S", "M", "L"]}, "done": {"type": "boolean"}}, "required": ["id", "drink", "size", "done"], "additionalProperties": false}
```

### ticket_done
```json
{"type": "object", "properties": {"id": {"type": "string"}}, "required": ["id"], "additionalProperties": false}
```
