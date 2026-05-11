import json

with open('architecture.json', 'r') as f:
    arch = json.load(f)

for item in arch:
    deps = item.get('dependencies', [])
    if 'checkup_review_loop_python.prompt' in deps or 'agentic_checkup_python.prompt' in deps:
        print(f"Module {item['filename']} depends on them.")
