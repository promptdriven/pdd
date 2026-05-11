import json

with open('architecture.json', 'r') as f:
    arch = json.load(f)

for item in arch:
    if item['filename'] in ['agentic_checkup_python.prompt', 'checkup_review_loop_python.prompt']:
        print(f"Filename: {item['filename']}")
        print(f"Dependencies: {item.get('dependencies', [])}")
        print("---")
