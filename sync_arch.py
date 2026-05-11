import json
import re
import os

with open('architecture.json', 'r') as f:
    arch = json.load(f)

def extract_tags(filename):
    with open(f"pdd/prompts/{filename}", "r") as f:
        content = f.read()
    reason_match = re.search(r'<pdd-reason>(.*?)</pdd-reason>', content, re.DOTALL)
    reason = reason_match.group(1).strip() if reason_match else ""
    interface_match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', content, re.DOTALL)
    interface = json.loads(interface_match.group(1).strip()) if interface_match else {}
    deps = re.findall(r'<pdd-dependency>(.*?)</pdd-dependency>', content)
    return reason, interface, deps

for item in arch:
    if item['filename'] == 'agentic_checkup_python.prompt':
        reason, interface, deps = extract_tags('agentic_checkup_python.prompt')
        item['reason'] = reason
        item['interface'] = interface
        item['dependencies'] = deps
    elif item['filename'] == 'checkup_review_loop_python.prompt':
        reason, interface, deps = extract_tags('checkup_review_loop_python.prompt')
        item['reason'] = reason
        item['interface'] = interface
        item['dependencies'] = deps

with open('architecture.json', 'w') as f:
    json.dump(arch, f, indent=2)
