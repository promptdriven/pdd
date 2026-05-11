import json
import re

with open('pdd/prompts/checkup_review_loop_python.prompt', 'r') as f:
    prompt_content = f.read()

with open('interface_checkup.json', 'r') as f:
    old_interface = json.load(f)

# Extract new interface to get the updated signatures
interface_match = re.search(r'<pdd-interface>\n(.*?)\n</pdd-interface>', prompt_content, re.DOTALL)
if interface_match:
    new_interface = json.loads(interface_match.group(1))
    
    # Merge functions
    new_funcs = {f['name']: f for f in new_interface['module']['functions']}
    merged_funcs = []
    for f in old_interface['module']['functions']:
        if f['name'] in new_funcs:
            f['signature'] = new_funcs[f['name']]['signature']
        merged_funcs.append(f)
    
    old_interface['module']['functions'] = merged_funcs
    
    # Replace the json inside prompt
    new_json_str = json.dumps(old_interface, indent=2)
    prompt_content = prompt_content.replace(interface_match.group(1), new_json_str)

# Also fix Issue 4: "Add a section or requirement instructing the generation of tests that cover the primary failure fallback and the surfacing of the failure-reason in the final report."
# Let's add it to the end of "% Deliverables" or "% Goal" or as a new section.
test_requirement = """
% Tests
- Cover (a) primary failed + secondary clean → loop completes with secondary, and (b) failure-reason surfaced in the final report.
"""
if "% Deliverables" in prompt_content:
    prompt_content = prompt_content.replace("% Deliverables", test_requirement + "\n% Deliverables")

with open('pdd/prompts/checkup_review_loop_python.prompt', 'w') as f:
    f.write(prompt_content)
