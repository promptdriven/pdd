import json
import re

with open('pdd/prompts/agentic_checkup_python.prompt', 'r') as f:
    prompt_content = f.read()

with open('interface_agentic_checkup.json', 'r') as f:
    old_interface = json.load(f)

# Extract new interface to get the updated signatures
interface_match = re.search(r'<pdd-interface>\n(.*?)\n</pdd-interface>', prompt_content, re.DOTALL)
if interface_match:
    new_interface = json.loads(interface_match.group(1))
    
    # We want to keep the new run_agentic_checkup signature, but add sideEffects and the old functions
    new_run_func = new_interface['module']['functions'][0]
    
    old_run_func = next(f for f in old_interface['module']['functions'] if f['name'] == 'run_agentic_checkup')
    new_run_func['sideEffects'] = old_run_func.get('sideEffects', ["None"])
    
    # Filter out run_agentic_checkup from old functions
    other_funcs = [f for f in old_interface['module']['functions'] if f['name'] != 'run_agentic_checkup']
    
    # Combine
    new_interface['module']['functions'] = [new_run_func] + other_funcs
    
    # Replace the json inside prompt
    new_json_str = json.dumps(new_interface, indent=2)
    prompt_content = prompt_content.replace(interface_match.group(1), new_json_str)

with open('pdd/prompts/agentic_checkup_python.prompt', 'w') as f:
    f.write(prompt_content)
