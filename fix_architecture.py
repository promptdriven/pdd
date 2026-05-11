import json
import os
import glob

with open('architecture.json', 'r') as f:
    arch = json.load(f)

# Find all files to help update filepaths
all_files = glob.glob('**/*', recursive=True)
all_files = [f for f in all_files if os.path.isfile(f)]
basename_to_paths = {}
for f in all_files:
    bn = os.path.basename(f)
    if bn not in basename_to_paths:
        basename_to_paths[bn] = []
    basename_to_paths[bn].append(f)

new_arch = []
for node in arch:
    fp = node.get('filepath')
    if fp and os.path.exists(fp):
        # Keep it
        new_arch.append(node)
        continue
    
    # Try to find it by basename
    bn = os.path.basename(fp) if fp else None
    if bn and bn in basename_to_paths and len(basename_to_paths[bn]) == 1:
        # Update filepath
        node['filepath'] = basename_to_paths[bn][0]
        new_arch.append(node)
        continue
        
    # Also check if filename (prompt file) exists. If it exists but target file doesn't, maybe we should still drop it? 
    # The instruction says "Remove or update the dead entries ... that do not exist on disk (e.g. resurface_check.py, prompts/agentic_bug_step4_reproduce_LLM.prompt, etc.)"
    # So we remove it.
    print(f"Removing dead entry: {fp} (Prompt: {node.get('filename')})")

# Fix signatures
for node in new_arch:
    functions = node.get('interface', {}).get('module', {}).get('functions', [])
    for func in functions:
        if func.get('name') == 'getPromptTemplate' and func.get('signature') == '(name: string, language: string, description?: string)':
            func['signature'] = '(name: string, language: string, description: string = None)'
            print("Fixed getPromptTemplate signature")
        if func.get('name') == 'Job' and func.get('signature') == '(id, command, args, options, status, result, error, cost, ...)':
            func['signature'] = '(id, command, args, options, status, result, error, cost, live_stdout, live_stderr)'
            print("Fixed Job signature")

with open('architecture.json', 'w') as f:
    json.dump(new_arch, f, indent=2)
