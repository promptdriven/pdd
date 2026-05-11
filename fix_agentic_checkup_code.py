import os

with open('.agentic_prompt_ca484d00.txt', 'r') as f:
    prompt = f.read()

start_idx = prompt.find("<generated_code>") + len("<generated_code>\n")
end_idx = prompt.find("</generated_code>")

if start_idx != -1 and end_idx != -1:
    code = prompt[start_idx:end_idx].strip()
    if code.endswith("```"):
        code = code[:-3].strip()
    
    with open('/tmp/pdd_job_LpFrqbS7pZ0P37hf4AUP_agw_as0q/pdd/agentic_checkup.py', 'w') as f:
        f.write(code + "\n")
    print("Code extracted and saved.")
else:
    print("Could not find code boundaries.")
