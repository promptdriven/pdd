import re
from typing import List, Tuple

def find_section(lines: List[str], start: int, sub_section: bool = False) -> Tuple[List[Tuple[str, int, int]], int]:
    sections = []
    i = start
    while i < len(lines):
        if lines[i].strip().startswith("```"):
            lang = lines[i].strip()[3:].strip()
            start_line = i
            i += 1
            while i < len(lines):
                if lines[i].strip() == "```":
                    sections.append((lang, start_line, i))
                    break
                i += 1
        i += 1
    return sections, i

def postprocess(llm_output: str, file_type: str) -> str:
    comment_chars = {
    "ada": "--",
    "applescript": "--",
    "assembly": ";",
    "bash": "#",
    "basic": "'",
    "batch": "REM",
    "c": "//",
    "cpp": "//",
    "csharp": "//",
    "clojure": ";",
    "cobol": "*",
    "coffeescript": "#",
    "css": "/*",
    "dart": "//",
    "delphi": "//",
    "erlang": "%",
    "fortran": "!",
    "go": "//",
    "groovy": "//",
    "haskell": "--",
    "html": "<!--",
    "java": "//",
    "javascript": "//",
    "julia": "#",
    "kotlin": "//",
    "latex": "%",
    "lisp": ";",
    "lua": "--",
    "makefile": "#",
    "matlab": "%",
    "objectivec": "//",
    "ocaml": "(*",
    "pascal": "//",
    "perl": "#",
    "php": "//",
    "powershell": "#",
    "python": "#",
    "r": "#",
    "ruby": "#",
    "rust": "//",
    "scala": "//",
    "shell": "#",
    "sql": "--",
    "swift": "//",
    "typescript": "//",
    "vbnet": "'",
    "verilog": "//",
    "vhdl": "--",
    "xml": "<!--",
    "yaml": "#"
    }
    comment_char = comment_chars.get(file_type.lower(), "#")
    
    lines = llm_output.split("\n")
    sections, _ = find_section(lines, 0)
    
    processed_lines = []
    in_code_block = False
    relevant_code = []
    
    for i, line in enumerate(lines):
        if line.strip().startswith("```"):
            if in_code_block:
                # End of a code block
                if relevant_code:
                    processed_lines.extend(relevant_code)
                    relevant_code = []
                else:
                    # If it's not a relevant code block, comment out its content
                    processed_lines.extend([comment_char + " " + l for l in lines[current_block_start+1:i]])
            else:
                # Start of a code block
                current_block_start = i
            in_code_block = not in_code_block
            processed_lines.append(comment_char + " " + line)
        elif in_code_block:
            if any(i > s[1] and i < s[2] for s in sections if s[0].lower() == file_type.lower()):
                relevant_code.append(line)
        else:
            processed_lines.append(comment_char + " " + line if line.strip() else line)
    
    # Handle any remaining relevant code after the last code block
    if relevant_code:
        processed_lines.extend(relevant_code)
    
    return "\n".join(processed_lines).strip()