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
                    if sub_section:
                        return [], i
                    sections.append((lang, start_line, i))
                    break
                elif lines[i].strip().startswith("```"):
                    sub_sections, i = find_section(lines, i, True)
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
    
    relevant_sections = [s for s in sections if s[0].lower() == file_type.lower()]
    if not relevant_sections:
        return comment_char + "\n" + comment_char.join(lines)
    
    largest_section = max(relevant_sections, key=lambda x: x[2] - x[1])
    
    processed_lines = []
    for i, line in enumerate(lines):
        if i == largest_section[1] or i == largest_section[2]:
            processed_lines.append(comment_char + " " + line)
        elif i > largest_section[1] and i < largest_section[2]:
            processed_lines.append(line)
        else:
            processed_lines.append(comment_char + " " + line if line.strip() else line)
    
    return "\n".join(processed_lines)