from pdd.get_comment import get_comment
from pdd.comment_line import comment_line

def find_section(lines, start_index=0, sub_section=False):
    sections = []
    i = start_index
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith('```'):
            # Start of a code block
            if len(line) > 3:
                # Extract the language from the line
                code_language = line[3:].strip()
                start_line = i
                i += 1
                # Find the end of the code block
                while i < len(lines) and not lines[i].strip().startswith('```'):
                    i += 1
                if i < len(lines):
                    end_line = i
                    if not sub_section:
                        sections.append((code_language, start_line, end_line))
                    else:
                        return []
            else:
                # End of a code block without a language
                if sub_section:
                    return []
        i += 1
    return sections

def postprocess(llm_output, language):
    # Step 1: Get the comment character for the specified language
    comment_characters = get_comment(language)
    
    # Step 2: Find the top-level code sections
    lines = llm_output.splitlines()
    sections = find_section(lines)
    
    # Step 3: Find the largest section of the specified file_type
    largest_section = None
    max_length = 0
    for section in sections:
        code_language, start_line, end_line = section
        if code_language.lower() == language.lower():
            length = end_line - start_line
            if length > max_length:
                max_length = length
                largest_section = section
    
    # Step 4: Comment out all lines except the largest section
    if largest_section:
        _, start_line, end_line = largest_section
        processed_lines = []
        for i, line in enumerate(lines):
            if i < start_line or i > end_line:
                processed_lines.append(comment_line(line, comment_characters))
            else:
                processed_lines.append(line)
        return '\n'.join(processed_lines)
    
    # If no section matches the language, comment out everything
    return '\n'.join(comment_line(line, comment_characters) for line in lines)