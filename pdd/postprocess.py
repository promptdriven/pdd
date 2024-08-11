from get_comment import get_comment
from comment_line import comment_line
from find_section import find_section

def postprocess(llm_output: str, language: str) -> str:
    comment_char = get_comment(language)
    lines = llm_output.splitlines()
    sections = find_section(lines)

    # Find the largest section of the specified language
    largest_section = None
    max_size = 0
    for code_lang, start, end in sections:
        if code_lang.lower() == language.lower():
            size = end - start + 1
            if size > max_size:
                max_size = size
                largest_section = (start, end)

    processed_lines = []
    in_largest_section = False
    for i, line in enumerate(lines):
        if largest_section and i == largest_section[0] + 1:# - 1:  # Start of largest code block
            in_largest_section = True
        elif largest_section and i == largest_section[1]:# + 1:  # End of largest code block
            in_largest_section = False

        if in_largest_section:
            processed_lines.append(line)
        else:
            processed_lines.append(comment_line(line, comment_char))

    return '\n'.join(processed_lines)