def find_section(lines, start_index=0, sub_section=False):
    sections = []
    stack = []
    
    for i, line in enumerate(lines):
        line = line.strip()
        
        if line.startswith('```'):
            if len(line) > 3:
                # Opening of a new block
                stack.append((i, line[3:].strip()))
            elif stack:
                # Closing of a block
                start, lang = stack.pop()
                if not stack:  # This is a top-level block
                    if start >= start_index:
                        if sub_section:
                            return [(lang, start, i)]
                        else:
                            sections.append((lang, start, i))

    # Handle unclosed blocks
    while stack:
        start, lang = stack.pop()
        if not stack and start >= start_index:  # This is a top-level block
            sections.append((lang, start, len(lines) - 1))
    
    return sections