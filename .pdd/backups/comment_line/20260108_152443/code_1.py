# To achieve the functionality described, we can write a Python function `comment_line` that handles the different scenarios for commenting out a line of code based on the provided `comment_characters`. Here's how you can implement this function:

# ```python
def comment_line(code_line, comment_characters):
    # Check if the language requires deletion of the line
    if comment_characters == 'del':
        return ''
    
    # Check if the language uses separate start and end comment characters
    if ' ' in comment_characters:
        start_comment, end_comment = comment_characters.split(' ', 1)
        return f"{start_comment}{code_line}{end_comment}"
    
    # For languages with a single comment character
    return f"{comment_characters}{code_line}"

# Example usage:
# Python style comment
# print(comment_line("print('Hello World!')", "#"))  # Output: "#print('Hello World!')"

# # HTML style comment
# print(comment_line("<h1>Hello World!</h1>", "<!-- -->"))  # Output: "<!--<h1>Hello World!</h1>-->"

# # Language with no comment character (deletion)
# print(comment_line("some code", "del"))  # Output: ""
# ```

# ### Explanation:
# 1. **Deletion Case**: If `comment_characters` is `'del'`, the function returns an empty string, effectively "deleting" the line.

# 2. **Encapsulating Comments**: If `comment_characters` contains a space, it indicates that the language uses separate start and end comment characters. The function splits the string into `start_comment` and `end_comment` and returns the line encapsulated by these.

# 3. **Single Comment Character**: For languages with a single comment character (like Python's `#`), the function simply prepends the `comment_characters` to the `code_line`.

# This function should handle the specified scenarios for commenting out lines in different programming languages.