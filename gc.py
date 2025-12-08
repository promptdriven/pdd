import os
import csv
from typing import Optional

def get_comment(language: str) -> str:
    """
    Retrieves the comment character(s) for a given programming language by looking up
    a CSV configuration file.

    The function expects an environment variable PDD_PATH to be set, pointing to the
    root directory where data/language_format.csv is located.

    Args:
        language (str): The name of the programming language (e.g., 'Python', 'Java').

    Returns:
        str: The comment character(s) for the language. Returns 'del' if the language
             is not found, the comment field is empty, or the file cannot be accessed.
    """
    # Step 1: Load environment variables PDD_PATH
    pdd_path = os.environ.get('PDD_PATH')
    
    if not pdd_path:
        # If the environment variable isn't set, we can't find the file.
        # Returning 'del' as a safe fallback for "not found/invalid".
        return 'del'

    csv_file_path = os.path.join(pdd_path, 'data', 'language_format.csv')

    # Step 2: Lower case the language string for case-insensitive comparison
    target_language = language.lower().strip()

    try:
        with open(csv_file_path, mode='r', encoding='utf-8') as csvfile:
            reader = csv.DictReader(csvfile)
            
            # Step 3: Look up the comment character(s) for the given language
            for row in reader:
                # Ensure we are comparing lowercased versions
                current_lang = row.get('language', '').lower().strip()
                
                if current_lang == target_language:
                    comment_char = row.get('comment', '').strip()
                    
                    # Step 4: Check validity. If empty, return 'del', else return char.
                    if comment_char:
                        return comment_char
                    else:
                        return 'del'
                        
    except FileNotFoundError:
        # If the CSV file doesn't exist, treat as language not found
        return 'del'
    except Exception:
        # Catch-all for other IO errors or CSV parsing issues
        return 'del'

    # If the loop finishes without finding the language
    return 'del'# Example usage (commented out to prevent execution during import):
# if __name__ == "__main__":
#     # Mocking the environment variable and file creation for demonstration purposes
#     # In a real scenario, ensure PDD_PATH is set in your environment.
#     import tempfile
# 
#     with tempfile.TemporaryDirectory() as tmpdirname:
#         os.environ['PDD_PATH'] = tmpdirname
#         os.makedirs(os.path.join(tmpdirname, 'data'), exist_ok=True)
#         
#         csv_content = "language,comment,extension\nPython,#,.py\nJava,//,.java\nHTML,<!-- -->,.html\nUnknown,,"
#         with open(os.path.join(tmpdirname, 'data', 'language_format.csv'), 'w') as f:
#             f.write(csv_content)
# 
#         print(f"Python comment: {get_comment('Python')}")   # Output: #
#         print(f"Java comment: {get_comment('java')}")       # Output: //
#         print(f"HTML comment: {get_comment('HTML')}")       # Output: <!-- -->
#         print(f"Rust comment: {get_comment('Rust')}")       # Output: del (not in CSV)
#         print(f"Unknown comment: {get_comment('Unknown')}") # Output: del (empty comment field)