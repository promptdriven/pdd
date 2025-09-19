import json
import sys
import os

JSON_FILE_PATH = "pdd/architecture.json"

def extract_filenames_from_json_data(json_string: str) -> list:
    """
    Parses a JSON string, extracts 'filename' values from each object,
    and returns it.

    Args:
        json_string: A string containing the JSON data (read from a file).

    Returns:
        A list of filename strings, or None if an error occurs (though sys.exit is used).
    """
    filenames = []
    
    # 1) Check if the JSON string (read from file) can be parsed.
    try:
        data = json.loads(json_string)
        if not isinstance(data, list):
            print("Error: JSON data from file is not a list of objects.", file=sys.stderr)
            sys.exit(1) 
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON data in file. Details: {e}", file=sys.stderr)
        sys.exit(1)

    # 2) For every object in the JSON data, locate the value of the key "filename".
    for item in data:
        if isinstance(item, dict):
            if "filename" in item:
                filename_value = item["filename"]
                # 3) Add each filename_value to a list.
                filenames.append(filename_value)
            else:
                print(f"Warning: Object found without a 'filename' key: {item}", file=sys.stderr)
        else:
            print(f"Warning: Non-dictionary item found in JSON list: {item}", file=sys.stderr)
            
    # 4) Return the list to the caller.
    return filenames

if __name__ == "__main__":
    # 1) Check if the file <tool_ordered_json> exists.
    if not os.path.exists(JSON_FILE_PATH):
        print(f"Error: File '{JSON_FILE_PATH}' not found.", file=sys.stderr)
        sys.exit(1)

    json_file_content = ""
    try:
        with open(JSON_FILE_PATH, 'r', encoding='utf-8') as f:
            json_file_content = f.read()
    except IOError as e:
        print(f"Error: Could not read file '{JSON_FILE_PATH}'. Details: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e: # Catch any other potential errors during file read
        print(f"An unexpected error occurred while reading '{JSON_FILE_PATH}'. Details: {e}", file=sys.stderr)
        sys.exit(1)

    # Call the function with the JSON string read from the file
    extracted_list = extract_filenames_from_json_data(json_file_content)
    
    # Print the list of filenames as a single space-separated string.
    print(" ".join(extracted_list))
