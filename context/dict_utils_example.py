import sys
import os
import json

# Add the parent directory to sys.path to allow importing the module
# This assumes the example script is running relative to the module location
# Adjust the path logic as needed for your specific project structure
current_dir = os.path.dirname(os.path.abspath(__file__))
# Assuming the module is in '../src/' relative to this example file
src_path = os.path.join(os.path.dirname(os.path.dirname(current_dir)), 'experiments', 'cloud_vs_local_fewshot_v2', 'src')
sys.path.append(src_path)

try:
    import dict_utils
except ImportError:
    # Fallback for when running in the same directory
    try:
        import dict_utils
    except ImportError:
        print("Error: Could not import 'dict_utils'. Ensure the module is in the python path.")
        sys.exit(1)

def print_header(title):
    print(f"\n{'='*20} {title} {'='*20}")

def print_json(data):
    print(json.dumps(data, indent=2))

def main():
    # 1. Deep Merge
    # Merges two dictionaries recursively. Nested dictionaries are combined rather than overwritten.
    print_header("1. Deep Merge")
    base_config = {
        "app": {
            "name": "MyApp",
            "debug": False,
            "database": {
                "host": "localhost",
                "port": 5432
            }
        },
        "users": ["admin"]
    }
    
    override_config = {
        "app": {
            "debug": True,  # Overrides base
            "database": {
                "password": "secret"  # Merges into database dict
            }
        },
        "version": "1.0.0"  # New key
    }
    
    merged = dict_utils.deep_merge(base_config, override_config)
    print("Base Config + Override Config:")
    print_json(merged)


    # 2. Flatten Dictionary
    # Converts a nested dictionary into a single level using dot notation.
    print_header("2. Flatten Dictionary")
    nested_data = {
        "user": {
            "profile": {
                "name": "John Doe",
                "settings": {
                    "theme": "dark"
                }
            },
            "id": 123
        }
    }
    
    flattened = dict_utils.flatten_dict(nested_data)
    print("Original Nested:")
    print_json(nested_data)
    print("\nFlattened (dot notation):")
    print_json(flattened)
    
    # You can also use a custom separator
    flattened_underscore = dict_utils.flatten_dict(nested_data, separator="__")
    print("\nFlattened (underscore separator):")
    print_json(flattened_underscore)


    # 3. Unflatten Dictionary
    # Reconstructs a nested dictionary from a flattened one.
    print_header("3. Unflatten Dictionary")
    flat_data = {
        "server.production.ip": "192.168.1.1",
        "server.production.active": True,
        "server.staging.ip": "10.0.0.1"
    }
    
    unflattened = dict_utils.unflatten_dict(flat_data)
    print("Original Flat:")
    print_json(flat_data)
    print("\nReconstructed Nested:")
    print_json(unflattened)


    # 4. Filter Keys
    # Selects or excludes specific keys from a dictionary.
    print_header("4. Filter Keys")
    api_response = {
        "id": 101,
        "title": "Hello World",
        "body": "Content goes here",
        "internal_id": "uuid-1234",
        "created_at": "2023-01-01"
    }
    
    # Include only specific keys
    public_fields = dict_utils.filter_keys(api_response, ["id", "title", "body"])
    print("Included Keys (id, title, body):")
    print_json(public_fields)
    
    # Exclude specific keys
    sanitized = dict_utils.filter_keys(api_response, ["internal_id"], exclude=True)
    print("\nExcluded Keys (internal_id):")
    print_json(sanitized)


    # 5. Get Nested Value
    # Safely retrieves a value from a deep structure using a path string.
    print_header("5. Get Nested Value")
    complex_data = {
        "store": {
            "book": [
                {"category": "reference", "author": "Nigel Rees", "title": "Sayings of the Century"},
                {"category": "fiction", "author": "Evelyn Waugh", "title": "Sword of Honour"}
            ],
            "bicycle": {
                "color": "red",
                "price": 19.95
            }
        }
    }
    
    # Get existing value
    bike_color = dict_utils.get_nested(complex_data, "store.bicycle.color")
    print(f"Store bicycle color: {bike_color}")
    
    # Get non-existent value with default
    bike_brand = dict_utils.get_nested(complex_data, "store.bicycle.brand", default="Unknown Brand")
    print(f"Store bicycle brand (defaulted): {bike_brand}")
    
    # Deep path that doesn't exist
    missing_path = dict_utils.get_nested(complex_data, "store.electronics.tv")
    print(f"Missing path result: {missing_path}")

if __name__ == "__main__":
    main()