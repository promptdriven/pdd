from construct_output_paths import construct_output_paths

# Example usage of the function
runnable_path, example_path = construct_output_paths(
    basename='context_generator',
    file_extension='.py',
    argv_output_path=None,  # Default case, no specific output path
    argv_example_output_path=None  # Default case for example output
)

print("Runnable Output Path:", runnable_path)
print("Example Output Path:", example_path)

# Additional examples with different arguments
print(construct_output_paths('context_generator', '.py', None, 'context/'))
print(construct_output_paths('context_generator', '.py', 'pdd/', 'context/'))
print(construct_output_paths('pdd', '.prompt', 'pdd/pdd_v1.py', None))
