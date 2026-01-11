import sys
import os

# Add the src directory to the Python path so we can import the module
# The structure is:
#   examples/hello/src/hello.py
#   examples/hello/examples/hello_example.py
# We need to go up one level from 'examples' to 'hello', then down into 'src'
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.join(current_dir, '..', 'src')
sys.path.insert(0, src_path)

from hello import hello

def main():
    """
    Demonstrates the usage of the hello function.
    """
    print("Calling the hello function from the module:")
    
    # The hello function takes no arguments and returns None.
    # It simply prints "hello" to standard output.
    hello()


if __name__ == "__main__":
    main()