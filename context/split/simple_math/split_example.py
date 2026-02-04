# Placeholder for split command example script 

import split_script

try:
    result = split_script.add(10, 20)
    print(f"The sum is: {result}")
except TypeError as e:
    print(f"Error: {e}")

try:
    result = split_script.add(5, "x")
    print(f"The sum is: {result}")
except TypeError as e:
    print(f"Error: {e}") 