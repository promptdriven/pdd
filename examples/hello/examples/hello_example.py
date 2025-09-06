# greeter.py

def hello() -> None:
  """Prints the string "hello" to the console.

  This function demonstrates a simple procedure with a side effect (printing)
  and no return value.
  """
  print("hello")

# main.py

# 1. Import the specific function 'hello' from the 'greeter' module (greeter.py).
from greeter import hello

def main() -> None:
  """
  Main function to demonstrate the usage of the imported 'hello' function.
  """
  print("About to call the imported function...")

  # 2. Call the function. It takes no arguments.
  #    The function will execute and print "hello" to the console.
  hello()

  print("...function call has finished.")


if __name__ == "__main__":
  main()