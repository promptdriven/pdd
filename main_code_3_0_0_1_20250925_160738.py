from module import add

def do_addition():
    # This is the fix, calling add() with two arguments.
    result = add(5, 10)
    print(f"The result is: {result}")
    # Return the result to make the function testable.
    return result

if __name__ == "__main__":
    do_addition()