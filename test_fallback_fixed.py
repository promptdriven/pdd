from module import add

def do_addition():
    result = add(5) # This is the bug, should be add(5, 10)
    print(f"The result is: {result}")

if __name__ == "__main__":
    do_addition()
