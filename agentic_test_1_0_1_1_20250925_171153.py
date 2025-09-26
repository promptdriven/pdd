# agentic_test.py

def calculate_sum(numbers):
    # Deliberate bug: This will raise a TypeError
    total = "This is not a number"
    for number in numbers:
        total += number
    return total

if __name__ == "__main__":
    my_numbers = [1, 2, 3, 4, 5]
    result = calculate_sum(my_numbers)
    print(f"The sum is: {result}")
