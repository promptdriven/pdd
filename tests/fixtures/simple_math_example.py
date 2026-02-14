"""Example program demonstrating usage of the simple_math module."""

from simple_math import add


def main():
    """Run example demonstrations of the add function."""
    test_cases = [(2, 3), (2.5, 3.5), (2, 3.5), (2.5, 3), (0, 0), (-5, 10), (3.14, -2.71)]
    print("Testing add() function:")
    print("-" * 40)
    for a, b in test_cases:
        result = add(a, b)
        print(f"add({a!r}, {b!r}) = {result!r}  (type: {type(result).__name__})")
    print("-" * 40)
    print("All tests completed!")


if __name__ == "__main__":
    main()
