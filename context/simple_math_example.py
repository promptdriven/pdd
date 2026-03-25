# Assuming the test module is saved as 'test_add.py' and 'solution.py' contains:
# def add(a, b):
#     return a + b

# To run the tests:
if __name__ == "__main__":
    import pytest
    pytest.main(['test_add.py', '-v'])