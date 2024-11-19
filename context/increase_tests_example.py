from pdd.increase_tests import increase_tests

def example_usage():
    """
    Demonstrates the usage of the increase_tests function with both basic and advanced parameters.
    Handles potential errors and prints the results.
    """
    # Existing code and tests
    existing_code = """
def calculate_average(numbers):
    if not numbers:
        return 0
    return sum(numbers) / len(numbers)
    """
    
    existing_unit_tests = """
def test_calculate_average():
    assert calculate_average([1, 2, 3]) == 2
    """
    
    coverage_report = """
Name                Stmts   Miss  Cover
--------------------------------------
calculate_average.py     5      2    60%
"""
    
    original_prompt = "Write a function to calculate the average of a list of numbers"

    # Call increase_tests to generate more comprehensive tests
    try:
        # Basic usage with default parameters
        new_tests, total_cost, model_name = increase_tests(
            existing_unit_tests=existing_unit_tests,
            coverage_report=coverage_report,
            code=existing_code,
            prompt_that_generated_code=original_prompt
        )
        
        print(f"Generated Tests: {new_tests}")
        print(f"Total Cost: ${total_cost}")
        print(f"Model Used: {model_name}")
        
        # Advanced usage with custom parameters
        verbose_tests, verbose_cost, verbose_model = increase_tests(
            existing_unit_tests=existing_unit_tests,
            coverage_report=coverage_report,
            code=existing_code,
            prompt_that_generated_code=original_prompt,
            language="python",
            strength=0.7,
            temperature=0.2,
            verbose=True
        )
    
    except ValueError as ve:
        print(f"Input validation error: {ve}")
    except Exception as e:
        print(f"Unexpected error: {e}")

# Run the example
if __name__ == "__main__":
    example_usage()