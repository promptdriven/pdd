import sys
import os

# Add the directory containing the module to the Python path
# This allows importing 'list_stats' even if it's in a different directory
current_dir = os.path.dirname(os.path.abspath(__file__))
# Assuming the module is in '../experiments/cloud_vs_local_fewshot_v2/src/' relative to this example
# Adjust the relative path below based on your actual project structure
module_path = os.path.abspath(os.path.join(current_dir, "../experiments/cloud_vs_local_fewshot_v2/src"))
sys.path.append(module_path)

try:
    import list_stats
except ImportError:
    # Fallback or mock for demonstration if the module is not found in the specified path
    print("Warning: list_stats module not found. Ensure the path is correct.")

def main() -> None:
    """
    Demonstrates the usage of the list_stats module functions including
    safe_mean, median, variance, and percentile.
    """
    # Sample data
    data = [10.5, 2.0, 5.5, 8.0, 2.0, 15.0]
    empty_data = []

    print(f"Dataset: {data}\n")

    # 1. Safe Mean
    # Calculates average, handles empty lists gracefully
    mean_val = list_stats.safe_mean(data)
    print(f"Mean: {mean_val:.2f}")  # Output: 7.17
    
    # Using default value for empty list
    empty_mean = list_stats.safe_mean(empty_data, default=-1.0)
    print(f"Mean of empty list (default -1.0): {empty_mean}")

    # 2. Median
    # Finds the middle value (sorts automatically)
    try:
        med_val = list_stats.median(data)
        print(f"Median: {med_val}")  # Output: 6.75 (average of 5.5 and 8.0)
    except ValueError as e:
        print(f"Median error: {e}")

    # 3. Variance
    # Calculate Population Variance (default)
    pop_var = list_stats.variance(data)
    print(f"Population Variance: {pop_var:.2f}")

    # Calculate Sample Variance (population=False)
    # Used when data is a subset of a larger population
    samp_var = list_stats.variance(data, population=False)
    print(f"Sample Variance: {samp_var:.2f}")

    # 4. Percentile
    # Calculate the 90th percentile
    try:
        p90 = list_stats.percentile(data, 90)
        print(f"90th Percentile: {p90:.2f}")
        
        # Calculate the 25th percentile (1st Quartile)
        p25 = list_stats.percentile(data, 25)
        print(f"25th Percentile: {p25:.2f}")
    except ValueError as e:
        print(f"Percentile error: {e}")

if __name__ == "__main__":
    main()