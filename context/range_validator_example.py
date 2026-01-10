import sys
import os

# Add the src directory to the python path so we can import the module
# This assumes the example is running from a directory relative to the src folder
# Adjust the relative path ('../experiments/cloud_vs_local_fewshot_v2/src') as needed for your structure
current_dir = os.path.dirname(os.path.abspath(__file__))
src_path = os.path.abspath(os.path.join(current_dir, "../../experiments/cloud_vs_local_fewshot_v2/src"))
sys.path.append(src_path)

try:
    import range_validator
except ImportError:
    print(f"Error: Could not import 'range_validator'. Checked path: {src_path}")
    sys.exit(1)

def main():
    """Demonstrates the usage of the range_validator module functions."""
    print("=== Range Validator Module Example ===\n")

    # 1. Checking if a value is within a range
    print("--- 1. is_in_range ---")
    val = 5.5
    min_v, max_v = 0.0, 10.0
    
    # Inclusive check [0, 10]
    result_inc = range_validator.is_in_range(val, min_v, max_v, inclusive=True)
    print(f"Is {val} in [{min_v}, {max_v}]? {result_inc}")

    # Exclusive check (0, 10)
    edge_val = 10.0
    result_exc = range_validator.is_in_range(edge_val, min_v, max_v, inclusive=False)
    print(f"Is {edge_val} in ({min_v}, {max_v})? {result_exc}")
    
    try:
        # This is expected to fail if the module validates that min < max
        range_validator.is_in_range(5, 10, 0) 
    except ValueError as e:
        print(f"Error caught: {e}")

    # 2. Normalizing values (Linear Mapping)
    print("\n--- 2. normalize_to_range ---")
    # Map a sensor reading (0-1023) to a percentage (0.0-1.0)
    sensor_val = 512
    normalized = range_validator.normalize_to_range(sensor_val, 0, 1023, 0.0, 1.0)
    print(f"Sensor value {sensor_val} (0-1023) -> {normalized:.4f} (0.0-1.0)")

    # Map temperature Celsius (0-100) to Fahrenheit (32-212)
    temp_c = 25
    temp_f = range_validator.normalize_to_range(temp_c, 0, 100, 32, 212)
    print(f"{temp_c}°C mapped to Fahrenheit range: {temp_f}°F")

    # 3. Wrapping values (Modular Arithmetic)
    print("\n--- 3. wrap_to_range ---")
    # Useful for angles (0-360 degrees)
    angle = 370.0
    wrapped_angle = range_validator.wrap_to_range(angle, 0.0, 360.0)
    print(f"Angle {angle} wrapped to [0, 360): {wrapped_angle}")

    negative_angle = -45.0
    wrapped_neg = range_validator.wrap_to_range(negative_angle, 0.0, 360.0)
    print(f"Angle {negative_angle} wrapped to [0, 360): {wrapped_neg}")

    # 4. Quantizing (Snapping to Grid)
    print("\n--- 4. quantize ---")
    raw_price = 12.37
    step = 0.25
    
    # Round to nearest quarter
    q_round = range_validator.quantize(raw_price, step, mode="round")
    print(f"Value {raw_price} rounded to nearest {step}: {q_round}")

    # Floor to nearest quarter
    q_floor = range_validator.quantize(raw_price, step, mode="floor")
    print(f"Value {raw_price} floored to nearest {step}: {q_floor}")

    # Ceiling to nearest quarter
    q_ceil = range_validator.quantize(raw_price, step, mode="ceil")
    print(f"Value {raw_price} ceiled to nearest {step}: {q_ceil}")

if __name__ == "__main__":
    main()