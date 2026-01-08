import sys
import os
import datetime

# Add the directory containing the module to the Python path
# This allows importing 'date_utils' even if it's in a different directory
# Adjust the relative path ('../experiments/cloud_vs_local_fewshot_v2/src') as needed based on your actual structure
current_dir = os.path.dirname(os.path.abspath(__file__))
module_path = os.path.join(current_dir, "../experiments/cloud_vs_local_fewshot_v2/src")
sys.path.append(module_path)

import date_utils

def main():
    print("--- Date Parsing ---")
    # 1. Parse dates with default formats
    date1 = date_utils.parse_date("2023-10-25")
    print(f"Parsed '2023-10-25': {date1} (Type: {type(date1)})")

    # 2. Parse dates with custom formats
    custom_date_str = "25.10.2023"
    date2 = date_utils.parse_date(custom_date_str, formats=["%d.%m.%Y"])
    print(f"Parsed '{custom_date_str}': {date2}")

    try:
        date_utils.parse_date("invalid-date")
    except ValueError as e:
        print(f"Error handling works: {e}")

    print("\n--- Date Formatting ---")
    # 3. Format a date object back to string
    formatted = date_utils.format_date(date1, "%A, %B %d, %Y")
    print(f"Formatted date: {formatted}")

    print("\n--- Age Calculation ---")
    # 4. Calculate age
    birth_date = datetime.date(1990, 5, 15)
    age = date_utils.calculate_age(birth_date)
    print(f"Born {birth_date}: {age} years old today")

    # Calculate age at a specific reference date
    past_date = datetime.date(2000, 1, 1)
    age_at_y2k = date_utils.calculate_age(birth_date, reference_date=past_date)
    print(f"Age at Y2K ({past_date}): {age_at_y2k}")

    print("\n--- Date Math ---")
    # 5. Calculate days between dates
    start = datetime.date(2023, 1, 1)
    end = datetime.date(2023, 1, 10)
    diff = date_utils.days_between(start, end)
    print(f"Days between {start} and {end}: {diff}")

    # 6. Add business days (skipping weekends)
    friday = datetime.date(2023, 10, 27) # A Friday
    next_business_day = date_utils.add_business_days(friday, 1)
    print(f"Friday {friday} + 1 business day = {next_business_day} (Monday)")
    
    three_biz_days = date_utils.add_business_days(friday, 3)
    print(f"Friday {friday} + 3 business days = {three_biz_days} (Wednesday)")

if __name__ == "__main__":
    main()