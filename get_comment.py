import os
import pandas as pd

# Global variables for caching the loaded data
# This avoids reloading and reprocessing the CSV file on every call to get_comment,
# which is efficient if the function is called multiple times.
_cached_data_df: pd.DataFrame | None = None
_cached_pdd_path_val: str | None = None
# _data_load_failed_flag indicates if the last attempt to load data (for the current PDD_PATH) failed.
# This prevents repeated failed attempts if, for example, the file is missing.
_data_load_failed_flag: bool = False 

def _load_and_cache_data() -> pd.DataFrame | None:
    """
    Internal helper function to load, preprocess, and cache the CSV data.
    It's designed to be called by get_comment. It handles PDD_PATH,
    file reading, basic validation, and caching logic.
    Returns a pandas DataFrame if successful, None otherwise.
    Sets _data_load_failed_flag appropriately.
    """
    global _cached_data_df, _cached_pdd_path_val, _data_load_failed_flag

    current_pdd_path: str | None = os.getenv("PDD_PATH")

    # Step 1: Load environment variables PDD_PATH so the CSV can be loaded.
    if not current_pdd_path:
        # PDD_PATH is not set, cannot load CSV.
        _data_load_failed_flag = True
        _cached_data_df = None # Ensure cache is cleared if PDD_PATH is gone
        return None

    # Check if cached data can be used:
    # 1. PDD_PATH is the same as when data was cached.
    # 2. Data is actually in the cache (_cached_data_df is not None).
    # 3. The previous load attempt for this PDD_PATH was successful (not _data_load_failed_flag).
    if (
        _cached_pdd_path_val == current_pdd_path and
        _cached_data_df is not None and 
        not _data_load_failed_flag
    ):
        return _cached_data_df
    
    # If conditions for using cache are not met, attempt to (re-)load data.
    # Update the cached PDD_PATH for this new attempt.
    _cached_pdd_path_val = current_pdd_path
    # Reset failure flag for this specific load attempt.
    _data_load_failed_flag = False
    # Clear any stale data from cache before attempting to load new data.
    _cached_data_df = None

    csv_file_path: str = os.path.join(current_pdd_path, "data", "language_format.csv")

    try:
        # Read the CSV file. Pandas by default interprets empty strings in cells as NaN.
        df: pd.DataFrame = pd.read_csv(csv_file_path) 
        
        # Validate that essential columns ('language', 'comment') exist in the CSV.
        if 'language' not in df.columns or 'comment' not in df.columns:
            _data_load_failed_flag = True # Mark as failed due to missing required columns
            return None

        # Preprocess for efficient and case-insensitive lookup:
        # Create a new column with lowercase language names.
        # Fill potential NaN values in the 'language' column with an empty string 
        # before lowercasing to prevent errors if a language name itself is missing/NaN.
        df['language_lower_lookup'] = df['language'].fillna('').astype(str).str.lower()
        # Set this new column as the DataFrame index for fast lookups.
        df = df.set_index('language_lower_lookup')
        
        _cached_data_df = df # Cache the successfully loaded and processed DataFrame
        # _data_load_failed_flag remains False, indicating this load was successful.
        return _cached_data_df
    
    except FileNotFoundError:
        # The CSV file does not exist at the constructed path.
        _data_load_failed_flag = True
        return None
    except pd.errors.EmptyDataError:
        # The CSV file is empty and cannot be parsed.
        _data_load_failed_flag = True
        return None
    except Exception: 
        # Catch any other unexpected errors during file reading or pandas processing
        # (e.g., malformed CSV content, permission issues).
        _data_load_failed_flag = True
        return None

def get_comment(language: str) -> str:
    """
    Retrieves the comment character(s) for a given programming language by looking
    it up in a CSV file. The location of the CSV file is determined by the
    PDD_PATH environment variable (expected at PDD_PATH/data/language_format.csv).

    The CSV file should contain at least 'language' and 'comment' columns.

    Args:
        language: The name of the language (string). The lookup is case-insensitive.

    Returns:
        A string representing the comment character(s) for the specified language.
        If the language is not found, its comment entry is missing or empty in the CSV,
        or if the CSV file cannot be accessed or parsed correctly, this function
        returns the string 'del'. The 'del' string signifies that lines with such
        "comments" should effectively be deleted by the calling code.
        Note: If "del" is the actual comment string defined in the CSV for a language,
        it will be returned as such.
    """
    
    # Attempt to load data (this will use cached data if available and valid).
    # _load_and_cache_data handles PDD_PATH checking, file operations, and caching logic.
    # It also sets a global flag (_data_load_failed_flag) internally upon failure.
    df: pd.DataFrame | None = _load_and_cache_data()

    # If df is None, it means that PDD_PATH was not set, or a file/CSV related error occurred
    # during the _load_and_cache_data call.
    if df is None:
        return 'del'

    # Step 2: Lower case the input language string to make the comparison case insensitive.
    lang_lower: str = language.lower()

    # Step 3: Look up the comment character(s) for the given language.
    # We use the DataFrame's index (which is pre-processed to lowercase language names)
    # for efficient lookup.
    try:
        # Retrieve the 'comment' field for the language specified by lang_lower.
        # df.loc[row_index, column_name]
        comment_val: any = df.loc[lang_lower, 'comment']
    except KeyError:
        # This KeyError means that lang_lower (the lowercase version of the input language)
        # was not found in the DataFrame's index. So, the language is not in the CSV.
        return 'del'
    
    # Step 4: If the language is not found (covered by KeyError above) or 
    # comment character(s) is an invalid string, return 'del'.
    # An "invalid string" for a comment can mean it's missing (NaN in pandas) 
    # or an actual empty string.

    # Check if the comment value retrieved from the CSV is NaN.
    # Pandas uses NaN to represent missing data, e.g., an empty cell in the 'comment' column.
    if pd.isna(comment_val):
        return 'del'

    # Convert the comment value to a string.
    # This is a safeguard; 'comment' column values are typically strings, but this handles
    # cases where they might be numbers or other types if the CSV is unusual.
    # It ensures that we are working with a string for the next check.
    comment_str: str = str(comment_val)

    # Check if the comment string is empty after conversion.
    # This handles cases where a cell might contain an explicit empty string `""`
    # which, depending on pandas read_csv parameters, might not be converted to NaN.
    # (Though default pd.read_csv usually converts "" to NaN, making pd.isna catch it).
    if not comment_str: # This is True if comment_str is an empty string ""
        return 'del'
        
    # If all checks pass, the comment_str is valid and found.
    return comment_str