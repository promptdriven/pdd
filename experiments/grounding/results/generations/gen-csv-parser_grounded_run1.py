import csv
from typing import List, Dict

class CsvParser:
    """
    A class to parse CSV files and perform basic data operations.
    
    Attributes:
        file_path (str): Path to the CSV file.
        headers (List[str]): List of column names.
        data (List[Dict[str, str]]): List of rows represented as dictionaries.
    """

    def __init__(self, file_path: str):
        """
        Initializes the CsvParser and loads data from the specified file.

        Args:
            file_path (str): The path to the CSV file to be read.

        Raises:
            FileNotFoundError: If the file does not exist.
            IOError: If there is an error reading the file.
        """
        self.file_path = file_path
        self.headers: List[str] = []
        self.data: List[Dict[str, str]] = []
        self._load_data()

    def _load_data(self) -> None:
        """Internal method to read the CSV file into memory."""
        try:
            with open(self.file_path, mode='r', encoding='utf-8', newline='') as f:
                reader = csv.DictReader(f)
                self.headers = reader.fieldnames if reader.fieldnames else []
                self.data = [row for row in reader]
        except FileNotFoundError:
            raise FileNotFoundError(f"The file at {self.file_path} was not found.")
        except Exception as e:
            # Handle empty files or malformed data gracefully
            if self.headers is None:
                self.headers = []
            self.data = []

    def get_headers(self) -> List[str]:
        """
        Returns the list of column headers.

        Returns:
            List[str]: The header names.
        """
        return self.headers

    def get_row_count(self) -> int:
        """
        Returns the total number of data rows (excluding the header).

        Returns:
            int: Number of rows.
        """
        return len(self.data)

    def filter_rows(self, column_name: str, value: str) -> List[Dict[str, str]]:
        """
        Filters rows where the specified column matches the given value.

        Args:
            column_name (str): The column to filter by.
            value (str): The value to search for.

        Returns:
            List[Dict[str, str]]: A list of rows matching the criteria.

        Raises:
            KeyError: If the column_name does not exist in the CSV.
        """
        if column_name not in self.headers:
            raise KeyError(f"Column '{column_name}' not found in headers: {self.headers}")
        
        return [row for row in self.data if row.get(column_name) == value]