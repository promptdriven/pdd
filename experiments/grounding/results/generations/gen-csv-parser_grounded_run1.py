import csv

class CsvParser:
    """A class to parse CSV files and perform basic data operations."""

    def __init__(self, file_path: str):
        self.file_path = file_path
        self._data = []
        self._headers = []
        self._load_data()

    def _load_data(self) -> None:
        """Internal method to load CSV content into memory."""
        try:
            with open(self.file_path, mode='r', encoding='utf-8', newline='') as f:
                reader = csv.DictReader(f)
                self._headers = reader.fieldnames if reader.fieldnames else []
                self._data = [row for row in reader]
        except FileNotFoundError:
            raise FileNotFoundError(f"The file at {self.file_path} was not found.")
        except Exception as e:
            raise RuntimeError(f"An error occurred while reading the CSV: {e}")

    def get_headers(self) -> list:
        """Returns the list of column headers."""
        return self._headers

    def get_row_count(self) -> int:
        """Returns the total number of data rows."""
        return len(self._data)

    def filter_rows(self, column_name: str, value: str) -> list:
        """
        Returns a list of rows where the specified column matches the given value.
        """
        if column_name not in self._headers:
            raise ValueError(f"Column '{column_name}' not found in CSV.")
        
        return [row for row in self._data if row[column_name] == value]