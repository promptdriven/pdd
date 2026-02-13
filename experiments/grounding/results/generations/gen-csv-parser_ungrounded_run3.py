import csv
from typing import List, Dict, Optional, Any


class CsvParser:
    """
    A CSV file parser that provides methods to inspect and filter CSV data.
    
    Usage:
        parser = CsvParser("data.csv")
        headers = parser.get_headers()
        count = parser.get_row_count()
        filtered = parser.filter_rows("status", "active")
    """

    def __init__(self, filepath: str, delimiter: str = ",", encoding: str = "utf-8"):
        """
        Initialize the parser and load data from the CSV file.

        Args:
            filepath:  Path to the CSV file.
            delimiter: Column delimiter character (default: comma).
            encoding:  File encoding (default: utf-8).

        Raises:
            FileNotFoundError: If the file does not exist.
            ValueError:        If the file is empty or has no headers.
        """
        self._filepath = filepath
        self._delimiter = delimiter
        self._encoding = encoding
        self._headers: List[str] = []
        self._rows: List[Dict[str, str]] = []

        self._load(filepath)

    # ------------------------------------------------------------------ #
    #  Private helpers                                                     #
    # ------------------------------------------------------------------ #

    def _load(self, filepath: str) -> None:
        """Read the CSV file into memory."""
        try:
            with open(filepath, mode="r", newline="", encoding=self._encoding) as f:
                reader = csv.DictReader(f, delimiter=self._delimiter)

                if reader.fieldnames is None:
                    raise ValueError(f"CSV file '{filepath}' is empty or has no header row.")

                self._headers = list(reader.fieldnames)
                self._rows = [dict(row) for row in reader]
        except FileNotFoundError:
            raise FileNotFoundError(f"CSV file not found: '{filepath}'")

    def _validate_column(self, column: str) -> None:
        """Raise a KeyError if *column* is not in the headers."""
        if column not in self._headers:
            raise KeyError(
                f"Column '{column}' not found. "
                f"Available columns: {self._headers}"
            )

    # ------------------------------------------------------------------ #
    #  Public API                                                          #
    # ------------------------------------------------------------------ #

    def get_headers(self) -> List[str]:
        """Return the list of column header names."""
        return list(self._headers)

    def get_row_count(self) -> int:
        """Return the number of data rows (excluding the header)."""
        return len(self._rows)

    def get_row(self, index: int) -> Dict[str, str]:
        """
        Return a single row by its zero-based index.

        Raises:
            IndexError: If the index is out of range.
        """
        if index < 0 or index >= len(self._rows):
            raise IndexError(
                f"Row index {index} out of range (0–{len(self._rows) - 1})."
            )
        return dict(self._rows[index])

    def get_column_values(self, column: str) -> List[str]:
        """
        Return all values for the given column.

        Raises:
            KeyError: If the column doesn't exist.
        """
        self._validate_column(column)
        return [row[column] for row in self._rows]

    def get_unique_values(self, column: str) -> List[str]:
        """Return sorted unique values for a given column."""
        self._validate_column(column)
        return sorted(set(row[column] for row in self._rows))

    def filter_rows(
        self,
        column: str,
        value: str,
        case_sensitive: bool = True,
    ) -> List[Dict[str, str]]:
        """
        Return rows where *column* equals *value*.

        Args:
            column:         Column name to filter on.
            value:          Value to match.
            case_sensitive: Whether comparison is case-sensitive (default True).

        Returns:
            A list of row dicts that match the filter.

        Raises:
            KeyError: If the column doesn't exist.
        """
        self._validate_column(column)

        if case_sensitive:
            return [dict(row) for row in self._rows if row[column] == value]
        return [
            dict(row)
            for row in self._rows
            if row[column].lower() == value.lower()
        ]

    def filter_rows_custom(
        self, predicate: Any
    ) -> List[Dict[str, str]]:
        """
        Return rows for which *predicate(row)* is True.

        Example:
            parser.filter_rows_custom(lambda r: int(r["age"]) >= 18)
        """
        return [dict(row) for row in self._rows if predicate(row)]

    def to_list(self) -> List[Dict[str, str]]:
        """Return a copy of all rows as a list of dicts."""
        return [dict(row) for row in self._rows]

    def summary(self) -> str:
        """Return a human-readable summary of the parsed CSV."""
        return (
            f"CsvParser Summary\n"
            f"  File:    {self._filepath}\n"
            f"  Columns: {len(self._headers)} {self._headers}\n"
            f"  Rows:    {len(self._rows)}"
        )

    def __repr__(self) -> str:
        return (
            f"CsvParser(filepath='{self._filepath}', "
            f"columns={len(self._headers)}, rows={len(self._rows)})"
        )


# ====================================================================== #
#  Demo / Manual Test                                                      #
# ====================================================================== #

if __name__ == "__main__":
    import tempfile
    import os

    # ---- Create a sample CSV file ------------------------------------ #
    sample_csv = (
        "name,age,department,status\n"
        "Alice,30,Engineering,active\n"
        "Bob,25,Marketing,inactive\n"
        "Charlie,35,Engineering,active\n"
        "Diana,28,Marketing,active\n"
        "Eve,40,Engineering,inactive\n"
    )

    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".csv", delete=False, newline=""
    )
    tmp.write(sample_csv)
    tmp.close()

    try:
        # ---- Use the parser ------------------------------------------ #
        parser = CsvParser(tmp.name)

        # 1. Summary
        print(parser.summary())
        print(f"\nRepr: {parser!r}\n")

        # 2. Headers
        print(f"Headers: {parser.get_headers()}")

        # 3. Row count
        print(f"Row count: {parser.get_row_count()}")

        # 4. Single row access
        print(f"\nRow 0: {parser.get_row(0)}")
        print(f"Row 2: {parser.get_row(2)}")

        # 5. Column values
        print(f"\nAll names: {parser.get_column_values('name')}")
        print(f"Unique departments: {parser.get_unique_values('department')}")

        # 6. Filter by exact column value
        print("\n--- Filter: department == 'Engineering' ---")
        for row in parser.filter_rows("department", "Engineering"):
            print(f"  {row}")

        # 7. Case-insensitive filter
        print("\n--- Filter: status == 'ACTIVE' (case-insensitive) ---")
        for row in parser.filter_rows("status", "ACTIVE", case_sensitive=False):
            print(f"  {row}")

        # 8. Custom predicate filter
        print("\n--- Filter: age >= 30 (custom predicate) ---")
        for row in parser.filter_rows_custom(lambda r: int(r["age"]) >= 30):
            print(f"  {row}")

        # 9. Error handling demo
        print("\n--- Error handling ---")
        try:
            parser.filter_rows("nonexistent", "value")
        except KeyError as e:
            print(f"  Caught KeyError: {e}")

        try:
            parser.get_row(999)
        except IndexError as e:
            print(f"  Caught IndexError: {e}")

    finally:
        os.unlink(tmp.name)