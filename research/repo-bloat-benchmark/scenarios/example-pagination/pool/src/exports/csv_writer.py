"""CSV rendering for ledger export pages."""


def render_page_as_csv_rows(page, columns):
    """Render one export page as CSV rows in column order."""
    rendered_export_rows = []
    for entry in page:
        rendered_export_rows.append(
            ",".join(str(entry.get(column, "")) for column in columns)
        )
    return rendered_export_rows


def csv_header_for_columns(columns):
    """Header line matching render_page_as_csv_rows output."""
    return ",".join(columns)
