import csv

from pdd.path_resolution import get_default_resolver


def get_comment(language: str) -> str:
    try:
        resolver = get_default_resolver()
        csv_file_path = resolver.resolve_data_file("data/language_format.csv")
    except ValueError:
        return "del"

    if not isinstance(language, str):
        return "del"

    language = language.lower()

    try:
        with open(str(csv_file_path), mode="r", newline="") as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row["language"].lower() == language:
                    comment = row.get("comment", "")
                    return comment if comment else "del"
    except FileNotFoundError:
        return "del"
    except Exception:
        return "del"

    return "del"