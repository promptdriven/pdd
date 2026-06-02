"""Writes a file when the contract forbids disk writes."""


def persist(data: str) -> None:
    with open("out.txt", "w", encoding="utf-8") as handle:
        handle.write(data)
