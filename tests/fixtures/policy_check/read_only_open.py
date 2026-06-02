"""Read-only file access should be allowed when writes are forbidden."""


def load_config() -> str:
    with open("config.txt", encoding="utf-8") as handle:
        return handle.read()
