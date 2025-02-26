"""
Configuration file for pytest.

This file defines pytest collection behavior, particularly
which directories to ignore during test discovery.
"""

# Directories or files to ignore during test collection
collect_ignore_glob = [
    "tests/csv/*",
] 