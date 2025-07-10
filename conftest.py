"""
Configuration file for pytest.

This file defines pytest collection behavior, particularly
which directories to ignore during test discovery.
"""
import os
from dotenv import load_dotenv

# Load environment variables from .env file
load_dotenv()

# Directories or files to ignore during test collection
collect_ignore_glob = [
    "tests/csv/*",
] 