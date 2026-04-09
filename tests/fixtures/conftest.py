"""Prevent pytest from collecting test files under fixtures/.

These are intentionally broken test files used as scenario data for the
one-session eval suite (test_one_session_eval.py). They are NOT meant to
be run as part of the regular test suite.
"""

collect_ignore_glob = ["*"]
