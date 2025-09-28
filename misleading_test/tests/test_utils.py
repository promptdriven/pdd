import unittest
import json
from pathlib import Path
from src import utils

class TestGreeting(unittest.TestCase):
    def test_get_greeting_with_name(self):
        config_path = Path("src/config.json")
        original_content = config_path.read_text()
        try:
            with config_path.open("w") as f:
                json.dump({"user": {"name": "Alice"}}, f)
            self.assertEqual(utils.get_greeting(), "Hello, Alice!")
        finally:
            config_path.write_text(original_content)

    def test_get_greeting_without_name(self):
        config_path = Path("src/config.json")
        original_content = config_path.read_text()
        try:
            with config_path.open("w") as f:
                json.dump({"user": {"email": "test@example.com"}}, f)
            msg = utils.get_greeting()
            self.assertIn('Hello', msg)
        finally:
            config_path.write_text(original_content)
