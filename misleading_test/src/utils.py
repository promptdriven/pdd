import json
from pathlib import Path

def get_greeting():
    cfg = Path(__file__).parent / 'config.json'
    with cfg.open('r') as f:
        config = json.load(f)
    # fragile: KeyError if 'name' missing
    name = config['user']['name']
    return f'Hello, {name}!'
