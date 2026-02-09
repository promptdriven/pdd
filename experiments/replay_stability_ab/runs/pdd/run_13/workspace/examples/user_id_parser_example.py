import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from user_id_parser import parse_user_id

# ---------------------------------------------------------------------------
# 1. String input in 'user:<id>' format
# ---------------------------------------------------------------------------

result = parse_user_id('user:alice_01')
print(f'String user:alice_01        -> {result!r}')  # ParseResult(user_id='alice_01', source='string')

# Normalization: leading/trailing whitespace is trimmed, text is lowercased
result = parse_user_id('user:  Bob-99  ')
print(f'String user:  Bob-99  -> {result!r}')  # ParseResult(user_id='bob-99', source='string')

# String without the 'user:' prefix is rejected
result = parse_user_id('alice_01')
print(f'String alice_01 (no prefix) -> {result!r}')  # None

# ---------------------------------------------------------------------------
# 2. Dict input with 'user_id' key
# ---------------------------------------------------------------------------

result = parse_user_id({'user_id': 'charlie'})
print(f'Dict user_id (charlie)        -> {result!r}')  # ParseResult(user_id='charlie', source='dict_flat')

# ---------------------------------------------------------------------------
# 3. Nested dict input: {'user': {'id': '<id>'}}
# ---------------------------------------------------------------------------

result = parse_user_id({'user': {'id': 'delta-7'}})
print(f'Nested dict id delta-7         -> {result!r}')  # ParseResult(user_id='delta-7', source='dict_nested')

# ---------------------------------------------------------------------------
# 4. Validation failures
# ---------------------------------------------------------------------------

# Too short
result = parse_user_id('user:ab')
print(f'Too short -> {result!r}')  # None

# Too long
result = parse_user_id('user:' + 'a' * 21)
print(f'Too long -> {result!r}')  # None

# Invalid characters
result = parse_user_id('user:bad user!')
print(f'Invalid chars -> {result!r}')  # None

# Reserved ID
result = parse_user_id('user:Admin')
print(f'Reserved Admin -> {result!r}')  # None

result = parse_user_id({'user_id': 'root'})
print(f'Reserved root -> {result!r}')  # None

result = parse_user_id({'user': {'id': 'system'}})
print(f'Reserved system -> {result!r}')  # None

# ---------------------------------------------------------------------------
# 5. Unsupported input types
# ---------------------------------------------------------------------------

result = parse_user_id(12345)
print(f'Int input -> {result!r}')  # None

result = parse_user_id(None)
print(f'None input -> {result!r}')  # None

result = parse_user_id(['user:alice'])
print(f'List input -> {result!r}')  # None