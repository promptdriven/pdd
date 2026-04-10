import pytest

from simple_math import add


def test_add_positive_numbers():
    assert add(2, 3) == 5


def test_add_negative_numbers():
    assert add(-4, -6) == -10


def test_add_mixed_sign_numbers():
    assert add(-4, 6) == 2


def test_add_zero():
    assert add(0, 0) == 0


def test_add_non_numbers_raises_type_error():
    with pytest.raises(TypeError):
        add(2, "3")
