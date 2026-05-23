"""Token bucket rate limiter module."""


class TokenBucket:
    """A token bucket rate limiter.

    The token bucket controls how many operations a caller can perform
    over time. Each consume call tries to take tokens from the bucket.
    A refill call adds tokens back up to the allowed limit.
    """

    def __init__(self, capacity: int, tokens_available: int = None):
        """Create a token bucket with the given capacity.

        Args:
            capacity: The maximum number of tokens the bucket can hold.
            tokens_available: Initial number of tokens. Defaults to capacity.

        Raises:
            ValueError: If capacity is not a positive integer.
            TypeError: If capacity is not an integer (excluding bool).
        """
        if isinstance(capacity, bool) or not isinstance(capacity, int):
            raise ValueError("capacity must be a positive integer")
        if capacity <= 0:
            raise ValueError("capacity must be a positive integer")

        if tokens_available is None:
            tokens_available = capacity
        else:
            if isinstance(tokens_available, bool) or not isinstance(
                tokens_available, int
            ):
                raise ValueError("tokens_available must be a non-negative integer")
            if tokens_available < 0:
                raise ValueError("tokens_available must be a non-negative integer")
            if tokens_available > capacity:
                raise ValueError("tokens_available cannot exceed capacity")

        self._capacity = capacity
        self._tokens_available = tokens_available

    @property
    def capacity(self) -> int:
        """Maximum number of tokens the bucket can hold."""
        return self._capacity

    @property
    def tokens_available(self) -> int:
        """Current number of available tokens."""
        return self._tokens_available

    def consume(self, requested_tokens: int) -> bool:
        """Attempt to consume requested_tokens from the bucket.

        Args:
            requested_tokens: The number of tokens to consume.

        Returns:
            True if the tokens were consumed, False if not enough tokens.

        Raises:
            ValueError: If requested_tokens is not a non-negative integer.
        """
        if isinstance(requested_tokens, bool) or not isinstance(
            requested_tokens, int
        ):
            raise ValueError("requested_tokens must be a non-negative integer")
        if requested_tokens < 0:
            raise ValueError("requested_tokens must be a non-negative integer")

        if requested_tokens > self._tokens_available:
            return False

        self._tokens_available -= requested_tokens
        return True

    def refill(self, amount: int) -> None:
        """Add amount tokens to the bucket, not exceeding capacity.

        Args:
            amount: The number of tokens to add.

        Raises:
            ValueError: If amount is not a non-negative integer.
        """
        if isinstance(amount, bool) or not isinstance(amount, int):
            raise ValueError("amount must be a non-negative integer")
        if amount < 0:
            raise ValueError("amount must be a non-negative integer")

        self._tokens_available = min(self._capacity, self._tokens_available + amount)

    def __repr__(self) -> str:
        return (
            f"TokenBucket(capacity={self._capacity}, "
            f"tokens_available={self._tokens_available})"
        )