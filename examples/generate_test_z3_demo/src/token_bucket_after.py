class TokenBucket:
    def __init__(self, capacity: int, tokens_available: int = None):
        if not isinstance(capacity, int) or isinstance(capacity, bool) or capacity <= 0:
            raise ValueError("capacity must be a positive integer")
        self._capacity = capacity
        if tokens_available is None:
            self._tokens_available = capacity
        else:
            if not isinstance(tokens_available, int) or isinstance(tokens_available, bool):
                raise ValueError("tokens_available must be an integer")
            if tokens_available < 0:
                raise ValueError("tokens_available must be non-negative")
            if tokens_available > capacity:
                raise ValueError("tokens_available cannot exceed capacity")
            self._tokens_available = tokens_available

    def consume(self, requested_tokens: int) -> bool:
        if not isinstance(requested_tokens, int) or isinstance(requested_tokens, bool):
            raise ValueError("requested_tokens must be an integer")
        if requested_tokens < 0:
            raise ValueError("requested_tokens must be non-negative")
        if requested_tokens > self._tokens_available:
            return False
        self._tokens_available -= requested_tokens
        return True

    def refill(self, amount: int) -> None:
        if not isinstance(amount, int) or isinstance(amount, bool):
            raise ValueError("amount must be an integer")
        if amount < 0:
            raise ValueError("amount must be non-negative")
        self._tokens_available = min(self._capacity, self._tokens_available + amount)

    @property
    def tokens_available(self) -> int:
        return self._tokens_available

    @property
    def capacity(self) -> int:
        return self._capacity