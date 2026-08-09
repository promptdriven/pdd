def validate_refund(charge_amount: int, refund_amount: int) -> str:
    """Return the refund decision for integer cent amounts."""
    if refund_amount <= 0:
        return "rejected"
    if refund_amount > charge_amount:
        return "rejected"
    return "approved"
