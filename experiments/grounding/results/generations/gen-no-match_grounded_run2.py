def rgb_to_hex(rgb: tuple[int, int, int]) -> str:
    """
    Converts an RGB tuple (r, g, b) to a hex string '#RRGGBB'.
    Ensures values stay between 0 and 255.
    """
    # Ensures values stay between 0 and 255 using clamping
    r, g, b = [max(0, min(val, 255)) for val in rgb]
    return f'#{r:02x}{g:02x}{b:02x}'.upper()

if __name__ == "__main__":
    # Example usage:
    color = (255, 0, 170)
    print(rgb_to_hex(color))  # Output: #FF00AA