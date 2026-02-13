def rgb_to_hex(rgb: tuple) -> str:
    """
    Convert an RGB color tuple (0-255) to a hex string format.

    Args:
        rgb: A tuple of three integers (r, g, b), each ranging from 0 to 255.

    Returns:
        A hex color string in the format '#RRGGBB'.

    Raises:
        ValueError: If any value is outside the 0-255 range.
    """
    for value in rgb:
        if not 0 <= value <= 255:
            raise ValueError(f"RGB values must be between 0 and 255, got {value}")

    r, g, b = rgb
    return f"#{r:02X}{g:02X}{b:02X}"

if __name__ == "__main__":
    print(rgb_to_hex((255, 0, 170)))    # '#FF00AA'
    print(rgb_to_hex((0, 0, 0)))        # '#000000'
    print(rgb_to_hex((255, 255, 255)))   # '#FFFFFF'
    print(rgb_to_hex((70, 130, 180)))    # '#4682B4' (steel blue)

    # Error handling
    try:
        print(rgb_to_hex((256, 0, 0)))
    except ValueError as e:
        print(e)  # "RGB values must be between 0 and 255, got 256"