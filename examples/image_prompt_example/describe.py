import io
from contextlib import redirect_stdout


def generate_scene_text() -> str:
    """Return a detailed description of a Christmas-themed shelf display.

    This function encapsulates the multi-line string so the printed output can be
    captured programmatically.
    """
    return (
        "A detailed, eye-level shot of a Christmas-themed retail or home display "
        "featuring two light-colored wooden shelves mounted against a dark, matte "
        "black wall.\n\n"
        "The top shelf is arranged with a variety of festive gift bags and "
        "decorative cutouts. From left to right, there is a gift bag with a green "
        "and red plaid pattern, followed by a dark blue bag with a repeating "
        "pattern of small, light-colored Christmas trees. Centrally placed is a "
        "stylized, light grey felt or wooden Christmas tree cutout with a wooden "
        "trunk and a star on top. Next to it are several more gift bags: one "
        "white with a delicate green and red foliage pattern, a prominent red "
        "bag with three nutcracker figures, and another white bag with foliage. "
        "To the right of these is a light grey, stylized reindeer cutout. The "
        "shelf ends with another dark blue gift bag with the tree pattern.\n\n"
        "The bottom shelf continues the festive theme. On the far left, there are "
        "two plush gnome-like figures (gonks). One is stout, dressed in red with "
        "a large white beard. The other is taller and slimmer, wearing a grey "
        "patterned sweater and a red and white patterned hat. Next to them are "
        "two small, decorative houses resembling gingerbread houses, a small "
        "scroll tied with a red ribbon, and two white pillar candles in glass "
        "holders. Further to the right is a larger glass container holding a "
        "bundle of red and white taper candles. The shelf is completed by a red "
        "gift bag with nutcracker figures and another plaid-patterned gift bag "
        "leaning against it.\n\n"
        "The overall color palette is a classic Christmas combination of red, "
        "green, and white, which stands out against the dark background and the "
        "natural wood of the shelves."
    )


def main() -> None:
    """Capture the printed scene text and output the captured string.

    Using redirect_stdout ensures no intermediate console output aside from the
    final captured text. This is equivalent in behavior to the original script
    while being clearer and more robust.
    """
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        # Print the description; this output goes into the buffer
        print(generate_scene_text())

    # Retrieve and print the captured output to the actual stdout
    script_output = buffer.getvalue().strip()
    print(script_output)


if __name__ == "__main__":
    main()
