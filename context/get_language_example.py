from pdd.get_language import get_language


def main() -> None:
    """
    Main function to demonstrate the usage of the get_language function.
    """


    # Example file extension
    file_extension: str = '.py'

    try:
        # Get the programming language associated with the file extension
        language: str = get_language(file_extension)

        # Output the result
        if language:
            print(f"The programming language for the extension '{file_extension}' is: {language}")
        else:
            print(f"No programming language found for the extension '{file_extension}'.")
    except Exception as e:
        print(f"An error occurred: {e}")


if __name__ == "__main__":
    main()
