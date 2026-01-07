from pdd.path_resolution import get_default_resolver


def main() -> None:
    resolver = get_default_resolver()

    include_path = resolver.resolve_include("context/python_preamble.prompt")
    prompt_path = resolver.resolve_prompt_template("load_prompt_template_python")
    project_root = resolver.resolve_project_root()

    print(include_path)
    print(prompt_path)
    print(project_root)

    try:
        data_path = resolver.resolve_data_file("data/language_format.csv")
        print(data_path)
    except ValueError:
        print("PDD_PATH not set")


if __name__ == "__main__":
    main()
