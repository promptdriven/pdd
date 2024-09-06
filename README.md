# PDD (Prompt-Driven Development) Command Line Interface

## Introduction

PDD (Prompt-Driven Development) is a versatile tool for generating code, creating examples, running unit tests, and managing prompt files. It leverages AI models to streamline the development process, allowing developers to work more efficiently with prompt-driven code generation.

## Version

Current version: 0.1.0

To check your installed version, run:
```
pdd --version
```

## Supported Programming Languages

PDD supports a wide range of programming languages, including but not limited to:
- Python
- JavaScript
- Java
- C++
- Ruby
- Go

The specific language is often determined by the prompt file's naming convention or specified in the command options.

## Prompt File Naming Convention

Prompt files in PDD follow this specific naming format:
```
<basename>_<language>.prompt
```
Where:
- `<basename>` is the base name of the file or project
- `<language>` is the programming language or context of the prompt file

Examples:
- `factorial_calculator_python.prompt` (basename: factorial_calculator, language: python)
- `responsive_layout_css.prompt` (basename: responsive_layout, language: css)
- `data_processing_pipeline_python.prompt` (basename: data_processing_pipeline, language: python)

## Basic Usage

```
pdd [GLOBAL OPTIONS] COMMAND [OPTIONS] [ARGS]...
```

## Global Options

These options can be used with any command:

- `--force`: Overwrite existing files without asking for confirmation.
- `--strength FLOAT`: Set the strength of the AI model (0.0 to 1.0, default is 0.5).
- `--temperature FLOAT`: Set the temperature of the AI model (default is 0.0).
- `--verbose`: Increase output verbosity for more detailed information.
- `--quiet`: Decrease output verbosity for minimal information.
- `--output-cost PATH_TO_CSV_FILE`: Enable cost tracking and output a CSV file with usage details.

## AI Model Information

PDD uses a large language model to generate and manipulate code. The `--strength` and `--temperature` options allow you to control the model's output:

- Strength: Determines how powerful/expensive a model should be used. Higher values (closer to 1.0) result in high performance, while lower values are cheaper.
- Temperature: Controls the randomness of the output. Higher values increase diversity but may lead to less coherent results, while lower values produce more focused and deterministic outputs.

## Output Cost Tracking

PDD includes a feature for tracking and reporting the cost of operations. When enabled, it generates a CSV file with usage details for each command execution.

### Usage

To enable cost tracking, use the `--output-cost` option with any command:

```
pdd --output-cost PATH_TO_CSV_FILE [COMMAND] [OPTIONS] [ARGS]...
```

The `PATH_TO_CSV_FILE` should be the desired location and filename for the CSV output.

### Cost Calculation and Presentation

PDD calculates costs based on the AI model usage for each operation. Costs are presented in USD (United States Dollars) and are calculated using the following factors:

1. Model strength: Higher strength settings generally result in higher costs.
2. Input size: Larger inputs (e.g., longer prompts or code files) typically incur higher costs.
3. Operation complexity: Some operations (like `fix` with multiple iterations) may be more costly than simpler operations.

The exact cost per operation is determined by the AI service provider's current pricing model. PDD uses an internal pricing table that is regularly updated to reflect the most current rates.

### CSV Output

The generated CSV file includes the following columns:
- timestamp: The date and time of the command execution
- model: The AI model used for the operation
- command: The PDD command that was executed
- cost: The estimated cost of the operation in USD (e.g., 0.05 for 5 cents)
- input_files: A list of input files involved in the operation
- output_files: A list of output files generated or modified by the operation

This comprehensive output allows for detailed tracking of not only the cost and type of operations but also the specific files involved in each PDD command execution.

### Environment Variable

You can set a default location for the cost output CSV file using the environment variable:

- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.

If this environment variable is set, the CSV file will be saved to the specified path by default, unless overridden by the `--output-cost` option. For example, if `PDD_OUTPUT_COST_PATH=/path/to/cost/reports/`, the CSV file will be saved in that directory with a default filename.

### Cost Budgeting

For commands that support it (like the `fix` command), you can set a maximum budget using the `--budget` option. This helps prevent unexpected high costs, especially for operations that might involve multiple AI model calls.

Example:
```
pdd fix --budget 5.0 [OTHER OPTIONS] [ARGS]...
```
This sets a maximum budget of $5.00 for the fix operation.

## Commands

Here are the main commands provided by PDD:

### 1. generate

Create runnable code from a prompt file.

```
pdd generate [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file used to generate the code.

Options:
- `--output LOCATION`: Specify where to save the generated code. The default file name is `<basename>.<language_file_extension>`. If an environment variable `PDD_GENERATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd generate --output src/factorial_calculator.py factorial_calculator_python.prompt 
```

### 2. example

Create an example file from an existing code file and the prompt that generated the code file.

```
pdd example [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE CODE_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code.
- `CODE_FILE`: The filename of the existing code file.

Options:
- `--output LOCATION`: Specify where to save the generated example code. The default file name is `<basename>_example.<language_file_extension>`. If an environment variable `PDD_EXAMPLE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd example --output examples/factorial_calculator_example.py factorial_calculator_python.prompt src/factorial_calculator.py
```

### 3. test

Generate a unit test file for a given code file and its corresponding prompt file.

```
pdd test [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE CODE_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code.
- `CODE_FILE`: The filename of the code file to be tested.

Options:
- `--output LOCATION`: Specify where to save the generated test file. The default file name is `test_<basename>.<language_file_extension>`.
- `--language`: Specify the programming language. Defaults to the language specified by the prompt file name.

Example:
```
pdd test --output tests/test_factorial_calculator.py factorial_calculator_python.prompt src/factorial_calculator.py
```

### 4. preprocess

Preprocess prompt files and save the results.

```
pdd preprocess [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file to preprocess.

Options:
- `--output LOCATION`: Specify where to save the preprocessed prompt file. The default file name is `<basename>_<language>_preprocessed.prompt`.
- `--xml`: Automatically insert XML delimiters for long and complex prompt files to structure the content better.

Example:
```
pdd preprocess --output preprocessed/factorial_calculator_python_preprocessed.prompt --xml factorial_calculator_python.prompt 
```

### 5. fix

Fix errors in code and unit tests based on error messages and the original prompt file.

```
pdd fix [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE CODE_FILE UNIT_TEST_FILE ERROR_FILE
```

Arguments:
- `PROMPT_FILE`: The filename of the prompt file that generated the code under test.
- `CODE_FILE`: The filename of the code file to be fixed.
- `UNIT_TEST_FILE`: The filename of the unit test file.
- `ERROR_FILE`: The filename containing the unit test runtime error messages. Optional and does not need to exist when used with the `--loop` command.

Options:
- `--output-test LOCATION`: Specify where to save the fixed unit test file. The default file name is `test_<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_TEST_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-code LOCATION`: Specify where to save the fixed code file. The default file name is `<basename>_fixed.<language_file_extension>`. If an environment variable `PDD_FIX_CODE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-results LOCATION`: Specify where to save the results of the error fixing process. The default file name is `<basename>_fix_results.log`. If an environment variable `PDD_FIX_RESULTS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--loop`: Enable iterative fixing process.
  - `--verification-program PATH`: Specify the path to a Python program that verifies if the code still runs correctly.
  - `--max-attempts INT`: Set the maximum number of fix attempts before giving up (default is 3).
  - `--budget FLOAT`: Set the maximum cost allowed for the fixing process (default is $5.0).

When the `--loop` option is used, the fix command will attempt to fix errors through multiple iterations. It will use the specified verification program to check if the code runs correctly after each fix attempt. The process will continue until either the errors are fixed, the maximum number of attempts is reached, or the budget is exhausted.

Outputs:
- Fixed unit test file
- Fixed code file
- Results file containing the LLM model's output with unit test results.
- Print out of results when using '--loop' containing:
  - Success status (boolean)
  - Total number of fix attempts made
  - Total cost of all fix attempts

Example:
```
pdd fix --output-test tests/test_factorial_calculator_fixed.py --output-code src/factorial_calculator_fixed.py --output-results results/factorial_fix_results.log factorial_calculator_python.prompt src/factorial_calculator.py tests/test_factorial_calculator.py errors.log
```
In this example, `factorial_calculator_python.prompt` is the prompt file that originally generated the code under test.

### 6. split

Split large complex prompt files into smaller, more manageable prompt files.

```
pdd split [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT INPUT_CODE EXAMPLE_CODE
```

Arguments:
- `INPUT_PROMPT`: The filename of the large prompt file to be split.
- `INPUT_CODE`: The filename of the code generated from the input prompt.
- `EXAMPLE_CODE`: The filename of the example code that serves as the interface to the sub-module prompt file.

Options:
- `--output-sub LOCATION`: Specify where to save the generated sub-prompt file. The default file name is `sub_<basename>.prompt`. If an environment variable `PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.
- `--output-modified LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd split --output-sub prompts/sub_data_processing.prompt --output-modified prompts/modified_main_pipeline.prompt data_processing_pipeline_python.prompt src/data_pipeline.py examples/pipeline_interface.py 
```

### 7. change

Modify an input prompt file based on a change prompt and the corresponding input code.

```
pdd change [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT_FILE INPUT_CODE_FILE CHANGE_PROMPT_FILE
```

Arguments:
- `INPUT_PROMPT_FILE`: The filename of the prompt file that will be modified.
- `INPUT_CODE_FILE`: The filename of the code that was generated from the input prompt file.
- `CHANGE_PROMPT_FILE`: The filename containing the instructions on how to modify the input prompt file.

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`. If an environment variable `PDD_CHANGE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd change --output modified_factorial_calculator_python.prompt factorial_calculator_python.prompt src/factorial_calculator.py changes_factorial.prompt
```

### 8. update

Update the original prompt file based on the original code and the modified code.

```
pdd update [GLOBAL OPTIONS] [OPTIONS] INPUT_PROMPT_FILE INPUT_CODE_FILE MODIFIED_CODE_FILE
```

Arguments:
- `INPUT_PROMPT_FILE`: The filename of the prompt file that generated the original code.
- `INPUT_CODE_FILE`: The filename of the original code that was generated from the input prompt file.
- `MODIFIED_CODE_FILE`: The filename of the code that was modified by the user.

Options:
- `--output LOCATION`: Specify where to save the modified prompt file. The default file name is `modified_<basename>.prompt`.  If an environment variable `PDD_UPDATE_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd update --output updated_factorial_calculator_python.prompt factorial_calculator_python.prompt src/original_factorial_calculator.py src/modified_factorial_calculator.py
```

### 9. detect

Analyze a list of prompt files and a change description to determine which prompts need to be changed.

```
pdd detect [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILES... CHANGE_FILE
```

Arguments:
- `PROMPT_FILES`: A list of filenames of prompts that may need to be changed.
- `CHANGE_FILE`: Filename whose content describes the changes that need to be analyzed and potentially applied to the prompts.

Options:
- `--output LOCATION`: Specify where to save the CSV file containing the analysis results. The default file name is `<change_file_basename>_detect.csv`.  If an environment variable `PDD_DETECT_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd detect --output detect_results.csv factorial_calculator_python.prompt data_processing_python.prompt web_scraper_python.prompt changes_description.prompt
```

### 10. conflicts

Analyze two prompt files to find conflicts between them and suggest how to resolve those conflicts.

```
pdd conflicts [GLOBAL OPTIONS] [OPTIONS] PROMPT1 PROMPT2
```

Arguments:
- `PROMPT1`: First prompt in the pair of prompts we are comparing.
- `PROMPT2`: Second prompt in the pair of prompts we are comparing.

Options:
- `--output LOCATION`: Specify where to save the CSV file containing the conflict analysis results. The default file name is `<prompt1_basename>_<prompt2_basename>_conflict.csv`.  If an environment variable `PDD_CONFLICTS_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd conflicts --output conflicts_analysis.csv data_processing_module_python.prompt data_visualization_module_python.prompt 
```

### 11. crash

Fix errors in a code module that caused a program to crash.

```
pdd crash [GLOBAL OPTIONS] [OPTIONS] PROMPT_FILE CODE_FILE PROGRAM_FILE ERROR_FILE
```

Arguments:
- `PROMPT_FILE`: Filename of the prompt file that generated the code module.
- `CODE_FILE`: Filename of the code module that caused the crash and will be modified so it runs properly.
- `PROGRAM_FILE`: Filename of the program that was running the code module.
- `ERROR_FILE`: Filename of the file containing the errors from the program run.

Options:
- `--output LOCATION`: Specify where to save the fixed code file. The default file name is `<basename>_fixed.<language_extension>`.  If an environment variable `PDD_CRASH_OUTPUT_PATH` is set, the file will be saved in that path unless overridden by this option.

Example:
```
pdd crash --output fixed_data_processor.py data_processing_module_python.prompt crashed_data_processor.py main_pipeline.py crash_errors.log 
```

## Output Location Specification

For all commands that generate or modify files, the `--output` option (or its variant, such as `--output-sub` or `--output-modified` for the `split` command) allows flexible specification of the output location:

1. **Filename only**: If you provide just a filename (e.g., `--output result.py`), the file will be created in the current working directory.
2. **Full path**: If you provide a full path (e.g., `--output /home/user/projects/result.py`), the file will be created at that exact location.
3. **Directory**: If you provide a directory name (e.g., `--output ./generated/`), a file with an automatically generated name will be created in that directory.
4. **Environment Variable**: If the `--output` option is not provided, and an environment variable specific to the command is set, PDD will use the path specified by this variable. Otherwise, it will use default naming conventions and save the file in the current working directory.
5. **No Output Location**: If no output location is specified and no environment variable is set, the file will be saved in the current working directory with a default name given the command.

## Multi-Command Chaining

PDD supports multi-command chaining, allowing you to execute multiple commands in a single line. Commands will be executed in the order they are specified. This feature enables you to perform complex workflows efficiently, combining various PDD operations into a single, streamlined process.

Basic syntax for multi-command chaining:
```
pdd [GLOBAL OPTIONS] COMMAND1 [OPTIONS] [ARGS]... [COMMAND2 [OPTIONS] [ARGS]...]...
```

Here are some examples of multi-command chaining to illustrate its power and flexibility:

1. Generate code, create an example, and run tests in one go:
```
pdd generate --output src/factorial_calculator.py factorial_calculator_python.prompt example --output examples/factorial_usage.py factorial_calculator_python.prompt src/factorial_calculator.py test --output tests/test_factorial_calculator.py factorial_calculator_python.prompt src/factorial_calculator.py
```

2. Preprocess a prompt, generate code, and create an example with cost tracking:
```
pdd --output-cost usage.csv preprocess --output preprocessed/data_pipeline_preprocessed.prompt data_processing_pipeline_python.prompt generate --output src/data_pipeline.py preprocessed/data_pipeline_preprocessed.prompt example --output examples/pipeline_usage.py preprocessed/data_pipeline_preprocessed.prompt src/data_pipeline.py
```

3. Split a large prompt, generate code from the sub-prompt, and create a test:
```
pdd split --output-sub sub_prompts/data_processing_module.prompt --output-modified modified_prompts/main_pipeline.prompt large_data_pipeline_python.prompt src/data_pipeline.py examples/pipeline_interface.py generate --output src/data_processing_module.py sub_prompts/data_processing_module.prompt test --output tests/test_data_processing_module.py sub_prompts/data_processing_module.prompt src/data_processing_module.py
```

4. Update a prompt based on code changes, then generate new code and tests:
```
pdd update --output updated_prompts/updated_web_scraper.prompt web_scraper_python.prompt src/original_scraper.py src/modified_scraper.py generate --output src/new_scraper.py updated_prompts/updated_web_scraper.prompt test --output tests/test_new_scraper.py updated_prompts/updated_web_scraper.prompt src/new_scraper.py
```

5. Detect prompts that need changes, then apply changes to those prompts:
```
pdd detect --output to_change.csv data_processing_python.prompt web_scraper_python.prompt api_interface_python.prompt changes.prompt change --output modified_prompts/modified_$(cat to_change.csv | cut -d',' -f1 | tail -n +2) $(cat to_change.csv | cut -d',' -f1 | tail -n +2) $(cat to_change.csv | cut -d',' -f1 | tail -n +2 | sed 's/\.prompt/_code.py/') changes.prompt
```

6. Analyze conflicts between two prompts and then update one of them:
```
pdd conflicts --output conflicts.csv data_processing_module_python.prompt data_visualization_module_python.prompt update --output updated_data_processing_module.prompt data_processing_module_python.prompt $(head -n 1 conflicts.csv | cut -d',' -f4) $(head -n 1 conflicts.csv | cut -d',' -f5)
```

7. Generate code, fix errors, and run tests:
```
pdd generate --output src/factorial_calculator.py factorial_calculator_python.prompt fix --output-test tests/test_factorial_calculator_fixed.py --output-code src/factorial_calculator_fixed.py --output-results results/factorial_fix_results.log factorial_calculator_python.prompt src/factorial_calculator.py tests/test_factorial_calculator.py errors.log test --output tests/test_factorial_calculator.py factorial_calculator_python.prompt src/factorial_calculator_fixed.py
```

These examples demonstrate how you can combine multiple PDD commands to create sophisticated workflows, automating complex development tasks in a single command line invocation. Remember that options always come before arguments for each command in the chain.

## Getting Help

PDD provides comprehensive help features:

1. **General Help**:
   ```
   pdd --help
   ```
   Displays a list of available commands and options.

2. **Command-Specific Help**:
   ```
   pdd COMMAND --help
   ```
   Provides detailed help for a specific command, including available options and usage examples.

## Additional Features

- **Tab Completion**: PDD supports tab completion for commands and options in compatible shells. You can install tab completion by running:
  ```
  pdd --install-completion
  ```
- **Colorized Output**: PDD provides colorized output for better readability in compatible terminals.

## Environment Variables for Output Paths

You can set environment variables to define default output paths for each command, reducing the need to specify output locations in the command line. The following environment variables are supported:

- **`PDD_GENERATE_OUTPUT_PATH`**: Default path for the `generate` command.
- **`PDD_EXAMPLE_OUTPUT_PATH`**: Default path for the `example` command.
- **`PDD_TEST_OUTPUT_PATH`**: Default path for the `test` command.
- **`PDD_PREPROCESS_OUTPUT_PATH`**: Default path for the `preprocess` command.
- **`PDD_FIX_TEST_OUTPUT_PATH`**: Default path for the fixed unit test files in the `fix` command.
- **`PDD_FIX_CODE_OUTPUT_PATH`**: Default path for the fixed code files in the `fix` command.
- **`PDD_FIX_RESULTS_OUTPUT_PATH`**: Default path for the results file generated by the `fix` command.
- **`PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH`**: Default path for the sub-prompts generated by the `split` command.
- **`PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH`**: Default path for the modified prompts generated by the `split` command.
- **`PDD_CHANGE_OUTPUT_PATH`**: Default path for the modified prompts generated by the `change` command.
- **`PDD_UPDATE_OUTPUT_PATH`**: Default path for the updated prompts generated by the `update` command.
- **`PDD_OUTPUT_COST_PATH`**: Default path for the cost tracking CSV file.
- **`PDD_DETECT_OUTPUT_PATH`**: Default path for the CSV file generated by the `detect` command.
- **`PDD_CONFLICTS_OUTPUT_PATH`**: Default path for the CSV file generated by the `conflicts` command.
- **`PDD_CRASH_OUTPUT_PATH`**: Default path for the fixed code file generated by the `crash` command.

## Error Handling

PDD provides informative error messages when issues occur during command execution. Common error scenarios include:

- Invalid input files or formats
- Insufficient permissions to read/write files
- AI model-related errors (e.g., API failures)
- Syntax errors in generated code

When an error occurs, PDD will display a message describing the issue and, when possible, suggest steps to resolve it.

## Troubleshooting

Here are some common issues and their solutions:

1. **Command not found**: Ensure PDD is properly installed and added to your system's PATH.

2. **Permission denied errors**: Check that you have the necessary permissions to read input files and write to output locations.

3. **AI model not responding**: Verify your internet connection and check the status of the AI service.

4. **Unexpected output**: Try adjusting the `--strength` and `--temperature` parameters to fine-tune the AI model's behavior.

5. **High costs**: Use the `--output-cost` option to track usage and set appropriate budgets for the `fix` command's `--budget` option.

If you encounter persistent issues, consult the PDD documentation or reach out to the support team for assistance.

## Security Considerations

When using PDD, keep the following security considerations in mind:

1. **Code Execution**: PDD generates and modifies code. Always review generated code before execution, especially in production environments.

2. **Data Privacy**: Avoid using sensitive data in prompts or code files, as this information may be processed by the AI model.

3. **API Keys**: If PDD requires API keys for AI model access, store these securely and never include them in version control systems.

4. **Input Validation**: PDD assumes input files are trustworthy. Implement proper input validation if using PDD in a multi-user or networked environment.

5. **Output Handling**: Treat output files with the same security considerations as you would any other code or configuration files in your project.

## Workflow Integration

PDD can be integrated into various development workflows. Here are some typical use cases:

1. **Initial Development**: Use `generate` to create initial code from prompts, then `example` and `test` to build out the project structure.

2. **Maintenance**: Use `update` to keep prompts in sync with code changes, and `fix` to address issues that arise during development.

3. **Refactoring**: Use `split` to break down large prompts, and `conflicts` to manage potential issues when working with multiple prompts.

4. **Continuous Integration**: Incorporate PDD commands into CI/CD pipelines to automate code generation, testing, and maintenance tasks.

5. **Debugging**: Use `crash` to quickly address runtime errors and generate fixes for failing modules.

## Conclusion

PDD (Prompt-Driven Development) CLI provides a comprehensive set of tools for managing prompt files, generating code, creating examples, running tests, and handling various aspects of prompt-driven development. By leveraging the power of AI models and iterative processes, PDD aims to streamline the development workflow and improve code quality.

The various commands and options allow for flexible usage, from simple code generation to complex workflows involving multiple steps. The ability to track costs, manage output locations through environment variables, and chain multiple commands further enhances the tool's utility in different development environments.

With the consistent argument order placing prompt files first, PDD emphasizes its prompt-driven nature and provides a more intuitive interface for users. This consistency across commands should make the tool easier to learn and use effectively.

As you become more familiar with PDD, you can create more complex workflows by chaining multiple commands and utilizing the full range of options available. Always refer to the latest documentation and use the built-in help features to make the most of PDD in your development process.

Remember to stay mindful of security considerations, especially when working with generated code or sensitive data. Regularly update PDD to access the latest features and improvements.

Happy coding with PDD!