"""
Tests for the enhanced pdd example command functionality.

This module tests the improvements made to the pdd example command:
- File path information passing to context generator
- Correct import statement generation
- Default output path to examples/ directory
- Enhanced prompt template with import instructions
"""

import pytest
import os
import tempfile
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock
from click.testing import CliRunner

from pdd.context_generator import context_generator
from pdd.context_generator_main import context_generator_main
from pdd.generate_output_paths import generate_output_paths
from pdd.cli import cli


class TestEnhancedContextGenerator:
    """Test the enhanced context_generator with file path parameters."""
    
    def test_context_generator_with_file_paths(self):
        """Test that context_generator accepts and uses file path parameters."""
        mock_code = "def hello():\n    print('hello')"
        mock_prompt = "Write a hello function"
        
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template
            mock_load.return_value = """
            % File path information:
            % - The source module file is located at: <source_file_path>{source_file_path}</source_file_path>
            % - The example file will be saved at: <example_file_path>{example_file_path}</example_file_path>
            % - The module name (without extension) is: <module_name>{module_name}</module_name>
            % - IMPORT INSTRUCTIONS: Import directly from the module name, e.g., "from {module_name} import function_name"
            """
            
            # Mock preprocessing
            mock_preprocess.side_effect = lambda x, **kwargs: x
            
            # Mock LLM response
            mock_llm_invoke.return_value = {
                'result': 'from hello import hello\n\nhello()',
                'cost': 0.01,
                'model_name': 'test-model'
            }
            
            # Mock unfinished prompt detection
            mock_unfinished.return_value = (None, True, 0.0, None)
            
            # Mock postprocessing
            mock_postprocess.return_value = ('from hello import hello\n\nhello()', 0.0, 'test-model')
            
            # Call with file path parameters
            result = context_generator(
                code_module=mock_code,
                prompt=mock_prompt,
                language="python",
                source_file_path="/path/to/source/hello.py",
                example_file_path="/path/to/examples/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result
            assert result[0] == 'from hello import hello\n\nhello()'
            assert result[1] == 0.01
            assert result[2] == 'test-model'
            
            # Verify that file path information was passed to LLM
            mock_llm_invoke.assert_called_once()
            call_args = mock_llm_invoke.call_args
            input_json = call_args[1]['input_json']
            
            assert input_json['source_file_path'] == "/path/to/source/hello.py"
            assert input_json['example_file_path'] == "/path/to/examples/hello_example.py"
            assert input_json['module_name'] == "hello"


class TestEnhancedContextGeneratorMain:
    """Test the enhanced context_generator_main with file path resolution."""
    
    def test_context_generator_main_with_file_paths(self):
        """Test that context_generator_main resolves and passes file paths."""
        mock_ctx = MagicMock()
        mock_ctx.obj = {
            'force': False,
            'quiet': False,
            'verbose': False,
            'strength': 0.5,
            'temperature': 0
        }
        
        with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
             patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
             patch('builtins.open', mock_open()) as mock_file:
            
            # Mock construct_paths
            mock_construct_paths.return_value = (
                {},  # resolved_config
                {"prompt_file": "test prompt", "code_file": "def hello(): pass"},
                {"output": "/path/to/examples/hello_example.py"},
                "python"
            )
            
            # Mock context_generator
            mock_context_generator.return_value = ("example code", 0.01, "test-model")
            
            # Call the function
            result = context_generator_main(
                mock_ctx, 
                "/path/to/prompt.prompt", 
                "/path/to/hello.py", 
                None
            )
            
            # Verify the result
            assert result == ("example code", 0.01, "test-model")
            
            # Verify that file path information was passed to context_generator
            mock_context_generator.assert_called_once()
            call_args = mock_context_generator.call_args[1]
            
            assert call_args['source_file_path'] == "/path/to/hello.py"
            assert call_args['example_file_path'] == "/path/to/examples/hello_example.py"
            assert call_args['module_name'] == "hello"


class TestEnhancedGenerateOutputPaths:
    """Test the enhanced generate_output_paths with examples directory default."""
    
    def test_example_command_defaults_to_examples_directory(self):
        """Test that example command defaults to examples/ directory."""
        with patch('os.path.exists', return_value=False), \
             patch('os.makedirs') as mock_makedirs:
            
            result = generate_output_paths(
                command="example",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config={}
            )
            
            # Verify the output path includes examples directory
            assert "output" in result
            assert "examples/hello_example.py" in result["output"]
            
            # Verify that examples directory was created
            mock_makedirs.assert_called_once_with("examples", exist_ok=True)
    
    def test_example_command_with_existing_examples_directory(self):
        """Test that example command works when examples directory already exists."""
        with patch('os.path.exists', return_value=True), \
             patch('os.makedirs') as mock_makedirs:
            
            result = generate_output_paths(
                command="example",
                output_locations={},
                basename="hello",
                language="python",
                file_extension=".py",
                context_config={}
            )
            
            # Verify the output path includes examples directory
            assert "output" in result
            assert "examples/hello_example.py" in result["output"]
            
            # Verify that makedirs was not called since directory exists
            mock_makedirs.assert_not_called()
    
    def test_other_commands_not_affected(self):
        """Test that other commands are not affected by the examples directory change."""
        result = generate_output_paths(
            command="generate",
            output_locations={},
            basename="hello",
            language="python",
            file_extension=".py",
            context_config={}
        )
        
        # Verify the output path is in current directory, not examples
        assert "output" in result
        assert result["output"].endswith("hello.py")
        assert not result["output"].startswith("examples/")


class TestEnhancedPromptTemplate:
    """Test the enhanced prompt template with import instructions."""
    
    def test_prompt_template_contains_import_instructions(self):
        """Test that the prompt template contains import instructions."""
        prompt_file = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
        
        assert prompt_file.exists(), "Prompt template file should exist"
        
        content = prompt_file.read_text()
        
        # Verify that the prompt contains the new import instructions
        assert "IMPORT INSTRUCTIONS" in content
        assert "Use the appropriate import mechanism for the target language" in content
        assert "For Python: Use direct imports from the module name" in content
        assert "For JavaScript: Use require() or ES6 import syntax" in content
        assert "source_file_path" in content
        assert "example_file_path" in content
        assert "module_name" in content


class TestExampleCommandIntegration:
    """Integration tests for the enhanced example command."""
    
    def test_example_command_cli_help(self):
        """Test that the example command shows correct help."""
        runner = CliRunner()
        result = runner.invoke(cli, ['example', '--help'])
        
        assert result.exit_code == 0
        assert "Generate example code for a given prompt and implementation" in result.output
        assert "--output" in result.output
    
    def test_example_command_with_mock_files(self, tmp_path):
        """Test the example command with mock files."""
        # Create mock files
        prompt_file = tmp_path / "test.prompt"
        code_file = tmp_path / "hello.py"
        
        prompt_file.write_text("Write a hello function")
        code_file.write_text("def hello():\n    print('hello')")
        
        runner = CliRunner()
        
        with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
             patch('pdd.context_generator_main.context_generator') as mock_context_generator, \
             patch('builtins.open', mock_open()) as mock_file:
            
            # Mock construct_paths
            mock_construct_paths.return_value = (
                {},
                {"prompt_file": "Write a hello function", "code_file": "def hello():\n    print('hello')"},
                {"output": str(tmp_path / "examples" / "hello_example.py")},
                "python"
            )
            
            # Mock context_generator
            mock_context_generator.return_value = ("from hello import hello\n\nhello()", 0.01, "test-model")
            
            # Run the command
            result = runner.invoke(cli, ['example', str(prompt_file), str(code_file)])
            
            # Verify the command succeeded
            assert result.exit_code == 0
            assert "Example code generated successfully" in result.output
            
            # Verify that file path information was passed
            mock_context_generator.assert_called_once()
            call_args = mock_context_generator.call_args[1]
            assert call_args['source_file_path'] == str(code_file.resolve())
            assert call_args['module_name'] == "hello"


class TestImportStatementGeneration:
    """Test the import statement generation improvements."""
    
    def test_import_instructions_in_prompt(self):
        """Test that the prompt template includes proper import instructions."""
        prompt_file = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
        content = prompt_file.read_text()
        
        # Check for specific import guidance
        assert "IMPORT INSTRUCTIONS" in content
        assert "Use the appropriate import mechanism for the target language" in content
        assert "For Python: Use direct imports from the module name" in content
        assert "For JavaScript: Use require() or ES6 import syntax" in content
    
    def test_file_path_context_in_prompt(self):
        """Test that the prompt template includes file path context."""
        prompt_file = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
        content = prompt_file.read_text()
        
        # Check for file path information
        assert "source_file_path" in content
        assert "example_file_path" in content
        assert "module_name" in content
        assert "File path information" in content


if __name__ == "__main__":
    pytest.main([__file__])
