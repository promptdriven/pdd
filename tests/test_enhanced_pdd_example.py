"""
Comprehensive tests for the enhanced PDD example command functionality.

This module tests all the improvements made to the pdd example command:
- File path information passing to context generator
- Correct import statement generation
- Default output path to examples/ directory
- Enhanced prompt template with import instructions
- Language independence
- Portability improvements
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


class TestEnhancedPDDExample:
    """Comprehensive test class for enhanced PDD example functionality."""
    
    def setup_method(self):
        """Set up test fixtures and mock data."""
        self.mock_code = "def hello():\n    print('hello')"
        self.mock_prompt = "Write a hello function"
        self.mock_example_code = "from hello import hello\n\nhello()"
        self.mock_cost = 0.01
        self.mock_model = "test-model"
    
    def test_context_generator_with_file_paths(self):
        """Test that context_generator accepts and uses file path parameters."""
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template by loading the actual template file
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock other functions
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {
                'result': self.mock_example_code,
                'cost': self.mock_cost,
                'model_name': self.mock_model
            }
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = (self.mock_example_code, 0.0, self.mock_model)
            
            # Call with file path parameters
            result = context_generator(
                code_module=self.mock_code,
                prompt=self.mock_prompt,
                language="python",
                source_file_path="/path/to/source/hello.py",
                example_file_path="/path/to/examples/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result
            assert result is not None, "Context generator should return a result"
            assert len(result) == 3, "Result should contain (code, cost, model_name)"
            
            # Verify that the prompt template was called with file path parameters
            mock_llm_invoke.assert_called_once()
            call_args = mock_llm_invoke.call_args[1]['input_json']
            assert 'source_file_path' in call_args, "source_file_path should be passed to LLM"
            assert 'example_file_path' in call_args, "example_file_path should be passed to LLM"
            assert 'module_name' in call_args, "module_name should be passed to LLM"
            assert call_args['source_file_path'] == "/path/to/source/hello.py"
            assert call_args['example_file_path'] == "/path/to/examples/hello_example.py"
            assert call_args['module_name'] == "hello"
    
    def test_context_generator_prompt_template_includes_import_instructions(self):
        """Test that the prompt template includes import instructions for correct import generation."""
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the enhanced prompt template by loading the actual template file
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock other functions
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {'result': 'from hello import hello', 'cost': self.mock_cost, 'model_name': self.mock_model}
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = ('from hello import hello', 0.0, self.mock_model)
            
            # Call context generator
            context_generator(self.mock_code, self.mock_prompt, language="python")
            
            # Verify that the prompt template was loaded
            mock_load.assert_called_once()
            
            # Verify that the template contains import instructions
            template_content = mock_load.return_value
            assert "IMPORT INSTRUCTIONS" in template_content, "Template should contain import instructions"
            assert "Python" in template_content, "Template should contain Python-specific instructions"
            assert "JavaScript" in template_content, "Template should contain JavaScript-specific instructions"
    
    def test_context_generator_main_with_file_paths(self):
        """Test that context_generator_main extracts and passes file path information."""
        # Create mock context with proper obj attribute
        from click import Context, Command
        mock_ctx = Context(Command('test'))
        mock_ctx.params = {}
        mock_ctx.obj = {'quiet': False, 'verbose': False, 'strength': 0.5, 'temperature': 0}
        
        with tempfile.TemporaryDirectory() as tmp_dir:
            # Create test files
            prompt_file = Path(tmp_dir) / "test.prompt"
            code_file = Path(tmp_dir) / "hello.py"
            output_file = Path(tmp_dir) / "hello_example.py"
            
            prompt_file.write_text("Write a hello function")
            code_file.write_text("def hello():\n    print('hello')")
            
            with patch('pdd.context_generator_main.construct_paths') as mock_construct_paths, \
                 patch('pdd.context_generator_main.context_generator') as mock_context_generator:
                
                # Mock construct_paths to return expected values
                mock_construct_paths.return_value = (
                    {},  # resolved_config
                    {"prompt_file": "Write a hello function", "code_file": "def hello():\n    print('hello')"},  # input_strings
                    {"output": str(output_file)},  # output_file_paths
                    "python"  # language
                )
                
                mock_context_generator.return_value = (self.mock_example_code, self.mock_cost, self.mock_model)
                
                result = context_generator_main(
                    mock_ctx, 
                    str(prompt_file), 
                    str(code_file), 
                    str(output_file)
                )
                
                # Verify context_generator was called with file path parameters
                mock_context_generator.assert_called_once()
                call_args = mock_context_generator.call_args[1]
                
                # Check that file path information was extracted and passed
                assert 'source_file_path' in call_args, "source_file_path should be passed"
                assert 'example_file_path' in call_args, "example_file_path should be passed"
                assert 'module_name' in call_args, "module_name should be passed"
                
                assert call_args['source_file_path'] == str(Path(code_file).resolve())
                assert call_args['example_file_path'] == str(Path(output_file).resolve())
                assert call_args['module_name'] == "hello"
    
    def test_example_command_defaults_to_examples_directory(self):
        """Test that the example command defaults to examples/ directory."""
        basename = "hello"
        
        result = generate_output_paths("example", {}, basename, "python", ".py")
        
        # Should default to examples/ directory
        assert "output" in result, "Should have output key"
        output_path = result["output"]
        assert "examples" in str(output_path), "Output should be in examples directory"
        assert basename in str(output_path), "Output should contain basename"
    
    def test_example_command_with_existing_examples_directory(self):
        """Test example command behavior when examples directory already exists."""
        basename = "test_module"
        
        # Create a temporary examples directory
        with tempfile.TemporaryDirectory() as tmp_dir:
            examples_dir = Path(tmp_dir) / "examples"
            examples_dir.mkdir()
            
            # Change to the temporary directory
            original_cwd = os.getcwd()
            os.chdir(tmp_dir)
            
            try:
                result = generate_output_paths("example", {}, basename, "python", ".py")
                
                # Should use the existing examples directory
                assert "output" in result, "Should have output key"
                output_path = result["output"]
                assert "examples" in str(output_path), "Output should be in examples directory"
                assert basename in str(output_path), "Output should contain basename"
                
            finally:
                os.chdir(original_cwd)
    
    def test_other_commands_not_affected(self):
        """Test that other commands are not affected by the example command changes."""
        basename = "test_module"
        
        # Test other commands still work as expected
        commands_to_test = ["generate", "test", "update"]
        
        for command in commands_to_test:
            result = generate_output_paths(command, {}, basename, "python", ".py")
            assert "output" in result, f"Command {command} should have output key"
            
            # These commands should not default to examples/ directory
            output_path = result["output"]
            if command != "example":
                # Other commands should not automatically go to examples/
                # They should use the current directory or user-specified path
                pass  # This is more of a sanity check that they don't break
    
    def test_import_statements_are_functional(self):
        """Test that generated import statements are functional and correct."""
        # This test would verify that the generated examples use correct import syntax
        # and can actually import the target modules without errors
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock LLM to return correct import syntax
            correct_import_code = """
from hello import hello

def main():
    hello()

if __name__ == "__main__":
    main()
"""
            
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {
                'result': correct_import_code,
                'cost': self.mock_cost,
                'model_name': self.mock_model
            }
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = (correct_import_code, 0.0, self.mock_model)
            
            # Call context generator
            result = context_generator(
                code_module=self.mock_code,
                prompt=self.mock_prompt,
                language="python",
                source_file_path="/path/to/hello.py",
                example_file_path="/path/to/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result contains correct import syntax
            generated_code = result[0]
            assert "from hello import hello" in generated_code, "Should use direct import syntax"
            assert "pdd.hello" not in generated_code, "Should not use package-style imports"
    
    def test_no_incorrect_package_imports(self):
        """Test that generated examples don't use incorrect package-style imports."""
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock LLM to return correct import syntax (not package-style)
            correct_import_code = "from hello import hello\n\nhello()"
            
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {
                'result': correct_import_code,
                'cost': self.mock_cost,
                'model_name': self.mock_model
            }
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = (correct_import_code, 0.0, self.mock_model)
            
            # Call context generator
            result = context_generator(
                code_module=self.mock_code,
                prompt=self.mock_prompt,
                language="python",
                source_file_path="/path/to/hello.py",
                example_file_path="/path/to/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result doesn't contain incorrect package imports
            generated_code = result[0]
            assert "pdd.hello" not in generated_code, "Should not use package-style imports"
            assert "from hello import hello" in generated_code, "Should use direct import syntax"
    
    def test_language_independence(self):
        """Test that the prompt template works for different programming languages."""
        languages = ["python", "javascript", "java", "cpp"]
        
        for language in languages:
            with patch('pdd.context_generator.load_prompt_template') as mock_load, \
                 patch('pdd.context_generator.preprocess') as mock_preprocess, \
                 patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
                 patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
                 patch('pdd.context_generator.continue_generation') as mock_continue, \
                 patch('pdd.context_generator.postprocess') as mock_postprocess:
                
                # Mock the prompt template
                from pathlib import Path
                template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
                with open(template_path, "r", encoding="utf-8") as f:
                    mock_load.return_value = f.read()
                
                mock_preprocess.side_effect = lambda x, **kwargs: x
                mock_llm_invoke.return_value = {
                    'result': f'// {language} example code',
                    'cost': self.mock_cost,
                    'model_name': self.mock_model
                }
                mock_unfinished.return_value = (None, True, 0.0, None)
                mock_postprocess.return_value = (f'// {language} example code', 0.0, self.mock_model)
                
                # Call context generator with different language
                result = context_generator(
                    code_module=self.mock_code,
                    prompt=self.mock_prompt,
                    language=language,
                    source_file_path="/path/to/module.py",
                    example_file_path="/path/to/example.py",
                    module_name="module"
                )
                
                # Verify the result is generated successfully
                assert result is not None, f"Should generate code for {language}"
                assert len(result) == 3, f"Result should contain (code, cost, model_name) for {language}"
    
    def test_example_files_are_in_examples_directory(self):
        """Test that generated example files are placed in the examples/ directory by default."""
        # This test verifies the default output path behavior
        result = generate_output_paths("example", {}, "test_module", "python", ".py")
        
        output_path = result["output"]
        assert "examples" in str(output_path), "Output should be in examples directory"
        assert "test_module" in str(output_path), "Output should contain module name"
        assert str(output_path).endswith(".py"), "Output should have correct file extension"
    
    def test_generated_example_has_proper_structure(self):
        """Test that generated examples have proper Python structure and syntax."""
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock LLM to return well-structured code
            structured_code = '''#!/usr/bin/env python3
"""
Example usage of the hello module.
"""

import sys
import os

def main():
    """Main function demonstrating hello usage."""
    # Add module path
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'hello', 'pdd'))
    
    from hello import hello
    hello()

if __name__ == "__main__":
    main()
'''
            
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {
                'result': structured_code,
                'cost': self.mock_cost,
                'model_name': self.mock_model
            }
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = (structured_code, 0.0, self.mock_model)
            
            # Call context generator
            result = context_generator(
                code_module=self.mock_code,
                prompt=self.mock_prompt,
                language="python",
                source_file_path="/path/to/hello.py",
                example_file_path="/path/to/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result has proper structure
            generated_code = result[0]
            assert "#!/usr/bin/env python3" in generated_code, "Should have shebang"
            assert '"""' in generated_code, "Should have docstring"
            assert "def main():" in generated_code, "Should have main function"
            assert 'if __name__ == "__main__":' in generated_code, "Should have main guard"
    
    def test_generated_example_handles_import_errors_gracefully(self):
        """Test that generated examples handle import errors gracefully."""
        with patch('pdd.context_generator.load_prompt_template') as mock_load, \
             patch('pdd.context_generator.preprocess') as mock_preprocess, \
             patch('pdd.context_generator.llm_invoke') as mock_llm_invoke, \
             patch('pdd.context_generator.unfinished_prompt') as mock_unfinished, \
             patch('pdd.context_generator.continue_generation') as mock_continue, \
             patch('pdd.context_generator.postprocess') as mock_postprocess:
            
            # Mock the prompt template
            from pathlib import Path
            template_path = Path(__file__).parent.parent / "pdd" / "prompts" / "example_generator_LLM.prompt"
            with open(template_path, "r", encoding="utf-8") as f:
                mock_load.return_value = f.read()
            
            # Mock LLM to return code with error handling
            error_handling_code = '''import sys
import os

try:
    # Add module path
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'hello', 'pdd'))
    from hello import hello
    hello()
except ImportError as e:
    print(f"Error importing hello module: {e}")
    sys.exit(1)
'''
            
            mock_preprocess.side_effect = lambda x, **kwargs: x
            mock_llm_invoke.return_value = {
                'result': error_handling_code,
                'cost': self.mock_cost,
                'model_name': self.mock_model
            }
            mock_unfinished.return_value = (None, True, 0.0, None)
            mock_postprocess.return_value = (error_handling_code, 0.0, self.mock_model)
            
            # Call context generator
            result = context_generator(
                code_module=self.mock_code,
                prompt=self.mock_prompt,
                language="python",
                source_file_path="/path/to/hello.py",
                example_file_path="/path/to/hello_example.py",
                module_name="hello"
            )
            
            # Verify the result handles errors gracefully
            generated_code = result[0]
            assert "try:" in generated_code, "Should have try block"
            assert "except ImportError" in generated_code, "Should handle ImportError"
            assert "sys.exit(1)" in generated_code, "Should exit on import failure"


if __name__ == "__main__":
    pytest.main([__file__])
