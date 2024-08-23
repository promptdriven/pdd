import os
import pytest
from generate_output_paths import generate_output_paths

def test_generate_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('generate', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'app.py'}

def test_generate_custom_directory():
    output_locations = {'output': '/Users'}
    result = generate_output_paths('generate', output_locations, 'app', 'python', '.py')
    assert result == {'output': '/Users/app.py'}

def test_generate_custom_full_path():
    output_locations = {'output': 'pdd/custom_name.py'}
    result = generate_output_paths('generate', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'pdd/custom_name.py'}

def test_generate_environment_variable():
    os.environ['PDD_GENERATE_OUTPUT_PATH'] = 'pdd'
    output_locations = {'output': None}
    result = generate_output_paths('generate', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'pdd/app.py'}
    del os.environ['PDD_GENERATE_OUTPUT_PATH']

def test_example_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('example', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'app_example.py'}

def test_test_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('test', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'test_app.py'}

def test_test_custom_path():
    output_locations = {'output': 'pdd/'}
    result = generate_output_paths('generate', output_locations, 'app', 'python', '.py')
    assert result == {'output': 'pdd/app.py'}

def test_preprocess_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('preprocess', output_locations, 'app', 'python', 'prompt')
    assert result == {'output': 'app_python_preprocessed.prompt'}

def test_fix_default_naming():
    output_locations = {'output-test': None, 'output-code': None}
    result = generate_output_paths('fix', output_locations, 'app', 'python', '.py')
    assert result == {'output-test': 'test_app_fixed.py', 'output-code': 'app_fixed.py'}

def test_fix_custom_paths():
    output_locations = {'output-test': 'tests', 'output-code': 'pdd'}
    result = generate_output_paths('fix', output_locations, 'app', 'python', '.py')
    assert result == {'output-test': 'tests/test_app_fixed.py', 'output-code': 'pdd/app_fixed.py'}

def test_split_default_naming():
    output_locations = {'output-sub': None, 'output-modified': None, 'output-cost': None}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': 'sub_app.prompt',
        'output-modified': 'modified_app.prompt'
    }

def test_split_custom_paths():
    output_locations = {'output-sub': 'prompts', 'output-modified': 'prompts', 'output-cost': './'}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': 'prompts/sub_app.prompt',
        'output-modified': 'prompts/modified_app.prompt'
    }

def test_split_environment_variables():
    os.environ['PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH'] = 'prompts'
    os.environ['PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH'] = 'prompts'
    os.environ['PDD_SPLIT_COST_OUTPUT_PATH'] = './'
    output_locations = {'output-sub': None, 'output-modified': None, 'output-cost': None}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': 'prompts/sub_app.prompt',
        'output-modified': 'prompts/modified_app.prompt'
    }
    del os.environ['PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH']
    del os.environ['PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH']
    del os.environ['PDD_SPLIT_COST_OUTPUT_PATH']

if __name__ == "__main__":
    pytest.main(["-vv", __file__])