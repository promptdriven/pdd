import os
import pytest
from generate_output_paths import generate_output_paths

def test_generate_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('generate', output_locations, 'app', 'python', 'py')
    assert result == {'output': 'app.py'}

def test_generate_custom_directory():
    output_locations = {'output': '/custom/dir'}
    result = generate_output_paths('generate', output_locations, 'app', 'python', 'py')
    assert result == {'output': '/custom/dir/app.py'}

def test_generate_custom_full_path():
    output_locations = {'output': '/custom/dir/custom_name.py'}
    result = generate_output_paths('generate', output_locations, 'app', 'python', 'py')
    assert result == {'output': '/custom/dir/custom_name.py'}

def test_generate_environment_variable():
    os.environ['PDD_GENERATE_OUTPUT_PATH'] = '/env/dir'
    output_locations = {'output': None}
    result = generate_output_paths('generate', output_locations, 'app', 'python', 'py')
    assert result == {'output': '/env/dir/app.py'}
    del os.environ['PDD_GENERATE_OUTPUT_PATH']

def test_example_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('example', output_locations, 'app', 'python', 'py')
    assert result == {'output': 'app_example.py'}

def test_test_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('test', output_locations, 'app', 'python', 'py')
    assert result == {'output': 'test_app.py'}

def test_preprocess_default_naming():
    output_locations = {'output': None}
    result = generate_output_paths('preprocess', output_locations, 'app', 'python', 'prompt')
    assert result == {'output': 'app_python_preprocessed.prompt'}

def test_fix_default_naming():
    output_locations = {'output-test': None, 'output-code': None}
    result = generate_output_paths('fix', output_locations, 'app', 'python', 'py')
    assert result == {'output-test': 'test_app_fixed.py', 'output-code': 'app_fixed.py'}

def test_fix_custom_paths():
    output_locations = {'output-test': '/test/dir', 'output-code': '/code/dir'}
    result = generate_output_paths('fix', output_locations, 'app', 'python', 'py')
    assert result == {'output-test': '/test/dir/test_app_fixed.py', 'output-code': '/code/dir/app_fixed.py'}

def test_split_default_naming():
    output_locations = {'output-sub': None, 'output-modified': None, 'output-cost': None}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': 'sub_app.prompt',
        'output-modified': 'modified_app.prompt',
        'output-cost': 'cost_app.txt'
    }

def test_split_custom_paths():
    output_locations = {'output-sub': '/sub/dir', 'output-modified': '/mod/dir', 'output-cost': '/cost/dir'}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': '/sub/dir/sub_app.prompt',
        'output-modified': '/mod/dir/modified_app.prompt',
        'output-cost': '/cost/dir/cost_app.txt'
    }

def test_split_environment_variables():
    os.environ['PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH'] = '/env/sub'
    os.environ['PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH'] = '/env/mod'
    os.environ['PDD_SPLIT_COST_OUTPUT_PATH'] = '/env/cost'
    output_locations = {'output-sub': None, 'output-modified': None, 'output-cost': None}
    result = generate_output_paths('split', output_locations, 'app', 'python', 'prompt')
    assert result == {
        'output-sub': '/env/sub/sub_app.prompt',
        'output-modified': '/env/mod/modified_app.prompt',
        'output-cost': '/env/cost/cost_app.txt'
    }
    del os.environ['PDD_SPLIT_SUB_PROMPT_OUTPUT_PATH']
    del os.environ['PDD_SPLIT_MODIFIED_PROMPT_OUTPUT_PATH']
    del os.environ['PDD_SPLIT_COST_OUTPUT_PATH']

if __name__ == "__main__":
    pytest.main(["-v", __file__])