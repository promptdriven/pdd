# test_preprocess_main.py
"""
Unit tests for the preprocess_main function in the pdd.preprocess_main module.
Uses pytest and unittest.mock to verify correct behavior under various scenarios.
"""

import sys
import pytest
import click
from unittest.mock import patch, MagicMock, mock_open

# Import the function under test from the corresponding module.
from pdd.preprocess_main import preprocess_main

@pytest.fixture
def basic_click_context():
    """
    Provide a basic Click Context fixture for testing.
    """
    ctx = click.Context(click.Command("test_cmd"))
    ctx.params["force"] = False
    ctx.params["quiet"] = False
    # ctx.obj will hold command-line options and shared objects
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
    }
    return ctx

def test_preprocess_main_no_xml(basic_click_context):
    """
    Test that preprocess_main correctly calls 'preprocess' when xml=False,
    saves the file, and returns the expected result.
    """
    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.xml_tagger") as mock_xml_tagger, \
         patch("builtins.open", mock_open()) as m_file:

        # Mock the return values
        mock_construct_paths.return_value = (
            {"prompt_file": "fake prompt content"},
            {"output": "/tmp/output.prompt"},
            None
        )
        mock_preprocess.return_value = "processed prompt text"

        # Call the function under test
        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="input.prompt",
            output=None,        # Let the function figure out the output path
            xml=False,
            recursive=False,
            double=False,
            exclude=[]
        )

        # Assertions
        assert result[0] == "processed prompt text"
        assert result[1] == 0.0  # We return 0.0 for total_cost when xml=False
        assert result[2] == "N/A"

        # Ensure construct_paths was called correctly
        mock_construct_paths.assert_called_once_with(
            input_file_paths={"prompt_file": "input.prompt"},
            force=False,
            quiet=False,
            command="preprocess",
            command_options={"output": None},
        )
        # Ensure preprocess was called with the correct arguments
        mock_preprocess.assert_called_once_with(
            "fake prompt content",
            False,  # recursive
            False,  # double
            exclude_keys=[]
        )
        # xml_tagger should NOT be called in this scenario
        mock_xml_tagger.assert_not_called()

        # Ensure a file write occurred
        m_file.assert_called_once_with("/tmp/output.prompt", "w")

def test_preprocess_main_with_xml(basic_click_context):
    """
    Test that preprocess_main correctly calls 'xml_tagger' when xml=True,
    saves the file, and returns the expected result.
    """
    # Override the default context to make verbose=True, so it passes
    # into xml_tagger as well.
    basic_click_context.obj["strength"] = 0.9
    basic_click_context.obj["temperature"] = 0.6
    basic_click_context.obj["verbose"] = True

    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.xml_tagger") as mock_xml_tagger, \
         patch("builtins.open", mock_open()) as m_file:

        # Mock the return values
        mock_construct_paths.return_value = (
            {"prompt_file": "fake prompt content for xml"},
            {"output": "/tmp/xml_output.prompt"},
            None
        )
        mock_xml_tagger.return_value = (
            "<xml>some tagged content</xml>", 0.123456, "xml-test-model"
        )

        # Call the function under test
        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="input_xml.prompt",
            output="/specified_output.prompt",
            xml=True,
            recursive=False,
            double=False,
            exclude=[]
        )

        # Assertions
        assert result[0] == "<xml>some tagged content</xml>"
        assert abs(result[1] - 0.123456) < 1e-7
        assert result[2] == "xml-test-model"

        # Ensure construct_paths was called correctly
        mock_construct_paths.assert_called_once_with(
            input_file_paths={"prompt_file": "input_xml.prompt"},
            force=False,
            quiet=False,
            command="preprocess",
            command_options={"output": "/specified_output.prompt"},
        )
        # preprocess should NOT be called if xml=True
        mock_preprocess.assert_not_called()

        # xml_tagger should be called
        mock_xml_tagger.assert_called_once_with(
            "fake prompt content for xml",
            0.9,     # strength
            0.6,     # temperature
            True     # verbose
        )

        # Ensure a file write occurred
        m_file.assert_called_once_with("/tmp/xml_output.prompt", "w")

def test_preprocess_main_recursive_and_double(basic_click_context):
    """
    Test the scenario where recursive=True and double=True,
    ensuring that 'preprocess' is called with those flags.
    """
    basic_click_context.obj["strength"] = 0.7
    basic_click_context.obj["temperature"] = 0.2

    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.xml_tagger") as mock_xml_tagger, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {"prompt_file": "some prompt for recursive test"},
            {"output": "/tmp/output_recursive.prompt"},
            None
        )
        mock_preprocess.return_value = "recursively processed prompt"
        mock_xml_tagger.return_value = ("", 0.0, "")

        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="recursive.prompt",
            output=None,
            xml=False,
            recursive=True,
            double=True,
            exclude=["do_not_double_this"]
        )

        # Check function return
        assert result[0] == "recursively processed prompt"
        assert result[1] == 0.0
        assert result[2] == "N/A"

        # preprocess called with those flags
        mock_preprocess.assert_called_once_with(
            "some prompt for recursive test",
            True,   # recursive
            True,   # double
            exclude_keys=["do_not_double_this"]
        )
        mock_xml_tagger.assert_not_called()
        m_file.assert_called_once_with("/tmp/output_recursive.prompt", "w")

def test_preprocess_main_quiet_mode(basic_click_context, capsys):
    """
    Test that no Rich output is printed when ctx.params['quiet'] is True.
    """
    basic_click_context.obj["quiet"] = True

    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {"prompt_file": "quiet prompt content"},
            {"output": "/tmp/quiet_output.prompt"},
            None
        )
        mock_preprocess.return_value = "quiet processed"

        preprocess_main(
            ctx=basic_click_context,
            prompt_file="quiet.prompt",
            output=None,
            xml=False,
            recursive=False,
            double=False,
            exclude=[]
        )

        captured = capsys.readouterr()
        # Because quiet=True, there's expected to be no Rich output.
        assert captured.out.strip() == ""
        # We can still check that the function wrote the file
        m_file.assert_called_once_with("/tmp/quiet_output.prompt", "w")

def test_preprocess_main_error_handling(basic_click_context, capsys):
    """
    Test that the function handles exceptions by printing an error message and
    calling sys.exit(1).
    """
    with patch("pdd.preprocess_main.construct_paths", side_effect=Exception("Construct paths failed!")), \
         patch.object(sys, "exit", side_effect=SystemExit) as mock_exit:

        with pytest.raises(SystemExit):
            preprocess_main(
                ctx=basic_click_context,
                prompt_file="faulty_input.prompt",
                output=None,
                xml=False,
                recursive=False,
                double=False,
                exclude=[]
            )

        captured = capsys.readouterr()
        assert "Error during preprocessing: Construct paths failed!" in captured.out
        mock_exit.assert_called_once_with(1)