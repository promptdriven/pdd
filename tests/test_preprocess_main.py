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
from pdd import DEFAULT_TIME, DEFAULT_STRENGTH

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
            {},  # resolved_config
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
            context_override=None
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
    basic_click_context.obj["strength"] = DEFAULT_STRENGTH
    basic_click_context.obj["temperature"] = 0.6
    basic_click_context.obj["verbose"] = True

    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.xml_tagger") as mock_xml_tagger, \
         patch("builtins.open", mock_open()) as m_file:

        # Mock the return values
        mock_construct_paths.return_value = (
            {},  # resolved_config
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
            context_override=None
        )
        # preprocess should NOT be called if xml=True
        mock_preprocess.assert_not_called()

        # xml_tagger should be called
        mock_xml_tagger.assert_called_once_with(
            "fake prompt content for xml",
            DEFAULT_STRENGTH,     # strength
            0.6,     # temperature
            True,    # verbose
            time=DEFAULT_TIME
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
            {},  # resolved_config
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
            {},  # resolved_config
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


def test_preprocess_main_with_pdd_tags(basic_click_context):
    """
    Test that preprocess_main correctly injects PDD tags when pdd_tags=True
    and the prompt doesn't already have tags.
    """
    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.get_architecture_entry_for_prompt") as mock_get_entry, \
         patch("pdd.preprocess_main.has_pdd_tags") as mock_has_tags, \
         patch("pdd.preprocess_main.generate_tags_from_architecture") as mock_gen_tags, \
         patch("builtins.open", mock_open()) as m_file:

        # Mock the return values
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "% Role & Scope\nYour goal is..."},
            {"output": "/tmp/output.prompt"},
            None
        )
        mock_get_entry.return_value = {
            "filename": "test.prompt",
            "reason": "Test module",
            "dependencies": ["dep.prompt"]
        }
        mock_has_tags.return_value = False
        mock_gen_tags.return_value = "<pdd-reason>Test module</pdd-reason>\n<pdd-dependency>dep.prompt</pdd-dependency>"
        mock_preprocess.return_value = "<pdd-reason>Test module</pdd-reason>\n<pdd-dependency>dep.prompt</pdd-dependency>\n\n% Role & Scope\nYour goal is..."

        # Call the function under test with pdd_tags=True
        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="test.prompt",
            output=None,
            xml=False,
            recursive=False,
            double=False,
            exclude=[],
            pdd_tags=True
        )

        # Assertions
        assert "<pdd-reason>Test module</pdd-reason>" in result[0]
        assert result[1] == 0.0
        assert result[2] == "N/A"

        # Ensure architecture sync functions were called
        mock_get_entry.assert_called_once()
        mock_has_tags.assert_called_once()
        mock_gen_tags.assert_called_once()


def test_preprocess_main_pdd_tags_skip_existing(basic_click_context):
    """
    Test that PDD tags injection is skipped when prompt already has tags.
    """
    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.get_architecture_entry_for_prompt") as mock_get_entry, \
         patch("pdd.preprocess_main.has_pdd_tags") as mock_has_tags, \
         patch("pdd.preprocess_main.generate_tags_from_architecture") as mock_gen_tags, \
         patch("builtins.open", mock_open()) as m_file:

        # Mock the return values
        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "<pdd-reason>Existing</pdd-reason>\n% Content"},
            {"output": "/tmp/output.prompt"},
            None
        )
        mock_get_entry.return_value = {"filename": "test.prompt", "reason": "Test"}
        mock_has_tags.return_value = True  # Already has tags
        mock_preprocess.return_value = "<pdd-reason>Existing</pdd-reason>\n% Content"

        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="test.prompt",
            output=None,
            xml=False,
            recursive=False,
            double=False,
            exclude=[],
            pdd_tags=True
        )

        # generate_tags should NOT be called when tags already exist
        mock_gen_tags.assert_not_called()


def test_preprocess_main_pdd_tags_no_entry(basic_click_context):
    """
    Test that PDD tags injection is skipped when no architecture entry exists.
    """
    with patch("pdd.preprocess_main.construct_paths") as mock_construct_paths, \
         patch("pdd.preprocess_main.preprocess") as mock_preprocess, \
         patch("pdd.preprocess_main.get_architecture_entry_for_prompt") as mock_get_entry, \
         patch("pdd.preprocess_main.has_pdd_tags") as mock_has_tags, \
         patch("pdd.preprocess_main.generate_tags_from_architecture") as mock_gen_tags, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "% Content without tags"},
            {"output": "/tmp/output.prompt"},
            None
        )
        mock_get_entry.return_value = None  # No architecture entry
        mock_preprocess.return_value = "% Content without tags"

        result = preprocess_main(
            ctx=basic_click_context,
            prompt_file="orphan.prompt",
            output=None,
            xml=False,
            recursive=False,
            double=False,
            exclude=[],
            pdd_tags=True
        )

        # has_pdd_tags and generate_tags should NOT be called when no entry exists
        mock_has_tags.assert_not_called()
        mock_gen_tags.assert_not_called()
