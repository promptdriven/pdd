import pytest
from unittest.mock import patch, mock_open
from pdd.xml_tagger import xml_tagger

@pytest.fixture
def mock_environment():
    """Mock the environment variable PDD_PATH."""
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_contents():
    """Mock the contents of the files used by xml_tagger."""
    xml_convertor_content = "XML Convertor Prompt"
    extract_xml_content = "Extract XML Prompt"
    mock_files = {
        '/mock/path/prompts/xml_convertor_LLM.prompt': xml_convertor_content,
        '/mock/path/prompts/extract_xml_LLM.prompt': extract_xml_content
    }
    with patch('builtins.open', mock_open(read_data="")) as mock_file:
        mock_file.side_effect = lambda filename, *args, **kwargs: mock_open(read_data=mock_files[filename])()
        yield

@pytest.fixture
def mock_llm_selector():
    """Mock the LLM selector function."""
    with patch('pdd.xml_tagger.llm_selector') as mock:
        mock.return_value = (
            lambda x: "Mocked LLM Output",  # mocked LLM
            lambda x: 100,  # mocked token counter
            0.01,  # mocked input cost
            0.02,  # mocked output cost
            "MockedModel"  # mocked model name
        )
        yield mock

@pytest.fixture
def mock_rich_print():
    """Mock the rich print function."""
    with patch('pdd.xml_tagger.rprint') as mock:
        yield mock

def test_xml_tagger_success(mock_environment, mock_file_contents, mock_llm_selector, mock_rich_print):
    """Test successful execution of xml_tagger."""
    raw_prompt = "Test prompt"
    strength = 0.7
    temperature = 0.5

    result, total_cost, model_name = xml_tagger(raw_prompt, strength, temperature)

    assert isinstance(result, str)
    assert isinstance(total_cost, float)
    assert model_name == "MockedModel"
    assert total_cost > 0

def test_xml_tagger_missing_env_var():
    """Test xml_tagger behavior when PDD_PATH is not set."""
    with patch.dict('os.environ', clear=True):
        result, total_cost, model_name = xml_tagger("Test", 0.7, 0.5)

    assert result == ""
    assert total_cost == 0.0
    assert model_name == ""

@patch('pdd.xml_tagger.Path')
def test_xml_tagger_file_not_found(mock_path, mock_environment, mock_rich_print):
    """Test xml_tagger behavior when a required file is not found."""
    mock_path.side_effect = FileNotFoundError("File not found")

    result, total_cost, model_name = xml_tagger("Test", 0.7, 0.5)

    assert result == ""
    assert total_cost == 0.0
    assert model_name == ""
    mock_rich_print.assert_called_with("[bold red]Error:[/bold red] File not found")

@patch('pdd.xml_tagger.PromptTemplate')
def test_xml_tagger_unexpected_error(mock_prompt, mock_environment, mock_file_contents, mock_rich_print):
    """Test xml_tagger behavior when an unexpected error occurs."""
    mock_prompt.from_template.side_effect = Exception("Unexpected error")

    result, total_cost, model_name = xml_tagger("Test", 0.7, 0.5)

    assert result == ""
    assert total_cost == 0.0
    assert model_name == ""
    mock_rich_print.assert_called_with("[bold red]An unexpected error occurred:[/bold red] Unexpected error")