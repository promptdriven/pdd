import pytest
from unittest.mock import patch, mock_open, MagicMock
from xml_tagger import xml_tagger

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_reads():
    mock_xml_convertor = "XML Convertor Prompt"
    mock_extract_xml = "Extract XML Prompt"
    with patch('builtins.open', mock_open(read_data=mock_xml_convertor)) as m:
        m.side_effect = [
            mock_open(read_data=mock_xml_convertor).return_value,
            mock_open(read_data=mock_extract_xml).return_value
        ]
        yield

@pytest.fixture
def mock_llm_selector():
    with patch('xml_tagger.llm_selector') as mock:
        mock.return_value = (
            lambda x: "Mocked LLM Response",
            lambda x: 100,  # token counter
            0.01,  # input cost
            0.02   # output cost
        )
        yield mock

@pytest.fixture
def mock_rich_print():
    with patch('xml_tagger.rprint') as mock:
        yield mock


def test_xml_tagger_success(mock_environment, mock_file_reads, mock_llm_selector, mock_rich_print):
    raw_prompt = "Test prompt"
    strength = 0.7
    temperature = 0.5

    # Mock the LLM response and token counter
    mock_llm_response = "Mocked LLM Response"
    mock_token_count = 100

    # Set up the mock LLM selector
    mock_llm = MagicMock()
    mock_llm.invoke = MagicMock(return_value=mock_llm_response)
    mock_token_counter = MagicMock(return_value=mock_token_count)
    mock_llm_selector.return_value = (mock_llm, mock_token_counter, 0.01, 0.02)

    # Mock the PromptTemplate and chain invocations
    with patch('xml_tagger.PromptTemplate') as mock_prompt_template, \
         patch('xml_tagger.StrOutputParser') as mock_str_parser, \
         patch('xml_tagger.JsonOutputParser') as mock_json_parser:
        
        mock_prompt_template.from_template.return_value = MagicMock()
        mock_str_parser.return_value = MagicMock()
        mock_json_parser.return_value = MagicMock()

        # Mock the chain invocations
        mock_xml_chain = MagicMock()
        mock_xml_chain.invoke.return_value = mock_llm_response
        mock_prompt_template.from_template.return_value.__or__.return_value.__or__.return_value = mock_xml_chain

        mock_extract_chain = MagicMock()
        mock_extract_chain.invoke.return_value = {'xml_tagged': 'Mocked XML'}
        mock_prompt_template.from_template.return_value.__or__.return_value.__or__.return_value = mock_extract_chain

        # Call the function
        xml_tagged, total_cost = xml_tagger(raw_prompt, strength, temperature)

    # Assertions
    assert isinstance(xml_tagged, str)
    assert xml_tagged == 'Mocked XML'
    assert isinstance(total_cost, float)
    assert total_cost > 0
    
    # Check if the mocks were called correctly
    mock_llm_selector.assert_called_once_with(strength, temperature)
    assert mock_token_counter
    
    import pytest
from unittest.mock import patch, mock_open
from xml_tagger import xml_tagger

@pytest.fixture
def mock_environment():
    with patch.dict('os.environ', {'PDD_PATH': '/mock/path'}):
        yield

@pytest.fixture
def mock_file_reads():
    mock_xml_convertor = "XML Convertor Prompt"
    mock_extract_xml = "Extract XML Prompt"
    with patch('builtins.open', mock_open(read_data=mock_xml_convertor)) as m:
        m.side_effect = [
            mock_open(read_data=mock_xml_convertor).return_value,
            mock_open(read_data=mock_extract_xml).return_value
        ]
        yield

@pytest.fixture
def mock_llm_selector():
    with patch('xml_tagger.llm_selector') as mock:
        mock.return_value = (
            lambda x: "Mocked LLM Response",
            lambda x: 100,  # token counter
            0.01,  # input cost
            0.02   # output cost
        )
        yield mock

@pytest.fixture
def mock_rich_print():
    with patch('xml_tagger.rprint') as mock:
        yield mock

def test_xml_tagger_missing_env_var():
    with patch.dict('os.environ', clear=True):
        xml_tagged, total_cost = xml_tagger("Test", 0.7, 0.5)

    assert xml_tagged == ""
    assert total_cost == 0.0

def test_xml_tagger_file_read_error(mock_environment):
    with patch('builtins.open', side_effect=IOError("Mock file read error")):
        xml_tagged, total_cost = xml_tagger("Test", 0.7, 0.5)

    assert xml_tagged == ""
    assert total_cost == 0.0

def test_xml_tagger_llm_error(mock_environment, mock_file_reads, mock_llm_selector):
    mock_llm_selector.side_effect = Exception("Mock LLM error")

    xml_tagged, total_cost = xml_tagger("Test", 0.7, 0.5)

    assert xml_tagged == ""
    assert total_cost == 0.0

def test_xml_tagger_invalid_input():
    with pytest.raises(TypeError):
        xml_tagger(123, "not a float", "not a float")
