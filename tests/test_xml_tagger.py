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

def test_xml_tagger_success(mock_environment, mock_file_reads, mock_llm_selector, mock_rich_print):
    raw_prompt = "Test prompt"
    strength = 0.7
    temperature = 0.5

    with patch('xml_tagger.PromptTemplate.from_template'), \
         patch('xml_tagger.StrOutputParser'), \
         patch('xml_tagger.JsonOutputParser'), \
         patch('xml_tagger.RunnablePassthrough'):
        
        xml_tagged, total_cost = xml_tagger(raw_prompt, strength, temperature)

    assert isinstance(xml_tagged, str)
    assert isinstance(total_cost, float)
    assert total_cost > 0

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
