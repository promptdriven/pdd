# tests/test_conflicts_in_prompts.py

import os
import pytest
from unittest.mock import patch, mock_open, MagicMock
from typing import List, Dict, Any, Tuple

# Assuming the module structure is pdd.conflicts_in_prompts
from pdd.conflicts_in_prompts import conflicts_in_prompts

@pytest.fixture
def mock_llm_selector():
    with patch('pdd.conflicts_in_prompts.llm_selector') as mock_selector:
        # Mock return values for llm_selector
        mock_llm = MagicMock()
        mock_token_counter = MagicMock(return_value=1000)
        mock_selector.return_value = (mock_llm, mock_token_counter, 0.02, 0.03, "mock_model")
        yield mock_selector

@pytest.fixture
def mock_open_files():
    mock_conflict_prompts = "Conflict prompt template {PROMPT1} {PROMPT2}"
    mock_extract_prompts = "Extract prompt template {llm_output}"
    m = mock_open()
    m.side_effect = [
        mock_open(read_data=mock_conflict_prompts).return_value,
        mock_open(read_data=mock_extract_prompts).return_value
    ]
    with patch('builtins.open', m):
        yield m

@pytest.fixture
def mock_env_pdd_path():
    with patch.dict(os.environ, {"PDD_PATH": "/fake/path"}):
        yield

def test_conflicts_in_prompts_success(mock_env_pdd_path, mock_open_files, mock_llm_selector):
    # Mock the chain.invoke method for conflict detection
    with patch('pdd.conflicts_in_prompts.PromptTemplate') as mock_prompt_template:
        # Mock conflict_chain.invoke
        mock_conflict_chain = MagicMock()
        mock_conflict_chain.invoke.return_value = "Conflict detected between prompts."
        mock_prompt_instance = MagicMock(return_value=mock_conflict_chain)
        mock_prompt_template.from_template.return_value = mock_prompt_instance

        # Mock extract_chain.invoke
        with patch('pdd.conflicts_in_prompts.JsonOutputParser') as mock_json_parser:
            mock_extract_chain = MagicMock()
            mock_extract_chain.invoke.return_value = {"changes_list": [{"name": "prompt1", "instruction": "Change X"}]}
            mock_json_parser.return_value = MagicMock(return_value=mock_extract_chain)

            changes_list, total_cost, model_name = conflicts_in_prompts("Prompt A", "Prompt B")

            assert changes_list == [{"name": "prompt1", "instruction": "Change X"}]
            assert total_cost == (1000 / 1_000_000) * (0.02 + 0.03) * 2  # Conflict and extract costs
            assert model_name == "mock_model"

def test_conflicts_in_prompts_no_conflicts(mock_env_pdd_path, mock_open_files, mock_llm_selector):
    # Mock the chain.invoke method for conflict detection with no conflicts
    with patch('pdd.conflicts_in_prompts.PromptTemplate') as mock_prompt_template:
        # Mock conflict_chain.invoke
        mock_conflict_chain = MagicMock()
        mock_conflict_chain.invoke.return_value = "No conflicts found."
        mock_prompt_instance = MagicMock(return_value=mock_conflict_chain)
        mock_prompt_template.from_template.return_value = mock_prompt_instance

        # Mock extract_chain.invoke with empty changes_list
        with patch('pdd.conflicts_in_prompts.JsonOutputParser') as mock_json_parser:
            mock_extract_chain = MagicMock()
            mock_extract_chain.invoke.return_value = {"changes_list": []}
            mock_json_parser.return_value = MagicMock(return_value=mock_extract_chain)

            changes_list, total_cost, model_name = conflicts_in_prompts("Prompt A", "Prompt B")

            assert changes_list == []
            assert total_cost == (1000 / 1_000_000) * (0.02 + 0.03) * 2  # Conflict and extract costs
            assert model_name == "mock_model"

def test_conflicts_in_prompts_missing_pdd_path(mock_open_files, mock_llm_selector):
    # Remove PDD_PATH
    with patch.dict(os.environ, {}, clear=True):
        changes_list, total_cost, model_name = conflicts_in_prompts("Prompt A", "Prompt B")
        assert changes_list == []
        assert total_cost == 0.0
        assert model_name == ""

def test_conflicts_in_prompts_missing_prompt_files(mock_env_pdd_path, mock_llm_selector):
    # Mock open to raise FileNotFoundError
    with patch('builtins.open', side_effect=FileNotFoundError("File not found")):
        changes_list, total_cost, model_name = conflicts_in_prompts("Prompt A", "Prompt B")
        assert changes_list == []
        assert total_cost == 0.0
        assert model_name == ""

def test_conflicts_in_prompts_empty_prompts(mock_env_pdd_path, mock_llm_selector):
    # Mock the chain.invoke method for conflict detection with empty prompts
    with patch('pdd.conflicts_in_prompts.PromptTemplate') as mock_prompt_template:
        # Mock conflict_chain.invoke
        mock_conflict_chain = MagicMock()
        mock_conflict_chain.invoke.return_value = "No conflicts found."
        mock_prompt_instance = MagicMock(return_value=mock_conflict_chain)
        mock_prompt_template.from_template.return_value = mock_prompt_instance

        # Mock extract_chain.invoke with empty changes_list
        with patch('pdd.conflicts_in_prompts.JsonOutputParser') as mock_json_parser:
            mock_extract_chain = MagicMock()
            mock_extract_chain.invoke.return_value = {"changes_list": []}
            mock_json_parser.return_value = MagicMock(return_value=mock_extract_chain)

            changes_list, total_cost, model_name = conflicts_in_prompts("", "")

            assert changes_list == []
            assert total_cost == (1000 / 1_000_000) * (0.02 + 0.03) * 2  # Conflict and extract costs
            assert model_name == "mock_model"

def test_conflicts_in_prompts_exception(mock_env_pdd_path, mock_open_files, mock_llm_selector):
    # Mock PromptTemplate.from_template to raise an unexpected exception
    with patch('pdd.conflicts_in_prompts.PromptTemplate.from_template', side_effect=Exception("Unexpected error")):
        changes_list, total_cost, model_name = conflicts_in_prompts("Prompt A", "Prompt B")
        assert changes_list == []
        assert total_cost == 0.0
        assert model_name == ""
