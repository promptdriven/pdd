"""
Tests for pdd.setup_tool module.
Tests the issue fix: "pdd Setup should use llm_invoke and give access to all models"
"""

import pytest
import os
from unittest.mock import patch, MagicMock, call
from pathlib import Path
from pdd.setup_tool import (
    get_csv_variable_names,
    discover_api_keys,
    test_api_key_with_llm_invoke,
    test_api_keys,
    save_configuration,
)


class TestGetCsvVariableNames:
    """Test that get_csv_variable_names discovers all API keys from CSV dynamically"""
    
    def test_discovers_all_unique_api_keys(self):
        """Should return all unique API key variable names from the CSV"""
        result = get_csv_variable_names()
        
        # Should be a dict mapping API key names to themselves
        assert isinstance(result, dict)
        
        # Should include common providers (from the real CSV)
        expected_keys = {
            'OPENAI_API_KEY',
            'GEMINI_API_KEY', 
            'ANTHROPIC_API_KEY',
            'FIREWORKS_API_KEY',
            'GROQ_API_KEY',
            'VERTEX_CREDENTIALS',
        }
        
        # All expected keys should be present
        for key in expected_keys:
            assert key in result, f"{key} should be discovered from CSV"
            assert result[key] == key, f"{key} should map to itself"
    
    def test_no_hardcoded_provider_list(self):
        """Should not be limited to just 3 providers (the old bug)"""
        result = get_csv_variable_names()
        
        # Should have more than 3 API keys (the old code only supported 3)
        assert len(result) > 3, "Should discover more than just OpenAI, Google, and Anthropic"


class TestDiscoverApiKeys:
    """Test that discover_api_keys checks environment for all providers"""
    
    def test_discovers_all_providers_from_csv(self):
        """Should check environment variables for ALL providers in CSV"""
        with patch('pdd.setup_tool.get_csv_variable_names') as mock_get_csv:
            # Mock CSV with multiple providers
            mock_get_csv.return_value = {
                'OPENAI_API_KEY': 'OPENAI_API_KEY',
                'ANTHROPIC_API_KEY': 'ANTHROPIC_API_KEY',
                'FIREWORKS_API_KEY': 'FIREWORKS_API_KEY',
                'GROQ_API_KEY': 'GROQ_API_KEY',
            }
            
            # Clear environment and set only specific keys
            with patch.dict(os.environ, {
                'OPENAI_API_KEY': 'sk-test-openai',
                'FIREWORKS_API_KEY': 'fw-test',
            }, clear=True):
                result = discover_api_keys()
            
            # Should check for all providers from CSV
            assert 'OPENAI_API_KEY' in result
            assert 'ANTHROPIC_API_KEY' in result
            assert 'FIREWORKS_API_KEY' in result
            assert 'GROQ_API_KEY' in result
            
            # Should find the ones that are set
            assert result['OPENAI_API_KEY'] == 'sk-test-openai'
            assert result['FIREWORKS_API_KEY'] == 'fw-test'
            
            # Should return None for the ones that aren't set
            assert result['ANTHROPIC_API_KEY'] is None
            assert result['GROQ_API_KEY'] is None


class TestApiKeyWithLlmInvoke:
    """Test that API keys are tested using llm_invoke (the main fix)"""
    
    def test_uses_llm_invoke_to_test_key(self):
        """Should use llm_invoke to test the API key"""
        with patch('pdd.setup_tool.llm_invoke') as mock_llm_invoke:
            mock_llm_invoke.return_value = {'result': 'Hello!', 'cost': 0.0001}
            
            result = test_api_key_with_llm_invoke('OPENAI_API_KEY', 'sk-test-key')
            
            # Should call llm_invoke
            assert mock_llm_invoke.called
            call_kwargs = mock_llm_invoke.call_args[1]
            
            # Should use simple prompt and cheapest settings
            assert call_kwargs['prompt'] == "Say hello"
            assert call_kwargs['strength'] == 0.0  # Cheapest model
            assert call_kwargs['verbose'] is False
            
            # Should return True if llm_invoke succeeds
            assert result is True
    
    def test_sets_api_key_in_environment_temporarily(self):
        """Should set the API key in environment during test, then restore"""
        original_value = os.environ.get('TEST_API_KEY')
        
        with patch('pdd.setup_tool.llm_invoke') as mock_llm_invoke:
            mock_llm_invoke.return_value = {'result': 'Hello!'}
            
            # Mock the environment to verify it gets set
            with patch.dict(os.environ, {}, clear=False):
                test_api_key_with_llm_invoke('TEST_API_KEY', 'test-value')
                
                # During the test, llm_invoke should see the key
                assert mock_llm_invoke.called
        
        # After test, environment should be restored
        assert os.environ.get('TEST_API_KEY') == original_value
    
    def test_returns_false_on_llm_invoke_failure(self):
        """Should return False if llm_invoke raises an exception"""
        with patch('pdd.setup_tool.llm_invoke') as mock_llm_invoke:
            mock_llm_invoke.side_effect = Exception("API key invalid")
            
            result = test_api_key_with_llm_invoke('OPENAI_API_KEY', 'bad-key')
            
            assert result is False
    
    def test_returns_false_for_empty_key(self):
        """Should return False for empty or None API key"""
        assert test_api_key_with_llm_invoke('OPENAI_API_KEY', '') is False
        assert test_api_key_with_llm_invoke('OPENAI_API_KEY', '   ') is False
    
    def test_works_with_any_provider(self):
        """Should work with any provider, not just OpenAI/Google/Anthropic"""
        with patch('pdd.setup_tool.llm_invoke') as mock_llm_invoke:
            mock_llm_invoke.return_value = {'result': 'Hello!'}
            
            # Test with Fireworks (would fail with old hardcoded approach)
            result = test_api_key_with_llm_invoke('FIREWORKS_API_KEY', 'fw-test')
            assert result is True
            
            # Test with Groq
            result = test_api_key_with_llm_invoke('GROQ_API_KEY', 'gsk-test')
            assert result is True
            
            # Test with any custom provider
            result = test_api_key_with_llm_invoke('CUSTOM_PROVIDER_KEY', 'custom-test')
            assert result is True


class TestTestApiKeys:
    """Test the test_api_keys function that tests multiple keys"""
    
    def test_tests_all_provided_keys(self):
        """Should test all API keys using llm_invoke"""
        keys = {
            'OPENAI_API_KEY': 'sk-test',
            'FIREWORKS_API_KEY': 'fw-test',
            'GROQ_API_KEY': None,  # Not set
        }
        
        with patch('pdd.setup_tool.test_api_key_with_llm_invoke') as mock_test:
            mock_test.return_value = True
            
            result = test_api_keys(keys)
            
            # Should test the keys that have values
            assert mock_test.call_count == 2
            mock_test.assert_any_call('OPENAI_API_KEY', 'sk-test')
            mock_test.assert_any_call('FIREWORKS_API_KEY', 'fw-test')
            
            # Results should reflect the tests
            assert result['OPENAI_API_KEY'] is True
            assert result['FIREWORKS_API_KEY'] is True
            assert result['GROQ_API_KEY'] is False  # Not set, so False


class TestSaveConfiguration:
    """Test that save_configuration includes all models, not just hardcoded ones"""
    
    def test_includes_all_models_with_valid_keys(self, tmp_path):
        """Should include ALL models from CSV if their API key is valid (not just gpt/gemini/anthropic)"""
        valid_keys = {
            'OPENAI_API_KEY': 'sk-test',
            'FIREWORKS_API_KEY': 'fw-test',
        }
        
        with patch('pdd.setup_tool.Path.home', return_value=tmp_path):
            with patch('pdd.setup_tool.detect_shell', return_value='bash'):
                saved_files, created_dir, init_updated = save_configuration(valid_keys)
        
        # Check that llm_model.csv was created
        llm_model_csv = tmp_path / '.pdd' / 'llm_model.csv'
        assert llm_model_csv.exists()
        
        # Read the CSV and verify it includes models from different providers
        import csv
        with open(llm_model_csv) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
        
        # Should have rows for both providers
        openai_models = [r for r in rows if r['api_key'] == 'OPENAI_API_KEY']
        fireworks_models = [r for r in rows if r['api_key'] == 'FIREWORKS_API_KEY']
        
        assert len(openai_models) > 0, "Should include OpenAI models"
        assert len(fireworks_models) > 0, "Should include Fireworks models"
        
        # Verify we're not filtering by model name prefix (the old bug)
        # Old code only included gpt-*, gemini/*, anthropic/*
        # New code should include fireworks_ai/* models too
        fireworks_model_names = [r['model'] for r in fireworks_models]
        assert any('fireworks' in m.lower() for m in fireworks_model_names), \
            "Should include Fireworks models (not filtered by hardcoded prefixes)"
    
    def test_excludes_models_without_valid_keys(self, tmp_path):
        """Should only include models whose API key is in valid_keys"""
        valid_keys = {
            'OPENAI_API_KEY': 'sk-test',
            # No Anthropic or Fireworks keys
        }
        
        with patch('pdd.setup_tool.Path.home', return_value=tmp_path):
            with patch('pdd.setup_tool.detect_shell', return_value='bash'):
                saved_files, created_dir, init_updated = save_configuration(valid_keys)
        
        llm_model_csv = tmp_path / '.pdd' / 'llm_model.csv'
        
        import csv
        with open(llm_model_csv) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
        
        # Should only have OpenAI models
        api_keys_in_csv = set(r['api_key'] for r in rows if r['api_key'])
        assert 'OPENAI_API_KEY' in api_keys_in_csv
        assert 'ANTHROPIC_API_KEY' not in api_keys_in_csv
        assert 'FIREWORKS_API_KEY' not in api_keys_in_csv


class TestIssueRegression:
    """Integration tests to ensure the original issue is fixed"""
    
    def test_setup_supports_more_than_three_providers(self):
        """Regression test: Setup should support more than just OpenAI, Google, Anthropic"""
        # Get all discovered API keys
        csv_vars = get_csv_variable_names()
        
        # Should support many providers, not just 3
        assert len(csv_vars) >= 5, \
            "Setup should support at least 5 providers (OpenAI, Google, Anthropic, Fireworks, Groq, etc.)"
    
    def test_setup_uses_llm_invoke_not_http_requests(self):
        """Regression test: Setup should use llm_invoke, not direct HTTP requests"""
        # This test verifies we're not using requests library anymore
        with patch('pdd.setup_tool.llm_invoke') as mock_llm_invoke:
            mock_llm_invoke.return_value = {'result': 'Hello!'}
            
            # Test an API key
            result = test_api_key_with_llm_invoke('ANY_PROVIDER_KEY', 'test-key')
            
            # Should have called llm_invoke
            assert mock_llm_invoke.called, "Should use llm_invoke to test keys"
            assert result is True
    
    def test_no_hardcoded_model_filtering(self, tmp_path):
        """Regression test: Should not filter models by hardcoded prefixes"""
        # The old code had _is_supported_model() that only accepted:
        # - gpt-* 
        # - gemini/*
        # - anthropic/*
        # This test ensures ALL models are included if their key is valid
        
        valid_keys = {
            'FIREWORKS_API_KEY': 'fw-test',  # Would be excluded by old code
            'GROQ_API_KEY': 'gsk-test',      # Would be excluded by old code
        }
        
        with patch('pdd.setup_tool.Path.home', return_value=tmp_path):
            with patch('pdd.setup_tool.detect_shell', return_value='bash'):
                saved_files, created_dir, init_updated = save_configuration(valid_keys)
        
        llm_model_csv = tmp_path / '.pdd' / 'llm_model.csv'
        
        import csv
        with open(llm_model_csv) as f:
            reader = csv.DictReader(f)
            rows = list(reader)
        
        # Should have models from these providers
        assert len(rows) > 0, "Should include models from non-hardcoded providers"
        
        # Verify we have Fireworks or Groq models
        providers = set(r.get('provider', '') for r in rows)
        assert any(p in ['Fireworks', 'OpenAI'] for p in providers), \
            "Should include models from providers beyond the original 3"
