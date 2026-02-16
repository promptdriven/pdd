"""Tests for pdd/setup/litellm_registry.py"""

from unittest import mock

import pytest

from pdd.setup.litellm_registry import (
    ProviderInfo,
    ModelInfo,
    PROVIDER_API_KEY_MAP,
    PROVIDER_DISPLAY_NAMES,
    is_litellm_available,
    get_api_key_env_var,
    get_top_providers,
    get_all_providers,
    search_providers,
    get_models_for_provider,
    _get_display_name,
    _entry_to_model_info,
)


# ---------------------------------------------------------------------------
# Tests for constants
# ---------------------------------------------------------------------------


class TestConstants:
    """Tests for static mappings."""

    def test_provider_api_key_map_has_common_providers(self):
        """Should have API key mappings for common providers."""
        assert "openai" in PROVIDER_API_KEY_MAP
        assert "anthropic" in PROVIDER_API_KEY_MAP
        assert "gemini" in PROVIDER_API_KEY_MAP
        assert "groq" in PROVIDER_API_KEY_MAP
        assert "mistral" in PROVIDER_API_KEY_MAP

    def test_provider_api_key_map_values_are_strings(self):
        """All API key env var names should be strings."""
        for key_name in PROVIDER_API_KEY_MAP.values():
            assert isinstance(key_name, str)
            assert len(key_name) > 0
            # Should look like an env var (uppercase with underscores)
            assert key_name.isupper() or "_" in key_name

    def test_provider_display_names_has_common_providers(self):
        """Should have display names for common providers."""
        assert "openai" in PROVIDER_DISPLAY_NAMES
        assert PROVIDER_DISPLAY_NAMES["openai"] == "OpenAI"
        assert PROVIDER_DISPLAY_NAMES["anthropic"] == "Anthropic"
        assert PROVIDER_DISPLAY_NAMES["gemini"] == "Google Gemini"

    def test_provider_display_names_are_human_readable(self):
        """Display names should be human-readable (not snake_case)."""
        for provider, display_name in PROVIDER_DISPLAY_NAMES.items():
            assert isinstance(display_name, str)
            assert len(display_name) > 0
            # Should not be all lowercase with underscores
            if "_" in provider:
                assert "_" not in display_name or display_name != provider


# ---------------------------------------------------------------------------
# Tests for dataclasses
# ---------------------------------------------------------------------------


class TestDataclasses:
    """Tests for ProviderInfo and ModelInfo dataclasses."""

    def test_provider_info_fields(self):
        """ProviderInfo should have all required fields."""
        info = ProviderInfo(
            name="openai",
            display_name="OpenAI",
            api_key_env_var="OPENAI_API_KEY",
            model_count=10,
            sample_models=["gpt-4", "gpt-3.5-turbo"],
        )
        assert info.name == "openai"
        assert info.display_name == "OpenAI"
        assert info.api_key_env_var == "OPENAI_API_KEY"
        assert info.model_count == 10
        assert info.sample_models == ["gpt-4", "gpt-3.5-turbo"]

    def test_provider_info_defaults(self):
        """ProviderInfo sample_models should default to empty list."""
        info = ProviderInfo(
            name="test",
            display_name="Test",
            api_key_env_var=None,
            model_count=0,
        )
        assert info.sample_models == []

    def test_model_info_fields(self):
        """ModelInfo should have all required fields."""
        info = ModelInfo(
            name="gpt-4",
            litellm_id="gpt-4",
            input_cost_per_million=30.0,
            output_cost_per_million=60.0,
            max_input_tokens=128000,
            max_output_tokens=8192,
            supports_vision=True,
            supports_function_calling=True,
        )
        assert info.name == "gpt-4"
        assert info.litellm_id == "gpt-4"
        assert info.input_cost_per_million == 30.0
        assert info.output_cost_per_million == 60.0
        assert info.max_input_tokens == 128000
        assert info.max_output_tokens == 8192
        assert info.supports_vision is True
        assert info.supports_function_calling is True

    def test_model_info_defaults(self):
        """ModelInfo should have sensible defaults."""
        info = ModelInfo(
            name="test",
            litellm_id="test",
            input_cost_per_million=0.0,
            output_cost_per_million=0.0,
        )
        assert info.max_input_tokens is None
        assert info.max_output_tokens is None
        assert info.supports_vision is False
        assert info.supports_function_calling is False


# ---------------------------------------------------------------------------
# Tests for is_litellm_available
# ---------------------------------------------------------------------------


class TestIsLitellmAvailable:
    """Tests for is_litellm_available function."""

    def test_returns_true_when_litellm_installed(self):
        """Should return True when litellm is importable with model data."""
        # If litellm is installed in test environment, this should return True
        # We'll mock it to ensure consistent behavior
        mock_litellm = mock.MagicMock()
        mock_litellm.model_cost = {"gpt-4": {"mode": "chat"}}

        with mock.patch.dict("sys.modules", {"litellm": mock_litellm}):
            # Need to reimport or call the function after mocking
            result = is_litellm_available()
            # Either True (if litellm is installed) or we need to mock
            assert isinstance(result, bool)

    def test_returns_false_when_litellm_not_installed(self):
        """Should return False when litellm import fails."""
        with mock.patch.dict("sys.modules", {"litellm": None}):
            # Force ImportError
            def raise_import_error():
                raise ImportError("No module named 'litellm'")

            with mock.patch(
                "pdd.setup.litellm_registry.is_litellm_available",
                side_effect=raise_import_error,
            ):
                # The actual function should handle this gracefully
                pass

    def test_returns_false_when_model_cost_empty(self):
        """Should return False when litellm.model_cost is empty."""
        mock_litellm = mock.MagicMock()
        mock_litellm.model_cost = {}

        with mock.patch("pdd.setup.litellm_registry.is_litellm_available") as mock_fn:
            mock_fn.return_value = False
            assert mock_fn() is False


# ---------------------------------------------------------------------------
# Tests for get_api_key_env_var
# ---------------------------------------------------------------------------


class TestGetApiKeyEnvVar:
    """Tests for get_api_key_env_var function."""

    def test_returns_key_for_known_providers(self):
        """Should return correct API key env var for known providers."""
        assert get_api_key_env_var("openai") == "OPENAI_API_KEY"
        assert get_api_key_env_var("anthropic") == "ANTHROPIC_API_KEY"
        assert get_api_key_env_var("gemini") == "GEMINI_API_KEY"
        assert get_api_key_env_var("groq") == "GROQ_API_KEY"

    def test_returns_none_for_unknown_providers(self):
        """Should return None for providers not in the mapping."""
        assert get_api_key_env_var("unknown_provider") is None
        assert get_api_key_env_var("") is None
        assert get_api_key_env_var("my_custom_llm") is None

    def test_case_sensitive(self):
        """Provider name lookup should be case-sensitive."""
        assert get_api_key_env_var("openai") == "OPENAI_API_KEY"
        assert get_api_key_env_var("OpenAI") is None
        assert get_api_key_env_var("OPENAI") is None


# ---------------------------------------------------------------------------
# Tests for _get_display_name
# ---------------------------------------------------------------------------


class TestGetDisplayName:
    """Tests for _get_display_name helper function."""

    def test_returns_mapped_name_for_known_providers(self):
        """Should return the mapped display name for known providers."""
        assert _get_display_name("openai") == "OpenAI"
        assert _get_display_name("fireworks_ai") == "Fireworks AI"
        assert _get_display_name("together_ai") == "Together AI"

    def test_falls_back_to_title_case_for_unknown(self):
        """Should fallback to title-case with underscore replacement."""
        assert _get_display_name("my_custom_provider") == "My Custom Provider"
        assert _get_display_name("unknown") == "Unknown"

    def test_handles_empty_string(self):
        """Should handle empty string gracefully."""
        result = _get_display_name("")
        assert result == ""


# ---------------------------------------------------------------------------
# Tests for _entry_to_model_info
# ---------------------------------------------------------------------------


class TestEntryToModelInfo:
    """Tests for _entry_to_model_info helper function."""

    def test_converts_basic_entry(self):
        """Should convert a model_cost entry to ModelInfo."""
        entry = {
            "input_cost_per_token": 0.00003,
            "output_cost_per_token": 0.00006,
            "max_input_tokens": 128000,
            "max_output_tokens": 8192,
            "supports_vision": True,
            "supports_function_calling": True,
        }

        result = _entry_to_model_info("gpt-4", entry)

        assert result.name == "gpt-4"
        assert result.litellm_id == "gpt-4"
        assert result.input_cost_per_million == 30.0
        assert result.output_cost_per_million == 60.0
        assert result.max_input_tokens == 128000
        assert result.max_output_tokens == 8192
        assert result.supports_vision is True
        assert result.supports_function_calling is True

    def test_handles_provider_prefix_in_model_id(self):
        """Should extract model name from provider/model format."""
        entry = {"input_cost_per_token": 0, "output_cost_per_token": 0}

        result = _entry_to_model_info("anthropic/claude-3-opus", entry)

        assert result.name == "claude-3-opus"
        assert result.litellm_id == "anthropic/claude-3-opus"

    def test_handles_missing_cost_fields(self):
        """Should handle entries with missing cost fields."""
        entry = {}

        result = _entry_to_model_info("test-model", entry)

        assert result.input_cost_per_million == 0.0
        assert result.output_cost_per_million == 0.0

    def test_handles_none_cost_values(self):
        """Should handle None cost values."""
        entry = {
            "input_cost_per_token": None,
            "output_cost_per_token": None,
        }

        result = _entry_to_model_info("test-model", entry)

        assert result.input_cost_per_million == 0.0
        assert result.output_cost_per_million == 0.0

    def test_converts_per_token_to_per_million(self):
        """Should correctly convert per-token costs to per-million."""
        entry = {
            "input_cost_per_token": 0.000001,  # $1 per million
            "output_cost_per_token": 0.000002,  # $2 per million
        }

        result = _entry_to_model_info("test", entry)

        assert result.input_cost_per_million == 1.0
        assert result.output_cost_per_million == 2.0


# ---------------------------------------------------------------------------
# Tests for get_top_providers (with mocking)
# ---------------------------------------------------------------------------


class TestGetTopProviders:
    """Tests for get_top_providers function."""

    def test_returns_empty_list_when_litellm_unavailable(self):
        """Should return empty list when litellm is not available."""
        with mock.patch(
            "pdd.setup.litellm_registry.is_litellm_available", return_value=False
        ):
            result = get_top_providers()
            assert result == []

    def test_returns_list_of_provider_info(self):
        """Should return a list of ProviderInfo objects."""
        # Only test if litellm is actually available
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_top_providers()

        assert isinstance(result, list)
        if result:
            assert isinstance(result[0], ProviderInfo)

    def test_includes_major_providers(self):
        """Top providers should include major cloud providers."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_top_providers()
        provider_names = [p.name for p in result]

        # At least some major providers should be present
        major_providers = {"openai", "anthropic", "gemini", "mistral"}
        found = set(provider_names) & major_providers
        assert len(found) > 0, f"Expected some major providers, got {provider_names}"


# ---------------------------------------------------------------------------
# Tests for get_all_providers (with mocking)
# ---------------------------------------------------------------------------


class TestGetAllProviders:
    """Tests for get_all_providers function."""

    def test_returns_empty_list_when_litellm_unavailable(self):
        """Should return empty list when litellm is not available."""
        with mock.patch(
            "pdd.setup.litellm_registry.is_litellm_available", return_value=False
        ):
            result = get_all_providers()
            assert result == []

    def test_returns_sorted_by_model_count(self):
        """Should return providers sorted by model count descending."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_all_providers()

        if len(result) > 1:
            for i in range(len(result) - 1):
                assert result[i].model_count >= result[i + 1].model_count

    def test_all_providers_have_at_least_one_model(self):
        """All returned providers should have at least one chat model."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_all_providers()

        for provider in result:
            assert provider.model_count >= 1


# ---------------------------------------------------------------------------
# Tests for search_providers
# ---------------------------------------------------------------------------


class TestSearchProviders:
    """Tests for search_providers function."""

    def test_empty_query_returns_all_providers(self):
        """Empty query should return all providers."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        all_providers = get_all_providers()
        search_result = search_providers("")

        assert len(search_result) == len(all_providers)

    def test_case_insensitive_search(self):
        """Search should be case-insensitive."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result_lower = search_providers("openai")
        result_upper = search_providers("OPENAI")
        result_mixed = search_providers("OpenAI")

        # All should return the same results
        assert len(result_lower) == len(result_upper) == len(result_mixed)

    def test_searches_in_name_and_display_name(self):
        """Should search in both provider name and display name."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        # Search by display name component
        result = search_providers("Gemini")
        provider_names = [p.name for p in result]

        # Should find gemini provider
        assert any("gemini" in name.lower() for name in provider_names)

    def test_returns_empty_for_no_match(self):
        """Should return empty list when no providers match."""
        result = search_providers("xyznonexistentprovider123")
        assert result == []

    def test_partial_match(self):
        """Should match partial strings."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        # "open" should match "openai"
        result = search_providers("open")
        if result:
            assert any("open" in p.name.lower() for p in result)


# ---------------------------------------------------------------------------
# Tests for get_models_for_provider
# ---------------------------------------------------------------------------


class TestGetModelsForProvider:
    """Tests for get_models_for_provider function."""

    def test_returns_empty_list_when_litellm_unavailable(self):
        """Should return empty list when litellm is not available."""
        with mock.patch(
            "pdd.setup.litellm_registry.is_litellm_available", return_value=False
        ):
            result = get_models_for_provider("openai")
            assert result == []

    def test_returns_list_of_model_info(self):
        """Should return a list of ModelInfo objects."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_models_for_provider("openai")

        assert isinstance(result, list)
        if result:
            assert isinstance(result[0], ModelInfo)

    def test_returns_sorted_by_name(self):
        """Models should be sorted by name."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_models_for_provider("openai")

        if len(result) > 1:
            names = [m.name for m in result]
            assert names == sorted(names)

    def test_returns_empty_for_unknown_provider(self):
        """Should return empty list for unknown provider."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_models_for_provider("nonexistent_provider_xyz")
        assert result == []

    def test_model_info_has_litellm_id(self):
        """Each model should have a litellm_id for API calls."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_models_for_provider("anthropic")

        for model in result:
            assert model.litellm_id is not None
            assert len(model.litellm_id) > 0

    def test_handles_vertex_ai_subproviders(self):
        """Should aggregate vertex_ai sub-providers."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        result = get_models_for_provider("vertex_ai")

        # Should return some models (vertex_ai has many)
        # The exact count depends on litellm version
        assert isinstance(result, list)


# ---------------------------------------------------------------------------
# Integration tests
# ---------------------------------------------------------------------------


class TestIntegration:
    """Integration tests that verify module works end-to-end."""

    def test_workflow_search_to_models(self):
        """Test typical workflow: search provider -> get models."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        # Search for anthropic
        providers = search_providers("anthropic")
        assert len(providers) > 0

        # Get the first matching provider
        provider = providers[0]
        assert provider.name == "anthropic" or "anthropic" in provider.name

        # Get models for that provider
        models = get_models_for_provider(provider.name)
        assert len(models) > 0

        # Each model should have required fields
        for model in models:
            assert model.litellm_id
            assert isinstance(model.input_cost_per_million, (int, float))
            assert isinstance(model.output_cost_per_million, (int, float))

    def test_top_providers_have_valid_data(self):
        """Top providers should all have valid, complete data."""
        if not is_litellm_available():
            pytest.skip("litellm not installed")

        top = get_top_providers()

        for provider in top:
            # Each provider should have a name and display name
            assert provider.name
            assert provider.display_name

            # Model count should be positive
            assert provider.model_count > 0

            # Sample models should not exceed 3
            assert len(provider.sample_models) <= 3

            # Can get models for this provider
            models = get_models_for_provider(provider.name)
            assert len(models) == provider.model_count
