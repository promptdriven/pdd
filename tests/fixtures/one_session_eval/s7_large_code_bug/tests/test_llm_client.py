"""Tests for llm_client module."""

import json
import sys
import os
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import llm_client


class TestLoadModels(unittest.TestCase):
    def test_loads_default_models(self):
        models = llm_client.load_models()
        self.assertGreater(len(models), 10)

    def test_models_sorted_by_elo(self):
        models = llm_client.load_models()
        elos = [m.elo for m in models]
        self.assertEqual(elos, sorted(elos))

    def test_model_fields_populated(self):
        models = llm_client.load_models()
        for m in models:
            self.assertIsInstance(m.name, str)
            self.assertIsInstance(m.provider, llm_client.Provider)
            self.assertGreater(m.input_cost_per_million, 0)
            self.assertGreater(m.output_cost_per_million, 0)
            self.assertGreater(m.elo, 0)
            self.assertGreater(m.context_limit, 0)

    def test_custom_csv(self):
        csv = """name,provider,input_cost_per_m,output_cost_per_m,elo,context_limit,supports_structured,reasoning_type
test-model,openai,1.0,2.0,1000,50000,true,none"""
        models = llm_client.load_models(csv)
        self.assertEqual(len(models), 1)
        self.assertEqual(models[0].name, "test-model")


class TestModelSelection(unittest.TestCase):
    def setUp(self):
        self.models = llm_client.load_models()

    def test_strength_zero_picks_cheap(self):
        model = llm_client.select_model(self.models, 0.0)
        cheapest = min(self.models, key=lambda m: llm_client._model_score(m))
        self.assertEqual(model.name, cheapest.name)

    def test_strength_one_picks_capable(self):
        model = llm_client.select_model(self.models, 1.0)
        best = max(self.models, key=lambda m: llm_client._model_score(m))
        self.assertEqual(model.name, best.name)

    def test_strength_clamped(self):
        low = llm_client.select_model(self.models, -5.0)
        zero = llm_client.select_model(self.models, 0.0)
        self.assertEqual(low.name, zero.name)
        high = llm_client.select_model(self.models, 100.0)
        one = llm_client.select_model(self.models, 1.0)
        self.assertEqual(high.name, one.name)

    def test_filter_structured(self):
        model = llm_client.select_model(self.models, 0.5, require_structured=True)
        self.assertTrue(model.supports_structured_output)

    def test_filter_reasoning(self):
        model = llm_client.select_model(self.models, 0.5, require_reasoning=True)
        self.assertTrue(model.is_reasoning_model)


class TestContextWindowValidation(unittest.TestCase):
    def setUp(self):
        self.models = llm_client.load_models()
        self.model = self.models[0]

    def test_within_limit_passes(self):
        self.assertTrue(llm_client.validate_context_window(100, self.model))

    def test_exceeds_limit_fails(self):
        self.assertFalse(
            llm_client.validate_context_window(self.model.context_limit + 1, self.model)
        )

    def test_safety_margin_applied(self):
        validator = llm_client.ContextWindowValidator(safety_margin=0.1)
        effective = int(self.model.context_limit * 0.9)
        self.assertTrue(validator.validate(effective, self.model))
        self.assertFalse(validator.validate(effective + 1, self.model))


class TestTokenCounting(unittest.TestCase):
    def test_empty_returns_one(self):
        self.assertEqual(llm_client.count_tokens(""), 1)

    def test_simple_text(self):
        tokens = llm_client.count_tokens("hello world this is a test")
        self.assertGreater(tokens, 0)

    def test_longer_text_more_tokens(self):
        short = llm_client.count_tokens("hello")
        long = llm_client.count_tokens("hello " * 100)
        self.assertGreater(long, short)


class TestJSONExtraction(unittest.TestCase):
    def test_extract_from_fenced_block(self):
        text = 'Some text\n```json\n{"key": "value"}\n```\nMore text'
        result = llm_client.extract_json(text)
        self.assertIsNotNone(result)
        parsed = json.loads(result)
        self.assertEqual(parsed["key"], "value")

    def test_extract_bare_json(self):
        text = 'The answer is {"result": 42} as expected.'
        result = llm_client.extract_json(text)
        self.assertIsNotNone(result)
        parsed = json.loads(result)
        self.assertEqual(parsed["result"], 42)

    def test_no_json_returns_none(self):
        text = "This is just plain text with no JSON."
        result = llm_client.extract_json(text)
        self.assertIsNone(result)


class TestJSONRepair(unittest.TestCase):
    def test_repair_trailing_comma(self):
        text = '{"a": 1, "b": 2,}'
        repaired = llm_client.repair_json(text)
        parsed = json.loads(repaired)
        self.assertEqual(parsed["a"], 1)

    def test_repair_unclosed_brace(self):
        text = '{"a": 1, "b": {"c": 2}'
        repaired = llm_client.repair_json(text)
        parsed = json.loads(repaired)
        self.assertEqual(parsed["a"], 1)

    def test_repair_unclosed_string(self):
        text = '{"name": "hello'
        repaired = llm_client.repair_json(text)
        parsed = json.loads(repaired)
        self.assertEqual(parsed["name"], "hello")

    def test_repair_single_quotes(self):
        text = "{'key': 'value'}"
        repaired = llm_client.repair_json(text)
        parsed = json.loads(repaired)
        self.assertEqual(parsed["key"], "value")


class TestSchemaValidation(unittest.TestCase):
    def test_valid_object(self):
        schema = {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "age": {"type": "integer"},
            },
            "required": ["name"],
        }
        valid, errors = llm_client.validate_schema({"name": "Alice", "age": 30}, schema)
        self.assertTrue(valid)
        self.assertEqual(len(errors), 0)

    def test_missing_required(self):
        schema = {
            "type": "object",
            "properties": {"name": {"type": "string"}},
            "required": ["name"],
        }
        valid, errors = llm_client.validate_schema({}, schema)
        self.assertFalse(valid)

    def test_wrong_type(self):
        schema = {"type": "string"}
        valid, errors = llm_client.validate_schema(42, schema)
        self.assertFalse(valid)

    def test_array_validation(self):
        schema = {
            "type": "array",
            "items": {"type": "integer"},
            "minItems": 1,
        }
        valid, errors = llm_client.validate_schema([1, 2, 3], schema)
        self.assertTrue(valid)
        valid, errors = llm_client.validate_schema([], schema)
        self.assertFalse(valid)


class TestStructuredOutput(unittest.TestCase):
    def test_parse_with_schema(self):
        text = '{"result": "ok", "confidence": 0.9}'
        schema = {
            "type": "object",
            "properties": {
                "result": {"type": "string"},
                "confidence": {"type": "number"},
            },
            "required": ["result"],
        }
        parsed = llm_client.parse_structured_output(text, schema)
        self.assertEqual(parsed["result"], "ok")

    def test_parse_invalid_json_raises(self):
        with self.assertRaises(llm_client.SchemaValidationError):
            llm_client.parse_structured_output("not json at all", None)


class TestProviderConfig(unittest.TestCase):
    def setUp(self):
        self.models = llm_client.load_models()

    def test_openai_provider(self):
        provider = llm_client.get_provider(llm_client.Provider.OPENAI)
        model = next(m for m in self.models if m.provider == llm_client.Provider.OPENAI)
        request = provider.format_request("Hello", model, 0.7, 100)
        self.assertEqual(request["model"], model.name)
        self.assertIn("messages", request)

    def test_anthropic_provider(self):
        provider = llm_client.get_provider(llm_client.Provider.ANTHROPIC)
        model = next(m for m in self.models if m.provider == llm_client.Provider.ANTHROPIC)
        request = provider.format_request("Hello", model, 0.7, 100)
        self.assertEqual(request["model"], model.name)

    def test_google_provider(self):
        provider = llm_client.get_provider(llm_client.Provider.GOOGLE)
        model = next(m for m in self.models if m.provider == llm_client.Provider.GOOGLE)
        request = provider.format_request("Hello", model, 0.7, 100)
        self.assertIn("contents", request)

    def test_provider_simulate_response(self):
        for prov in llm_client.Provider:
            provider = llm_client.get_provider(prov)
            model = next(m for m in self.models if m.provider == prov)
            raw = provider.simulate_response("Hello", model)
            parsed = provider.parse_response(raw)
            self.assertIn("content", parsed)
            self.assertIn("input_tokens", parsed)
            self.assertIn("output_tokens", parsed)


class TestCaching(unittest.TestCase):
    def test_cache_hit(self):
        cache = llm_client.ResponseCache(max_size=10)
        key = cache.compute_key("prompt", "model", 0.7)
        cache.put(key, {"content": "cached response", "input_tokens": 5, "output_tokens": 3})
        result = cache.get(key)
        self.assertIsNotNone(result)
        self.assertEqual(result["content"], "cached response")

    def test_cache_miss(self):
        cache = llm_client.ResponseCache(max_size=10)
        result = cache.get("nonexistent_key")
        self.assertIsNone(result)

    def test_lru_eviction(self):
        cache = llm_client.ResponseCache(max_size=2)
        cache.put("k1", {"content": "v1"})
        cache.put("k2", {"content": "v2"})
        cache.put("k3", {"content": "v3"})
        self.assertIsNone(cache.get("k1"))
        self.assertIsNotNone(cache.get("k2"))
        self.assertIsNotNone(cache.get("k3"))

    def test_cache_stats(self):
        cache = llm_client.ResponseCache(max_size=10)
        key = cache.compute_key("p", "m", 0.5)
        cache.put(key, {"content": "val"})
        cache.get(key)
        cache.get("miss_key")
        stats = cache.stats()
        self.assertEqual(stats["hits"], 1)
        self.assertEqual(stats["misses"], 1)


class TestCostCalculation(unittest.TestCase):
    def test_basic_cost(self):
        models = llm_client.load_models()
        model = models[0]
        cost = llm_client.calculate_cost(1000, 500, model)
        expected = (1000 / 1e6) * model.input_cost_per_million + (500 / 1e6) * model.output_cost_per_million
        self.assertAlmostEqual(cost, expected)

    def test_zero_tokens_zero_cost(self):
        models = llm_client.load_models()
        cost = llm_client.calculate_cost(0, 0, models[0])
        self.assertEqual(cost, 0.0)


class TestInvoke(unittest.TestCase):
    def setUp(self):
        self.client = llm_client.LLMClient()

    def test_basic_invoke(self):
        result = self.client.invoke("Hello, world!", strength=0.5)
        self.assertIsInstance(result, llm_client.InvocationResult)
        self.assertIsInstance(result.result, str)
        self.assertGreater(len(result.result), 0)
        self.assertGreater(result.cost, 0)

    def test_invoke_with_schema(self):
        schema = {
            "type": "object",
            "properties": {
                "result": {"type": "string"},
                "confidence": {"type": "number"},
            },
        }
        result = self.client.invoke(
            "Give me a structured response",
            strength=0.5,
            output_schema=schema,
        )
        self.assertIsInstance(result, llm_client.InvocationResult)

    def test_invoke_context_overflow(self):
        models = llm_client.load_models()
        tiny_model_csv = """name,provider,input_cost_per_m,output_cost_per_m,elo,context_limit,supports_structured,reasoning_type
tiny-model,openai,0.1,0.2,800,10,true,none"""
        tiny_models = llm_client.load_models(tiny_model_csv)
        client = llm_client.LLMClient(models=tiny_models)
        with self.assertRaises(llm_client.ContextOverflowError):
            client.invoke("This prompt is definitely longer than ten tokens limit")


class TestRetryCostAccumulation(unittest.TestCase):
    """Critical test: verifies that costs from failed attempts are accumulated."""

    def test_retry_cost_accumulation(self):
        """When a request fails and is retried, the total cost must include
        the cost of ALL attempts (the failed one plus the successful retry).
        """
        config = llm_client.ClientConfig(
            retry_config=llm_client.RetryConfig(max_retries=3, base_delay=0.0, max_delay=0.0, jitter_factor=0.0),
            cache_strategy=llm_client.CacheStrategy.NONE,
        )
        client = llm_client.LLMClient(config=config)
        result = client.invoke(
            "Test prompt for retry cost",
            strength=0.3,
            bypass_cache=True,
            fail_sequence=["rate_limit", None],
        )
        self.assertEqual(result.retry_count, 1)
        single_call_result = client.invoke(
            "Test prompt for retry cost",
            strength=0.3,
            bypass_cache=True,
            fail_sequence=[None],
        )
        single_cost = single_call_result.cost
        self.assertGreater(result.cost, single_cost,
            f"Retry cost ({result.cost}) should be greater than single call cost "
            f"({single_cost}) because it includes the failed attempt's cost too. "
            f"Expected approximately {single_cost * 2}."
        )

    def test_multiple_retries_accumulate(self):
        """Multiple retries should accumulate cost from every attempt."""
        config = llm_client.ClientConfig(
            retry_config=llm_client.RetryConfig(max_retries=5, base_delay=0.0, max_delay=0.0, jitter_factor=0.0),
            cache_strategy=llm_client.CacheStrategy.NONE,
        )
        client = llm_client.LLMClient(config=config)
        result = client.invoke(
            "Test prompt for multiple retries",
            strength=0.3,
            bypass_cache=True,
            fail_sequence=["rate_limit", "timeout", None],
        )
        self.assertEqual(result.retry_count, 2)
        single_result = client.invoke(
            "Test prompt for multiple retries",
            strength=0.3,
            bypass_cache=True,
            fail_sequence=[None],
        )
        self.assertGreater(result.cost, single_result.cost,
            "Cost after 2 retries must exceed cost of a single successful call"
        )


class TestPromptFormatting(unittest.TestCase):
    def test_variable_substitution(self):
        result = llm_client.format_prompt("Hello {{name}}", {"name": "World"})
        self.assertEqual(result, "Hello World")

    def test_conditional(self):
        template = "{% if show %}visible{% endif %}"
        self.assertEqual(llm_client.format_prompt(template, {"show": True}), "visible")
        self.assertEqual(llm_client.format_prompt(template, {"show": False}), "")

    def test_loop(self):
        template = "{% for item in items %}{{item}} {% endfor %}"
        result = llm_client.format_prompt(template, {"items": ["a", "b", "c"]})
        self.assertIn("a", result)
        self.assertIn("b", result)
        self.assertIn("c", result)


class TestRetryConfig(unittest.TestCase):
    def test_exponential_backoff(self):
        config = llm_client.RetryConfig(base_delay=1.0, max_delay=60.0, jitter_factor=0.0)
        d0 = config.compute_delay(0)
        d1 = config.compute_delay(1)
        d2 = config.compute_delay(2)
        self.assertAlmostEqual(d0, 1.0)
        self.assertAlmostEqual(d1, 2.0)
        self.assertAlmostEqual(d2, 4.0)

    def test_max_delay_cap(self):
        config = llm_client.RetryConfig(base_delay=1.0, max_delay=5.0, jitter_factor=0.0)
        d10 = config.compute_delay(10)
        self.assertLessEqual(d10, 5.0)

    def test_should_retry_transient(self):
        config = llm_client.RetryConfig(max_retries=3)
        self.assertTrue(config.should_retry(llm_client.RateLimitError(), 0))
        self.assertTrue(config.should_retry(llm_client.TimeoutError(), 2))
        self.assertFalse(config.should_retry(llm_client.RateLimitError(), 3))

    def test_should_not_retry_auth(self):
        config = llm_client.RetryConfig(max_retries=3)
        self.assertFalse(config.should_retry(llm_client.AuthenticationError(), 0))


class TestErrorClassifier(unittest.TestCase):
    def test_classify_rate_limit(self):
        cat = llm_client.ErrorClassifier.classify(llm_client.RateLimitError())
        self.assertEqual(cat, llm_client.ErrorCategory.RATE_LIMIT)

    def test_classify_timeout(self):
        cat = llm_client.ErrorClassifier.classify(llm_client.TimeoutError())
        self.assertEqual(cat, llm_client.ErrorCategory.TIMEOUT)

    def test_is_transient(self):
        self.assertTrue(llm_client.ErrorClassifier.is_transient(llm_client.RateLimitError()))
        self.assertTrue(llm_client.ErrorClassifier.is_transient(llm_client.ServerError()))
        self.assertFalse(llm_client.ErrorClassifier.is_transient(llm_client.AuthenticationError()))


class TestSchemaBuilder(unittest.TestCase):
    def test_build_schema(self):
        schema = (
            llm_client.SchemaBuilder()
            .add_string("name", required=True)
            .add_number("score", required=True, minimum=0, maximum=1)
            .add_boolean("active", required=False)
            .build()
        )
        self.assertEqual(schema["type"], "object")
        self.assertIn("name", schema["properties"])
        self.assertIn("score", schema["properties"])
        self.assertIn("name", schema["required"])


class TestModelComparator(unittest.TestCase):
    def test_compare_by_cost(self):
        models = llm_client.load_models()
        comp = llm_client.ModelComparator(models)
        by_cost = comp.compare_by_cost()
        costs = [c for _, c in by_cost]
        self.assertEqual(costs, sorted(costs))

    def test_pareto_optimal(self):
        models = llm_client.load_models()
        comp = llm_client.ModelComparator(models)
        pareto = comp.find_pareto_optimal()
        self.assertGreater(len(pareto), 0)
        for i in range(1, len(pareto)):
            self.assertGreater(pareto[i].elo, pareto[i - 1].elo)


if __name__ == "__main__":
    unittest.main()
