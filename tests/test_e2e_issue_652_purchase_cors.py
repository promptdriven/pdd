"""E2E tests for Issue #652: Purchase fails with CORS violation / Mock API in production.

These tests exercise the full system paths that a user's browser would take
when attempting a PDDC purchase from promptdriven.ai:

1. CORS E2E: A real FastAPI app with configure_cors() handles actual HTTP
   preflight and cross-origin requests, verifying the Access-Control-Allow-Origin
   header is present for the production domain.

2. Cloud endpoint resolution E2E: The full CloudConfig pipeline resolves
   the processPddcPurchase endpoint to a real production URL, not a mock
   fallback, exercising environment detection, base URL resolution, and
   endpoint registry lookup end-to-end.
"""

import os
import pytest
from unittest.mock import patch

from fastapi import FastAPI
from fastapi.testclient import TestClient

from pdd.server.security import configure_cors
from pdd.core.cloud import (
    CloudConfig,
    CLOUD_ENDPOINTS,
    DEFAULT_BASE_URL,
    PDD_CLOUD_URL_ENV,
    PDD_JWT_TOKEN_ENV,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def clean_env():
    """Ensure a clean environment for cloud config tests."""
    original_env = os.environ.copy()
    keys_to_clear = [
        PDD_CLOUD_URL_ENV, PDD_JWT_TOKEN_ENV,
        "PDD_ENV", "PDD_FORCE_LOCAL",
        "K_SERVICE", "FUNCTIONS_EMULATOR",
        "FIREBASE_AUTH_EMULATOR_HOST", "FIREBASE_EMULATOR_HUB",
        "NEXT_PUBLIC_FIREBASE_API_KEY", "GITHUB_CLIENT_ID",
    ]
    for key in keys_to_clear:
        os.environ.pop(key, None)
    yield
    os.environ.clear()
    os.environ.update(original_env)


@pytest.fixture
def cors_app():
    """Create a real FastAPI app with default CORS configuration."""
    app = FastAPI()

    # Apply the real configure_cors with default origins
    configure_cors(app)

    @app.get("/api/health")
    def health():
        return {"status": "ok"}

    @app.post("/api/purchase")
    def purchase():
        return {"status": "success"}

    return app


# ---------------------------------------------------------------------------
# E2E Test 1: CORS preflight from production origin
# ---------------------------------------------------------------------------

class TestCorsProductionOriginE2E:
    """E2E: Verify that a browser on promptdriven.ai can make cross-origin requests."""

    def test_preflight_request_from_production_origin(self, cors_app):
        """Simulate a browser OPTIONS preflight from https://promptdriven.ai.

        The browser sends an OPTIONS request with Origin header before the
        actual POST to processPddcPurchase. If CORS doesn't include the
        production origin, the preflight fails and the purchase never happens.

        This test FAILS on buggy code because configure_cors() defaults only
        include localhost origins.
        """
        client = TestClient(cors_app)
        response = client.options(
            "/api/purchase",
            headers={
                "Origin": "https://promptdriven.ai",
                "Access-Control-Request-Method": "POST",
                "Access-Control-Request-Headers": "Authorization, Content-Type",
            },
        )

        # The CORS middleware must respond with the production origin
        allow_origin = response.headers.get("access-control-allow-origin", "")
        assert allow_origin == "https://promptdriven.ai", (
            f"Preflight response must include 'https://promptdriven.ai' in "
            f"Access-Control-Allow-Origin. Got: '{allow_origin}'"
        )

    def test_cors_header_on_actual_post_from_production(self, cors_app):
        """Simulate the actual POST request from the production origin.

        After preflight passes, the browser sends the real request. The
        response must include the Access-Control-Allow-Origin header.
        """
        client = TestClient(cors_app)
        response = client.post(
            "/api/purchase",
            headers={"Origin": "https://promptdriven.ai"},
        )

        allow_origin = response.headers.get("access-control-allow-origin", "")
        assert allow_origin == "https://promptdriven.ai", (
            f"POST response must include 'https://promptdriven.ai' in "
            f"Access-Control-Allow-Origin. Got: '{allow_origin}'"
        )
        assert response.status_code == 200

    def test_cors_still_allows_localhost_development(self, cors_app):
        """Ensure localhost dev origins still work after adding production."""
        client = TestClient(cors_app)
        response = client.get(
            "/api/health",
            headers={"Origin": "http://localhost:3000"},
        )

        allow_origin = response.headers.get("access-control-allow-origin", "")
        assert allow_origin == "http://localhost:3000", (
            f"Localhost dev origin should still be allowed. Got: '{allow_origin}'"
        )

    def test_cors_rejects_unknown_origin(self, cors_app):
        """Verify that arbitrary origins are rejected (no wildcard)."""
        client = TestClient(cors_app)
        response = client.get(
            "/api/health",
            headers={"Origin": "https://evil-site.example.com"},
        )

        allow_origin = response.headers.get("access-control-allow-origin", "")
        assert allow_origin == "", (
            f"Unknown origin should be rejected. Got: '{allow_origin}'"
        )


# ---------------------------------------------------------------------------
# E2E Test 2: Full purchase endpoint resolution pipeline
# ---------------------------------------------------------------------------

class TestPurchaseEndpointResolutionE2E:
    """E2E: Verify the full pipeline from environment setup through URL resolution."""

    def test_purchase_endpoint_full_pipeline_production(self, clean_env):
        """Exercise the complete production path for processPddcPurchase.

        This simulates what happens when the web app attempts to call
        processPddcPurchase: CloudConfig resolves environment, gets base URL,
        looks up the endpoint in CLOUD_ENDPOINTS, and constructs the full URL.

        FAILS on buggy code because processPddcPurchase is missing from
        CLOUD_ENDPOINTS, causing a fallback to the default /{name} pattern.
        """
        # Step 1: Simulate production environment (inject token to trigger _ensure_default_env)
        os.environ[PDD_JWT_TOKEN_ENV] = "ey.test.token"

        # Step 2: Trigger environment detection
        CloudConfig._ensure_default_env()
        assert os.environ.get("PDD_ENV") == "prod"

        # Step 3: Verify base URL resolves to production
        base_url = CloudConfig.get_base_url()
        assert base_url == DEFAULT_BASE_URL

        # Step 4: Verify processPddcPurchase is in the endpoint registry
        assert "processPddcPurchase" in CLOUD_ENDPOINTS, (
            "processPddcPurchase must be registered in CLOUD_ENDPOINTS. "
            "Without it, mock handlers are used in production."
        )

        # Step 5: Verify full URL resolution
        url = CloudConfig.get_endpoint_url("processPddcPurchase")
        expected = f"{DEFAULT_BASE_URL}/processPddcPurchase"
        assert url == expected, (
            f"processPddcPurchase must resolve to {expected}. Got: {url}"
        )

    def test_purchase_endpoint_not_mock_url(self, clean_env):
        """Verify that the resolved purchase URL contains no mock indicators.

        The console logs from issue #652 show 'Mock API' messages, indicating
        the real endpoint was never called. This test ensures the resolved URL
        points to real cloud infrastructure.
        """
        url = CloudConfig.get_endpoint_url("processPddcPurchase")

        mock_indicators = ["mock", "localhost", "127.0.0.1", "0.0.0.0", "fake"]
        for indicator in mock_indicators:
            assert indicator not in url.lower(), (
                f"Purchase endpoint URL must not contain '{indicator}'. Got: {url}"
            )

        assert "us-central1-prompt-driven-development.cloudfunctions.net" in url

    def test_purchase_endpoint_registered_not_fallback(self, clean_env):
        """Verify processPddcPurchase is explicitly registered, not using fallback.

        When an endpoint is missing from CLOUD_ENDPOINTS, get_endpoint_url()
        falls back to /{name}. While this produces the same URL string, the
        missing registration means the endpoint is not part of the known API
        surface, enabling mock handlers to intercept instead.
        """
        # This directly checks the registry, not the URL (which looks the same)
        path = CLOUD_ENDPOINTS.get("processPddcPurchase")
        assert path is not None, (
            "processPddcPurchase is not registered in CLOUD_ENDPOINTS. "
            "It falls through to default /{name}, allowing mock interception."
        )
        assert path == "/processPddcPurchase"

    def test_all_billing_endpoints_registered(self, clean_env):
        """Verify all billing-related endpoints are in the registry.

        Prevents future regressions where new payment endpoints are added
        but not registered.
        """
        billing_endpoints = ["processPddcPurchase", "getCreditBalance"]
        missing = [ep for ep in billing_endpoints if ep not in CLOUD_ENDPOINTS]
        assert not missing, (
            f"Billing endpoints missing from CLOUD_ENDPOINTS: {missing}"
        )

    def test_environment_defaults_to_production_in_clean_state(self, clean_env):
        """Verify that with no overrides, _ensure_default_env sets prod.

        Issue #652: Mock APIs were active in production. If the environment
        detection doesn't default to 'prod', mock handlers may be activated.
        """
        CloudConfig._ensure_default_env()
        assert os.environ.get("PDD_ENV") == "prod"
