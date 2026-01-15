"""
Test Plan for pdd.server.routes.config

1. **Router setup**:
   - Should have prefix "/api/v1/config"
   - Should have tags ["config"]

2. **CloudUrlResponse model**:
   - Should have cloud_url and environment fields
   - Should be a Pydantic BaseModel

3. **GET /cloud-url endpoint**:
   - **Case 1: Default environment**: Should return production as environment.
   - **Case 2: Custom environment**: Should respect PDD_ENV env var.
   - **Case 3: Response format**: Should return CloudUrlResponse with correct fields.
"""

import os
from unittest.mock import patch, MagicMock

import pytest
from fastapi.testclient import TestClient
from fastapi import FastAPI


@pytest.fixture
def mock_cloud_config():
    """Mock CloudConfig for testing."""
    with patch("pdd.server.routes.config.CloudConfig") as mock:
        mock.get_base_url.return_value = "https://us-central1-pdd-test.cloudfunctions.net"
        yield mock


@pytest.fixture
def app(mock_cloud_config):
    """Create a test FastAPI app with config router."""
    from pdd.server.routes.config import router

    app = FastAPI()
    app.include_router(router)
    return app


@pytest.fixture
def client(app):
    """Create a test client."""
    return TestClient(app)


# --- Router Tests ---

def test_router_prefix():
    """Should have correct prefix."""
    from pdd.server.routes.config import router
    assert router.prefix == "/api/v1/config"


def test_router_tags():
    """Should have correct tags."""
    from pdd.server.routes.config import router
    assert "config" in router.tags


# --- CloudUrlResponse Tests ---

def test_cloud_url_response_model():
    """CloudUrlResponse should have required fields."""
    from pdd.server.routes.config import CloudUrlResponse

    response = CloudUrlResponse(
        cloud_url="https://example.com",
        environment="test"
    )
    assert response.cloud_url == "https://example.com"
    assert response.environment == "test"


# --- GET /cloud-url Tests ---

def test_get_cloud_url_default_environment(client, mock_cloud_config):
    """Should return production as default environment."""
    # Ensure PDD_ENV is not set
    with patch.dict(os.environ, {}, clear=False):
        if "PDD_ENV" in os.environ:
            del os.environ["PDD_ENV"]

        response = client.get("/api/v1/config/cloud-url")

        assert response.status_code == 200
        data = response.json()
        assert data["cloud_url"] == "https://us-central1-pdd-test.cloudfunctions.net"
        assert data["environment"] == "production"


def test_get_cloud_url_custom_environment(client, mock_cloud_config):
    """Should respect PDD_ENV environment variable."""
    with patch.dict(os.environ, {"PDD_ENV": "staging"}):
        response = client.get("/api/v1/config/cloud-url")

        assert response.status_code == 200
        data = response.json()
        assert data["environment"] == "staging"


def test_get_cloud_url_response_format(client, mock_cloud_config):
    """Response should match CloudUrlResponse schema."""
    response = client.get("/api/v1/config/cloud-url")

    assert response.status_code == 200
    data = response.json()

    # Should have exactly these keys
    assert set(data.keys()) == {"cloud_url", "environment"}
    assert isinstance(data["cloud_url"], str)
    assert isinstance(data["environment"], str)
