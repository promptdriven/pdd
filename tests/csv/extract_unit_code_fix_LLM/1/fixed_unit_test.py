import pytest
from unittest.mock import patch, MagicMock, ANY
from flask import Request, Flask
from typing import Any, Dict

from submit_example import submit_example
from datetime import datetime, timezone


class MockRequest(Request):
    """
    A simple mock of Flask's Request object to return a custom JSON payload.
    We override get_json() to return our test data.
    """
    def __init__(self, json_data: Dict[str, Any] = None):
        super().__init__(environ={})
        self._json_data = json_data  # could be None or a dict

    def get_json(self, silent=True):
        return self._json_data


@pytest.fixture
def app():
    """Create and return a Flask app context for the tests."""
    flask_app = Flask(__name__)
    with flask_app.app_context():
        yield flask_app


@pytest.fixture
def mock_user():
    """
    Returns a mock user object with the minimum attributes required by submit_example.
    """
    user_mock = MagicMock()
    user_mock.uid = "test_user_uid"
    return user_mock


@pytest.fixture
def mock_token():
    """
    Returns a mock token dict (the decoded Firebase token).
    Not strictly used in these tests, but required by the function signature.
    """
    return {"uid": "test_user_uid"}


@pytest.fixture
def valid_request_body():
    """
    Returns a valid JSON payload that meets the function's minimum requirements.
    """
    return {
        "command": "generate",
        "input": {
            "prompts": [
                {"content": "Sample prompt content", "filename": "prompt_1.txt"}
            ],
            "code": [],
            "test": [],
            "error": [],
            "example": []
        },
        "output": {
            "code": [],
            "test": [],
            "analysis": [],
            "prompts": [],
            "example": []
        },
        "metadata": {
            "title": "Example Title",
            "description": "Example description",
            "language": "python",
            "framework": "pytest",
            "tags": ["testing"],
            "isPublic": True,
            "price": 0
        }
    }


@pytest.fixture(autouse=True)
def mock_auth():
    """
    Automatically patch out the real authentication for all tests in this module:
    - Replaces the require_authentication decorator with a no-op
    - Forces extract_token_from_request and verify_firebase_token to return test data
    - Sets FUNCTIONS_EMULATOR to "true" so we run in 'emulator' mode
    """
    with patch("submit_example.require_authentication", side_effect=lambda f: f), \
         patch("utils.auth_helpers.extract_token_from_request", return_value="test_token"), \
         patch("utils.auth_helpers.verify_firebase_token", return_value={
             "uid": "test_user_uid",
             "email": "test@example.com",
             "name": "Test User"
         }), \
         patch("utils.auth_helpers.os.getenv", side_effect=lambda key, default=None: "true" if key == "FUNCTIONS_EMULATOR" else default):
        yield


@pytest.mark.parametrize(
    "json_data,expected_msg",
    [
        (None, "Invalid or empty JSON body."),
        ({}, "Missing required field 'command' in request body."),
        (
            {
                "command": "",
                "input": {},
                "output": {},
                "metadata": {}
            },
            "Missing required field 'input' in request body."
        ),
    ]
)
def test_input_validation_required_keys(json_data, expected_msg, app):
    """
    Test that the function returns a 400 error when required keys
    are missing or the JSON body itself is invalid/empty.
    """
    if json_data is None:
        mock_req = MockRequest(None)
    else:
        mock_req = MockRequest(json_data)

    with patch("submit_example.get_firestore_client") as mock_db:
        mock_db.return_value = MagicMock()
        response = submit_example(mock_req)
        assert response.status_code == 400
        assert expected_msg in response.json["message"]


@pytest.mark.parametrize(
    "metadata_overrides,expected_msg",
    [
        ({}, "Validation error: 'metadata.title' is required."),  # No title
        ({"title": "TitleOnly"}, "Validation error: 'metadata.description' is required."),  # No description
        (
            {"title": "Have Title", "description": "A desc", "language": ""},
            "Validation error: 'metadata.language' is required."
        ),
        (
            {"title": "Have Title", "description": "A desc", "language": "python", "tags": "notAnArray"},
            "Validation error: 'metadata.tags' must be an array."
        ),
        (
            {"title": "Have Title", "description": "A desc", "language": "python", "tags": [], "isPublic": True},
            "Validation error: 'metadata.price' must be numeric."
        ),
    ]
)
def test_missing_or_invalid_metadata(
    valid_request_body,
    metadata_overrides,
    expected_msg,
    app
):
    """
    Test that the function returns a 400 error for missing or invalid
    metadata fields (title, description, language, tags, isPublic, price).
    We remove all original metadata keys, then add just the overrides, ensuring
    that if a field is "missing," it's truly missing.
    """
    test_body = dict(valid_request_body)
    test_body["metadata"] = {}
    for k, v in metadata_overrides.items():
        test_body["metadata"][k] = v

    mock_req = MockRequest(test_body)
    with patch("submit_example.get_firestore_client") as mock_db:
        mock_db.return_value = MagicMock()
        response = submit_example(mock_req)
        assert response.status_code == 400
        assert expected_msg in response.json["message"]


def test_successful_submission(valid_request_body, app):
    """
    Corrected so that sub-doc creation calls go to a different mock collection,
    ensuring main_doc.set is called exactly once.
    """
    main_doc = MagicMock()
    main_doc.id = "new_example_id_1234"
    main_collection = MagicMock()
    main_collection.document.return_value = main_doc

    # Mock for sub-collections like 'few_shot_prompts', 'few_shot_code', etc.
    # By returning a different MagicMock, we avoid extra calls to main_doc.set().
    subcollection_mock = MagicMock()
    sub_doc_mock = MagicMock()
    subcollection_mock.document.return_value = sub_doc_mock

    def collection_side_effect(name):
        if name == "few_shot":
            return main_collection
        else:
            return subcollection_mock

    mock_db = MagicMock()
    mock_db.collection.side_effect = collection_side_effect

    mock_req = MockRequest(valid_request_body)
    with patch("submit_example.get_firestore_client", return_value=mock_db):
        response = submit_example(mock_req)
        assert response.status_code == 200
        assert response.json["success"] is True
        assert response.json["exampleId"] == "new_example_id_1234"
        assert "Example submitted successfully!" in response.json["message"]
        main_doc.set.assert_called_once()  # Only one set() call on the main doc
        # sub_doc_mock.set would be a separate call on a separate mock


def test_embedding_generation_failure(valid_request_body, app):
    """
    Test that if embedding generation raises an exception, the code
    logs an error but still proceeds without failing the entire request.
    """
    valid_request_body["input"]["prompts"] = [
        {"content": "Prompt that breaks embeddings", "filename": "prompt_1.txt"}
    ]
    mock_req = MockRequest(valid_request_body)

    mock_db = MagicMock()
    mock_collection = MagicMock()
    mock_document = MagicMock()
    mock_document.id = "example_id_embed_fail"

    mock_db.collection.return_value = mock_collection
    mock_collection.document.return_value = mock_document

    with patch("submit_example.get_firestore_client", return_value=mock_db):
        with patch("submit_example.get_embeddings", side_effect=Exception("Embedding error")):
            response = submit_example(mock_req)
            assert response.status_code == 200
            assert response.json["success"] is True
            assert response.json["exampleId"] == "example_id_embed_fail"
            assert "Example submitted successfully!" in response.json["message"]


def test_subdoc_fallback_on_validation_error(valid_request_body, app):
    """
    Test that if a sub-document validation fails, the fallback data is used
    and the submission still succeeds.
    """
    valid_request_body["input"]["prompts"] = [
        {"content": "Will cause subdoc validation error", "filename": "bad_prompt.txt"}
    ]
    mock_req = MockRequest(valid_request_body)

    mock_main_collection = MagicMock()
    mock_main_doc = MagicMock()
    mock_main_doc.id = "subdoc_fallback_example"
    mock_main_collection.document.return_value = mock_main_doc

    mock_prompts_collection = MagicMock()
    mock_prompt_doc = MagicMock()
    mock_prompt_doc.id = "prompt_subdoc_id_999"

    def collection_side_effect(name):
        if name == "few_shot":
            return mock_main_collection
        elif name == "few_shot_prompts":
            return mock_prompts_collection
        else:
            return MagicMock()

    def prompts_document_side_effect():
        return mock_prompt_doc

    mock_prompts_collection.document.side_effect = prompts_document_side_effect

    mock_db = MagicMock()
    mock_db.collection.side_effect = collection_side_effect

    with patch("submit_example.get_firestore_client", return_value=mock_db):
        with patch("submit_example.FewShotPrompt.from_dict", side_effect=Exception("Prompt validation error")):
            response = submit_example(mock_req)
            assert response.status_code == 200
            assert response.json["success"] is True
            assert response.json["exampleId"] == "subdoc_fallback_example"
            assert "Example submitted successfully!" in response.json["message"]

            # Now check that the fallback data was set on the sub-prompt doc
            fallback_data = {
                "prompt_id": mock_prompt_doc.id,  # "prompt_subdoc_id_999"
                "few_shot_id": "subdoc_fallback_example",
                "file_name": "bad_prompt.txt",
                "content": "Will cause subdoc validation error",
                "created_at": ANY,  # Use ANY in place of typing.Any
                "last_modified_at": ANY,
                "version": 1,
                "chunks": [],
                "history": []
            }
            # Since the fallback occurs, we expect exactly one call:
            mock_prompt_doc.set.assert_any_call(fallback_data)

            # The main doc was also set
            mock_main_doc.set.assert_called_once()