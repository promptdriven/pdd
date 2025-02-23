import logging
from datetime import datetime, timezone
from typing import Any, Dict, List
from flask import jsonify, Request

# Firebase / Firestore imports
from firebase_admin import firestore

# Project-specific imports
from utils.auth_helpers import (
    get_authenticated_user,
    extract_token_from_request,
    verify_firebase_token,
)
from utils.error_handling import ValidationError, AuthenticationError
from utils.firebase_helpers import get_firestore_client
from utils.auth_helpers import require_authentication

# Models for FewShot and sub-documents
from models.few_shot import FewShot, Metadata, Embeddings, EmbeddingVector, SearchMeta, ContentRefs
from models.few_shot_prompts import FewShotPrompt
from models.few_shot_code import FewShotCode
from models.few_shot_tests import FewShotTest
from models.few_shot_errors import FewShotError
from models.few_shot_analysis import FewShotAnalysis

# Optional vector embedding helper
try:
    from utils.vector_helpers import get_embeddings
except ImportError:
    # Fallback if vector_helpers is not available
    def get_embeddings(text: str) -> list:
        # Dummy embedding generator as fallback
        return [0.0] * 8

logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

def create_subdoc_if_present(
    subcollection_name: str,
    items: List[Dict[str, Any]],
    model_class,
    doc_key: str,
    new_example_id: str,
    now: datetime
) -> List[Any]:
    """
    Creates sub-documents in the given subcollection for each content/filename pair.
    Uses model_class.from_dict() to validate. If validation fails,
    writes a fallback dictionary that ensures all required fields are present
    (with exact field names matching the model).
    """
    refs = []
    db = get_firestore_client()

    for item in items:
        if item.get("content"):
            sub_ref = db.collection(subcollection_name).document()
            try:
                # Base dictionary that might match the model fields if user-supplied data is fine
                base_dict = {
                    "content": item["content"],
                    "created_at": now,
                    "last_modified_at": now,
                    "version": 1,
                }
                base_dict["file_name"] = item.get("filename", f"unnamed_{doc_key}.txt")

                # Model-specific fields
                if model_class.__name__ == "FewShotPrompt":
                    base_dict["prompt_id"] = sub_ref.id
                    base_dict["few_shot_id"] = new_example_id
                    base_dict["file_name"] = base_dict.get("file_name", "unnamed_prompt.txt")
                elif model_class.__name__ == "FewShotCode":
                    base_dict["code_id"] = sub_ref.id
                    base_dict["few_shot_id"] = new_example_id
                    base_dict["file_name"] = base_dict.pop("file_name", "unnamed_code.py")
                    base_dict["type"] = "other"
                    base_dict["language"] = item.get("language", "")
                elif model_class.__name__ == "FewShotTest":
                    base_dict["test_id"] = sub_ref.id
                    base_dict["few_shot_id"] = new_example_id
                    base_dict["file_name"] = base_dict.get("file_name", "unnamed_test.py")
                    base_dict["type"] = "input"
                    base_dict["framework"] = item.get("framework", "pytest")
                elif model_class.__name__ == "FewShotAnalysis":
                    base_dict["analysisId"] = sub_ref.id
                    base_dict["fewShotId"] = new_example_id
                    base_dict["analysisType"] = "performance"
                    base_dict["metrics"] = {}
                    base_dict["createdAt"] = base_dict.pop("created_at", now)
                    base_dict["lastModifiedAt"] = base_dict.pop("last_modified_at", now)
                elif model_class.__name__ == "FewShotError":
                    base_dict["error_id"] = sub_ref.id
                    base_dict["few_shot_id"] = new_example_id
                    base_dict["file_name"] = base_dict.get("file_name", "unnamed_error.txt")
                    base_dict["stack_trace"] = None
                    base_dict["error_type"] = "RuntimeError"
                    base_dict["resolved"] = False

                # Attempt to instantiate the model
                sub_obj = model_class.from_dict(base_dict)
                sub_obj.validate()
                sub_ref.set(sub_obj.to_dict())
                refs.append(sub_ref)

            except Exception as ex:
                # If validation failed, build fallback_data that EXACTLY matches each model's required fields
                fallback_data = {}

                if model_class.__name__ == "FewShotPrompt":
                    fallback_data["prompt_id"] = sub_ref.id
                    fallback_data["few_shot_id"] = new_example_id
                    fallback_data["file_name"] = item.get("filename", f"unnamed_{doc_key}.txt")
                    fallback_data["content"] = item.get("content", "")
                    fallback_data["created_at"] = now
                    fallback_data["last_modified_at"] = now
                    fallback_data["version"] = 1
                    fallback_data["chunks"] = []
                    fallback_data["history"] = []

                elif model_class.__name__ == "FewShotCode":
                    fallback_data["code_id"] = sub_ref.id
                    fallback_data["few_shot_id"] = new_example_id
                    fallback_data["file_name"] = item.get("filename", f"unnamed_{doc_key}.py")
                    fallback_data["content"] = item.get("content", "")
                    fallback_data["type"] = "other"
                    fallback_data["created_at"] = now
                    fallback_data["last_modified_at"] = now
                    fallback_data["version"] = 1
                    fallback_data["language"] = item.get("language", "")
                    fallback_data["framework"] = ""
                    fallback_data["history"] = []

                elif model_class.__name__ == "FewShotAnalysis":
                    fallback_data["analysisId"] = sub_ref.id
                    fallback_data["fewShotId"] = new_example_id
                    fallback_data["analysisType"] = "performance"
                    fallback_data["metrics"] = {}
                    fallback_data["content"] = item.get("content", "")
                    fallback_data["createdAt"] = now
                    fallback_data["lastModifiedAt"] = now

                elif model_class.__name__ == "FewShotTest":
                    fallback_data["test_id"] = sub_ref.id
                    fallback_data["few_shot_id"] = new_example_id
                    fallback_data["file_name"] = item.get("filename", f"unnamed_{doc_key}.py")
                    fallback_data["content"] = item.get("content", "")
                    fallback_data["type"] = "input"
                    fallback_data["created_at"] = now
                    fallback_data["last_modified_at"] = now
                    fallback_data["version"] = 1
                    fallback_data["framework"] = "pytest"
                    fallback_data["history"] = []

                elif model_class.__name__ == "FewShotError":
                    fallback_data["error_id"] = sub_ref.id
                    fallback_data["few_shot_id"] = new_example_id
                    fallback_data["file_name"] = item.get("filename", f"unnamed_{doc_key}.txt")
                    fallback_data["content"] = item.get("content", "")
                    fallback_data["created_at"] = now
                    fallback_data["last_modified_at"] = now
                    fallback_data["stack_trace"] = None
                    fallback_data["error_type"] = "RuntimeError"
                    fallback_data["resolved"] = False
                sub_ref.set(fallback_data)
                refs.append(sub_ref)
    return refs

@require_authentication
def submit_example(request: Request, user, token) -> Any:
    """
    Cloud Function entry point for creating/updating a "few_shot" example in Firestore.
    Steps:
      1) Authenticate the request using the require_authentication decorator.
      2) Parse and validate the JSON request body (command, input, output, metadata).
      3) Generate embeddings based on the prompts content.
      4) Create the main "few_shot" document (and optionally sub-documents for prompts/code/tests/etc.).
      5) Return a JSON response indicating success or error.
    Args:
        request (Request): The incoming HTTP request (Flask Request).
        user: Authenticated user object injected by the require_authentication decorator.
        token: Decoded Firebase token injected by the require_authentication decorator.
    Returns:
        Flask Response: A JSON response with status code.
    """
    db = get_firestore_client()

    # The inline authentication has been removed as authentication is now handled by the decorator.

    # 2) Parse and validate the JSON request body
    try:
        data = request.get_json(silent=True)
        # Only treat None (ie. failure to parse) as “empty”
        if data is None:
            raise ValidationError("Invalid or empty JSON body.")

        required_keys = ["command", "input", "output", "metadata"]
        for k in required_keys:
            if k not in data:
                raise ValidationError(f"Missing required field '{k}' in request body.")

        command = data["command"]
        input_data = data["input"]
        output_data = data["output"]
        metadata_data = data["metadata"]
        # Ensure that input_data has a non-empty prompts array.
        if not input_data.get("prompts") or len(input_data.get("prompts")) == 0:
            raise ValidationError("Missing required field 'input' in request body.")
        if "title" not in metadata_data or not metadata_data["title"]:
            raise ValidationError("Validation error: 'metadata.title' is required.")
        if "description" not in metadata_data:
            raise ValidationError("Validation error: 'metadata.description' is required.")
        if "language" not in metadata_data or not metadata_data["language"]:
            raise ValidationError("Validation error: 'metadata.language' is required.")
        if "tags" not in metadata_data or not isinstance(metadata_data["tags"], list):
            raise ValidationError("Validation error: 'metadata.tags' must be an array.")
        if "isPublic" not in metadata_data:
            raise ValidationError("Validation error: 'metadata.isPublic' is required.")
        if "price" not in metadata_data or not isinstance(metadata_data["price"], (int, float)):
            raise ValidationError("Validation error: 'metadata.price' must be numeric.")
    except ValidationError as ve:
        logger.error(f"Validation error: {ve.message}")
        res = jsonify({"success": False, "message": ve.message})
        res.status_code = 400
        return res
    except Exception as e:
        logger.error(f"JSON parse/validation error: {str(e)}")
        res = jsonify({"success": False, "message": "Invalid request payload."})
        res.status_code = 400
        return res

    # 3) Generate embeddings based on the prompt content
    prompt_text = ""
    if input_data.get("prompts") and len(input_data["prompts"]) > 0:
        prompt_text = input_data["prompts"][0].get("content", "")
    
    embedding_list = []
    if prompt_text:
        try:
            embedding_list = get_embeddings(prompt_text)
        except Exception as e:
            logger.error(f"Failed to generate embeddings: {str(e)}")

    # 4) Create or update the "few_shot" document with sub-docs
    few_shot_ref = db.collection("few_shot").document()
    new_example_id = few_shot_ref.id
    input_refs: Dict[str, List[Any]] = {}
    output_refs: Dict[str, List[Any]] = {}
    now = datetime.now(timezone.utc)
    input_refs["prompts"] = create_subdoc_if_present("few_shot_prompts", input_data.get("prompts", []), FewShotPrompt, "prompt", new_example_id, now)
    input_refs["code"] = create_subdoc_if_present("few_shot_code", input_data.get("code", []), FewShotCode, "code", new_example_id, now)
    input_refs["test"] = create_subdoc_if_present("few_shot_tests", input_data.get("test", []), FewShotTest, "test", new_example_id, now)
    input_refs["error"] = create_subdoc_if_present("few_shot_errors", input_data.get("error", []), FewShotError, "error", new_example_id, now)
    input_refs["example"] = create_subdoc_if_present("few_shot_code", input_data.get("example", []), FewShotCode, "example", new_example_id, now)
    output_refs["code"] = create_subdoc_if_present("few_shot_code", output_data.get("code", []), FewShotCode, "code", new_example_id, now)
    output_refs["test"] = create_subdoc_if_present("few_shot_tests", output_data.get("test", []), FewShotTest, "test", new_example_id, now)
    output_refs["analysis"] = create_subdoc_if_present("few_shot_analysis", output_data.get("analysis", []), FewShotAnalysis, "analysis", new_example_id, now)
    output_refs["prompts"] = create_subdoc_if_present("few_shot_prompts", output_data.get("prompts", []), FewShotPrompt, "prompt", new_example_id, now)
    output_refs["example"] = create_subdoc_if_present("few_shot_code", output_data.get("example", []), FewShotCode, "example", new_example_id, now)
    
    metadata_obj = Metadata(
        title=metadata_data["title"],
        description=metadata_data["description"],
        language=metadata_data["language"],
        framework=metadata_data.get("framework", ""),
        command=command,
        tags=metadata_data["tags"],
        isPublic=metadata_data["isPublic"],
        price=float(metadata_data["price"]),
        version="1.0.0"
    )
    emb_vector = EmbeddingVector(
        vector=embedding_list,
        model="text-embedding-ada-002",
        dimension=len(embedding_list),
        updatedAt=now
    )
    embeddings_obj = Embeddings(
        current=emb_vector,
        history=[]
    )
    search_meta_obj = SearchMeta(
        popularityScore=0.0,
        precomputedClusters=[],
        cachedSimilarExamples=[],
        searchFrequency={}
    )
    input_refs_obj = ContentRefs(
        prompts=input_refs["prompts"],
        code=input_refs["code"],
        test=input_refs["test"],
        error=input_refs["error"],
        example=input_refs["example"]
    )
    output_refs_obj = ContentRefs(
        code=output_refs["code"],
        test=output_refs["test"],
        analysis=output_refs["analysis"],
        prompts=output_refs["prompts"],
        example=output_refs["example"]
    )
    few_shot_obj = FewShot(
        createdAt=now,
        updatedAt=now,
        createdBy=db.collection("users").document(user.uid),
        updatedBy=db.collection("users").document(user.uid),
        metadata=metadata_obj,
        embeddings=embeddings_obj,
        searchMeta=search_meta_obj,
        inputRefs=input_refs_obj,
        outputRefs=output_refs_obj
    )
    try:
        few_shot_obj.validate()
    except ValidationError as e:
        logger.error(f"FewShot validation failed: {e.message}")
        res = jsonify({"success": False, "message": f"Validation error: {e.message}"})
        res.status_code = 400
        return res

    few_shot_data = few_shot_obj.to_dict()
    try:
        few_shot_ref.set(few_shot_data)
    except Exception as e:
        logger.error(f"Failed to create few_shot document: {str(e)}")
        res = jsonify({"success": False, "message": "Internal error creating document."})
        res.status_code = 500
        return res

    logger.info(f"Successfully created/updated example with ID: {new_example_id}")
    res = jsonify({
        "success": True,
        "exampleId": str(new_example_id),
        "message": "Example submitted successfully!"
    })
    res.status_code = 200
    return res