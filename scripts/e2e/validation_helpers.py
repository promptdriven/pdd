"""
Validation helpers for E2E testing of PDD Connect remote sessions.

This module provides utilities to validate API responses from the remote session
endpoints (registerSession, listSessions, heartbeatSession, deregisterSession).
"""

from typing import Dict, Any, List
import re
import datetime


def validate_register_response(response: Dict[str, Any]) -> tuple[bool, str]:
    """
    Validate registerSession API response.

    Expected response format:
    {
        "sessionId": "uuid-string",
        "cloudUrl": "https://pdd.dev/connect/{sessionId}"
    }

    Args:
        response: The JSON response from registerSession endpoint

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    required_fields = ["sessionId", "cloudUrl"]

    # Check required fields exist
    for field in required_fields:
        if field not in response:
            return False, f"Missing required field: {field}"

    # Validate sessionId format (should be a non-empty string)
    session_id = response["sessionId"]
    if not isinstance(session_id, str) or not session_id:
        return False, f"Invalid sessionId: {session_id}"

    # Validate cloudUrl format
    cloud_url = response["cloudUrl"]
    expected_pattern = r"^https://pdd\.dev/connect/[a-zA-Z0-9_-]+$"
    if not re.match(expected_pattern, cloud_url):
        return False, f"Invalid cloudUrl format: {cloud_url}"

    # Verify cloudUrl contains sessionId
    if session_id not in cloud_url:
        return False, f"cloudUrl does not contain sessionId: {cloud_url}"

    return True, ""


def validate_list_sessions_response(response: Dict[str, Any]) -> tuple[bool, str]:
    """
    Validate listSessions API response.

    Expected response format:
    {
        "sessions": [
            {
                "sessionId": "...",
                "cloudUrl": "...",
                "projectName": "...",
                "projectPath": "...",
                "createdAt": "ISO datetime string",
                "lastHeartbeat": "ISO datetime string",
                "status": "active" | "stale",
                "metadata": {...}
            }
        ]
    }

    Args:
        response: The JSON response from listSessions endpoint

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    # Check sessions field exists
    if "sessions" not in response:
        return False, "Missing 'sessions' field in response"

    sessions = response["sessions"]
    if not isinstance(sessions, list):
        return False, f"'sessions' should be a list, got {type(sessions)}"

    # Validate each session
    for idx, session in enumerate(sessions):
        is_valid, error = validate_session_object(session)
        if not is_valid:
            return False, f"Invalid session at index {idx}: {error}"

    return True, ""


def validate_session_object(session: Dict[str, Any]) -> tuple[bool, str]:
    """
    Validate a single session object from listSessions response.

    Args:
        session: A single session object

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    required_fields = [
        "sessionId", "cloudUrl", "projectName", "projectPath",
        "createdAt", "lastHeartbeat", "status", "metadata"
    ]

    # Check required fields
    for field in required_fields:
        if field not in session:
            return False, f"Missing required field: {field}"

    # Validate sessionId
    if not isinstance(session["sessionId"], str) or not session["sessionId"]:
        return False, f"Invalid sessionId: {session['sessionId']}"

    # Validate cloudUrl
    cloud_url_pattern = r"^https://pdd\.dev/connect/[a-zA-Z0-9_-]+$"
    if not re.match(cloud_url_pattern, session["cloudUrl"]):
        return False, f"Invalid cloudUrl: {session['cloudUrl']}"

    # Validate datetime strings
    for field in ["createdAt", "lastHeartbeat"]:
        try:
            parse_datetime(session[field])
        except ValueError as e:
            return False, f"Invalid {field}: {str(e)}"

    # Validate status
    valid_statuses = ["active", "stale"]
    if session["status"] not in valid_statuses:
        return False, f"Invalid status: {session['status']} (expected one of {valid_statuses})"

    # Validate metadata is a dict
    if not isinstance(session["metadata"], dict):
        return False, f"metadata should be dict, got {type(session['metadata'])}"

    return True, ""


def validate_session_status(session: Dict[str, Any], staleness_threshold_minutes: int = 3) -> tuple[bool, str]:
    """
    Validate that a session's status matches its last_heartbeat timestamp.

    A session should be:
    - "active" if last_heartbeat is within staleness_threshold_minutes
    - "stale" if last_heartbeat is older than staleness_threshold_minutes

    Args:
        session: Session object with status and lastHeartbeat fields
        staleness_threshold_minutes: Threshold in minutes for staleness detection

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    if "status" not in session or "lastHeartbeat" not in session:
        return False, "Missing required fields: status, lastHeartbeat"

    try:
        last_heartbeat = parse_datetime(session["lastHeartbeat"])
        now = datetime.datetime.now(datetime.timezone.utc)
        time_diff = (now - last_heartbeat).total_seconds() / 60  # Convert to minutes

        expected_status = "stale" if time_diff > staleness_threshold_minutes else "active"
        actual_status = session["status"]

        if actual_status != expected_status:
            return False, (
                f"Status mismatch: expected '{expected_status}' but got '{actual_status}' "
                f"(heartbeat was {time_diff:.1f} minutes ago)"
            )

        return True, ""

    except ValueError as e:
        return False, f"Failed to parse lastHeartbeat: {str(e)}"


def validate_heartbeat_response(response: Dict[str, Any]) -> tuple[bool, str]:
    """
    Validate heartbeatSession API response.

    Expected response format:
    {
        "success": true,
        "message": "Heartbeat received"
    }

    Args:
        response: The JSON response from heartbeatSession endpoint

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    # Heartbeat response can be empty or contain success field
    if not response:
        return True, ""

    if "success" in response and response["success"] is False:
        message = response.get("message", "Unknown error")
        return False, f"Heartbeat failed: {message}"

    return True, ""


def validate_deregister_response(response: Dict[str, Any]) -> tuple[bool, str]:
    """
    Validate deregisterSession API response.

    Expected response format:
    {
        "success": true,
        "message": "Session deregistered successfully"
    }

    Args:
        response: The JSON response from deregisterSession endpoint

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    # Deregister response can be empty or contain success field
    if not response:
        return True, ""

    if "success" in response and response["success"] is False:
        message = response.get("message", "Unknown error")
        return False, f"Deregister failed: {message}"

    return True, ""


def parse_datetime(dt_str: str) -> datetime.datetime:
    """
    Parse an ISO 8601 datetime string to datetime object.

    Handles both UTC formats:
    - "2023-01-01T12:00:00Z" (Z suffix)
    - "2023-01-01T12:00:00+00:00" (timezone offset)

    Args:
        dt_str: ISO 8601 datetime string

    Returns:
        datetime.datetime: Parsed datetime with UTC timezone

    Raises:
        ValueError: If datetime string is invalid
    """
    if not dt_str:
        raise ValueError("Empty datetime string")

    # Handle 'Z' suffix for UTC
    if dt_str.endswith('Z'):
        dt_str = dt_str[:-1] + '+00:00'

    try:
        return datetime.datetime.fromisoformat(dt_str)
    except ValueError as e:
        raise ValueError(f"Invalid datetime format: {dt_str}") from e


def validate_error_response(response: Dict[str, Any], expected_status: int = None) -> tuple[bool, str]:
    """
    Validate an error response from the API.

    Expected error format:
    {
        "error": "Error message",
        "statusCode": 400
    }

    Args:
        response: The JSON response
        expected_status: Optional expected status code

    Returns:
        tuple: (is_valid: bool, error_message: str)
    """
    if "error" not in response:
        return False, "Error response missing 'error' field"

    if expected_status is not None:
        if "statusCode" not in response:
            return False, "Error response missing 'statusCode' field"

        if response["statusCode"] != expected_status:
            return False, (
                f"Expected status {expected_status}, got {response['statusCode']}"
            )

    return True, ""


# Convenience function for pretty printing validation results
def print_validation_result(is_valid: bool, error_message: str, context: str = ""):
    """
    Print validation result with color coding.

    Args:
        is_valid: Whether validation passed
        error_message: Error message if validation failed
        context: Optional context string (e.g., "registerSession response")
    """
    prefix = f"[{context}] " if context else ""

    if is_valid:
        print(f"✅ {prefix}Validation passed")
    else:
        print(f"❌ {prefix}Validation failed: {error_message}")
