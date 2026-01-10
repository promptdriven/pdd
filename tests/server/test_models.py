import pytest
from datetime import datetime
from pydantic import ValidationError
import z3

# Import the actual models
from pdd.server.models import (
    FileMetadata,
    FileTreeNode,
    FileContent,
    WriteFileRequest,
    WriteResult,
    CommandRequest,
    JobHandle,
    JobStatus,
    JobResult,
    WSMessage,
    StdoutMessage,
    StderrMessage,
    ProgressMessage,
    InputRequestMessage,
    CompleteMessage,
    FileChangeMessage,
    ServerStatus,
    ServerConfig,
)

# ============================================================================
# Z3 Formal Verification Tests
# ============================================================================

def test_z3_path_validation_logic():
    """
    Formally verify the path validation logic using Z3.
    We model the constraint: A path is invalid if it contains "..".
    We generate a counter-example (a string with "..") and verify the model rejects it.
    """
    # Create a Z3 string variable
    path = z3.String('path')
    
    # Define the unsafe condition: path contains ".."
    unsafe_condition = z3.Contains(path, z3.StringVal(".."))
    
    # Create a solver
    solver = z3.Solver()
    solver.add(unsafe_condition)
    
    # Add a constraint to make the string non-empty and reasonable length for a test
    solver.add(z3.Length(path) > 2)
    solver.add(z3.Length(path) < 20)
    
    # Check if we can generate such a string
    if solver.check() == z3.sat:
        model = solver.model()
        # Get the concrete string value from Z3
        generated_unsafe_path = model[path].as_string()
        
        # Now verify that our Pydantic model actually rejects this Z3-generated unsafe path
        # We test both FileMetadata and WriteFileRequest as they both use the validator
        
        # 1. Test FileMetadata
        with pytest.raises(ValidationError) as excinfo:
            FileMetadata(path=generated_unsafe_path, exists=True)
        assert "Path traversal ('..') is not allowed" in str(excinfo.value)
        
        # 2. Test WriteFileRequest
        with pytest.raises(ValidationError) as excinfo:
            WriteFileRequest(path=generated_unsafe_path, content="test")
        assert "Path traversal ('..') is not allowed" in str(excinfo.value)
    else:
        pytest.fail("Z3 failed to generate an unsafe path containing '..'")

# ============================================================================
# File Models Unit Tests
# ============================================================================

def test_file_metadata_valid():
    """Test valid creation of FileMetadata."""
    meta = FileMetadata(
        path="src/main.py",
        exists=True,
        size=1024,
        mtime=datetime.now(),
        is_directory=False
    )
    assert meta.path == "src/main.py"
    assert meta.exists is True
    assert meta.size == 1024
    assert isinstance(meta.mtime, datetime)

def test_file_metadata_defaults():
    """Test default values for FileMetadata."""
    meta = FileMetadata(path="README.md", exists=False)
    assert meta.size is None
    assert meta.mtime is None
    assert meta.is_directory is False

def test_file_metadata_path_traversal():
    """Test that FileMetadata rejects paths with '..'."""
    invalid_paths = ["../secret", "folder/../file", ".."]
    for p in invalid_paths:
        with pytest.raises(ValidationError) as exc:
            FileMetadata(path=p, exists=True)
        assert "Path traversal" in str(exc.value)

def test_file_tree_node_recursive():
    """Test recursive structure of FileTreeNode."""
    child = FileTreeNode(
        name="child.py",
        path="src/child.py",
        type="file",
        size=100
    )
    parent = FileTreeNode(
        name="src",
        path="src",
        type="directory",
        children=[child]
    )
    
    assert parent.children is not None
    assert len(parent.children) == 1
    assert parent.children[0].name == "child.py"
    assert parent.children[0].type == "file"

def test_file_content_encoding_literal():
    """Test FileContent encoding constraints."""
    # Valid encodings
    fc_utf8 = FileContent(path="a", content="b", size=1, encoding="utf-8")
    assert fc_utf8.encoding == "utf-8"
    
    fc_base64 = FileContent(path="a", content="b", size=1, encoding="base64")
    assert fc_base64.encoding == "base64"
    
    # Invalid encoding
    with pytest.raises(ValidationError):
        FileContent(path="a", content="b", size=1, encoding="latin-1")

def test_write_file_request_defaults():
    """Test WriteFileRequest defaults."""
    req = WriteFileRequest(path="new.txt", content="hello")
    assert req.encoding == "utf-8"
    assert req.create_parents is True

def test_write_file_request_path_validation():
    """Test WriteFileRequest path validation."""
    with pytest.raises(ValidationError) as exc:
        WriteFileRequest(path="../bad.txt", content="x")
    assert "Path traversal" in str(exc.value)

def test_write_result():
    """Test WriteResult model."""
    res = WriteResult(success=True, path="a.txt", mtime=datetime.now())
    assert res.success is True
    assert res.error is None
    
    res_fail = WriteResult(success=False, path="a.txt", error="Permission denied")
    assert res_fail.success is False
    assert res_fail.error == "Permission denied"

# ============================================================================
# Command & Job Models Unit Tests
# ============================================================================

def test_command_request_defaults():
    """Test CommandRequest default factories."""
    cmd = CommandRequest(command="ls")
    assert cmd.args == {}
    assert cmd.options == {}
    
    cmd_full = CommandRequest(command="ls", args={"path": "."}, options={"l": True})
    assert cmd_full.args["path"] == "."
    assert cmd_full.options["l"] is True

def test_job_status_enum():
    """Test JobStatus enum values."""
    assert JobStatus.QUEUED == "queued"
    assert JobStatus.RUNNING == "running"
    assert JobStatus.COMPLETED == "completed"
    assert JobStatus.FAILED == "failed"
    assert JobStatus.CANCELLED == "cancelled"

def test_job_handle_creation():
    """Test JobHandle creation and defaults."""
    handle = JobHandle(job_id="job-123")
    assert handle.job_id == "job-123"
    assert handle.status == JobStatus.QUEUED
    assert isinstance(handle.created_at, datetime)

def test_job_result_model():
    """Test JobResult model."""
    res = JobResult(
        job_id="job-123",
        status=JobStatus.COMPLETED,
        result={"output": "ok"},
        cost=0.05,
        duration_seconds=1.2
    )
    assert res.status == "completed"
    assert res.result["output"] == "ok"
    assert res.cost == 0.05

# ============================================================================
# WebSocket Message Models Unit Tests
# ============================================================================

def test_ws_message_subclasses_types():
    """Test that WSMessage subclasses have correct fixed types."""
    
    # Stdout
    msg = StdoutMessage(data="hello")
    assert msg.type == "stdout"
    assert msg.data == "hello"
    
    # Stderr
    msg = StderrMessage(data="error")
    assert msg.type == "stderr"
    
    # Progress
    msg = ProgressMessage(current=50, total=100)
    assert msg.type == "progress"
    assert msg.current == 50
    
    # Input Request
    msg = InputRequestMessage(prompt="Password:")
    assert msg.type == "input_request"
    assert msg.password is False  # Default
    
    # Complete
    msg = CompleteMessage(success=True)
    assert msg.type == "complete"
    assert msg.success is True
    
    # File Change
    msg = FileChangeMessage(path="test.py", event="modified")
    assert msg.type == "file_change"
    assert msg.event == "modified"

def test_file_change_message_event_literal():
    """Test FileChangeMessage event literal validation."""
    with pytest.raises(ValidationError):
        FileChangeMessage(path="x", event="renamed")  # Invalid event

# ============================================================================
# Server Configuration Models Unit Tests
# ============================================================================

def test_server_status():
    """Test ServerStatus model."""
    status = ServerStatus(
        version="1.0.0",
        project_root="/app",
        uptime_seconds=3600.5
    )
    assert status.version == "1.0.0"
    assert status.active_jobs == 0  # Default

def test_server_config_defaults():
    """Test ServerConfig defaults."""
    config = ServerConfig()
    assert config.host == "127.0.0.1"
    assert config.port == 9876
    assert config.token is None
    assert config.allow_remote is False

def test_server_config_custom():
    """Test ServerConfig with custom values."""
    config = ServerConfig(host="0.0.0.0", port=8000, token="abc", allow_remote=True)
    assert config.host == "0.0.0.0"
    assert config.port == 8000
    assert config.token == "abc"
    assert config.allow_remote is True