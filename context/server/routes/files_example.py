import uvicorn
import shutil
import os
from pathlib import Path
from datetime import datetime
from typing import List, Optional, Literal
from fastapi import FastAPI, HTTPException, APIRouter
from pydantic import BaseModel
import base64
import hashlib

# ============================================================================
# 1. MOCK DEPENDENCIES
#    In a real app, these would be imported from `..models` and `..security`
# ============================================================================

# Mock Models (pdd.server.models)
class FileTreeNode(BaseModel):
    name: str
    path: str
    type: Literal["file", "directory"]
    children: Optional[List['FileTreeNode']] = None
    size: Optional[int] = None
    mtime: Optional[datetime] = None

class FileContent(BaseModel):
    path: str
    content: str
    encoding: str
    size: int
    is_binary: bool
    chunk_index: Optional[int] = None
    total_chunks: Optional[int] = None
    checksum: Optional[str] = None

class WriteFileRequest(BaseModel):
    path: str
    content: str
    encoding: Literal["utf-8", "base64"] = "utf-8"
    create_parents: bool = False

class WriteResult(BaseModel):
    success: bool
    path: str
    mtime: Optional[datetime] = None
    error: Optional[str] = None

class FileMetadata(BaseModel):
    path: str
    exists: bool
    size: Optional[int] = None
    mtime: Optional[datetime] = None
    is_directory: bool = False

# Mock Security (pdd.server.security)
class SecurityError(Exception):
    def __init__(self, message: str):
        self.message = message

class PathValidator:
    def __init__(self, project_root: Path):
        self.project_root = project_root.resolve()

    def validate(self, path: str) -> Path:
        """
        Simple validation logic for the example.
        In production, this prevents directory traversal attacks.
        """
        target = (self.project_root / path).resolve()
        try:
            target.relative_to(self.project_root)
        except ValueError:
            raise SecurityError("Path traversal detected")
        return target

# ============================================================================
# 2. ROUTER IMPLEMENTATION
# ============================================================================

# Create a temporary directory for our "project root"
TEMP_ROOT = Path("./temp_project_root")
if TEMP_ROOT.exists():
    shutil.rmtree(TEMP_ROOT)
TEMP_ROOT.mkdir()

# Create some dummy files
(TEMP_ROOT / "hello.txt").write_text("Hello World!", encoding="utf-8")
(TEMP_ROOT / "src").mkdir()
(TEMP_ROOT / "src" / "main.py").write_text("print('main')", encoding="utf-8")

router = APIRouter(prefix="/api/v1/files", tags=["files"])
_path_validator_instance = PathValidator(TEMP_ROOT)

def get_path_validator_mock() -> PathValidator:
    return _path_validator_instance

# --- HELPER FUNCTIONS ---
def _is_binary_file(path: Path) -> bool:
    """Simplified check for binary files based on extension."""
    return path.suffix in {".png", ".jpg", ".pyc"}

def _build_file_tree(path: Path, root: Path, depth: int, current: int = 0) -> FileTreeNode:
    rel = path.relative_to(root)
    if path.is_dir():
        children = []
        if current < depth:
            for p in path.iterdir():
                children.append(_build_file_tree(p, root, depth, current + 1))
        return FileTreeNode(name=path.name, path=str(rel), type="directory", children=children)
    return FileTreeNode(name=path.name, path=str(rel), type="file", size=path.stat().st_size)

# --- ROUTES ---
@router.get("/tree", response_model=FileTreeNode)
async def get_tree(path: str = "", depth: int = 3):
    validator = get_path_validator_mock()
    try:
        abs_path = validator.validate(path)
    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)
    return _build_file_tree(abs_path, validator.project_root, depth)

@router.get("/content", response_model=FileContent)
async def get_content(path: str):
    validator = get_path_validator_mock()
    try:
        abs_path = validator.validate(path)
    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)
    
    if not abs_path.exists():
        raise HTTPException(404, "File not found")
        
    content = abs_path.read_text(encoding="utf-8")
    return FileContent(
        path=path, content=content, encoding="utf-8", 
        size=len(content), is_binary=False
    )

@router.post("/write", response_model=WriteResult)
async def write_file(req: WriteFileRequest):
    validator = get_path_validator_mock()
    try:
        abs_path = validator.validate(req.path)
    except SecurityError as e:
        raise HTTPException(status_code=403, detail=e.message)
    
    if req.create_parents:
        abs_path.parent.mkdir(parents=True, exist_ok=True)
        
    abs_path.write_text(req.content, encoding="utf-8")
    return WriteResult(success=True, path=req.path, mtime=datetime.now())

# ============================================================================
# 3. MAIN APP SETUP
# ============================================================================

def main():
    # 1. Create the FastAPI app
    app = FastAPI(title="File Server Example")

    # 2. Include the router
    app.include_router(router)

    print(f"Server root set to: {TEMP_ROOT.resolve()}")
    print("Created dummy files: hello.txt, src/main.py")
    
    # 3. Run the server
    print("\nRoutes available:")
    print("  GET  /api/v1/files/tree?path=&depth=2")
    print("  GET  /api/v1/files/content?path=hello.txt")
    print("  POST /api/v1/files/write")
    
    print("\nStarting server on http://127.0.0.1:8000...")
    try:
        uvicorn.run(app, host="127.0.0.1", port=8000)
    except KeyboardInterrupt:
        print("\nStopping server...")
    finally:
        # Cleanup
        if TEMP_ROOT.exists():
            shutil.rmtree(TEMP_ROOT)
            print("Cleaned up temp directory.")

if __name__ == "__main__":
    main()