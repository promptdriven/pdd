"""Distractor definition, generation, and manifest building (design.md §5)."""

from .definition import CandidateFile, DefinitionChecker, Violation
from .generator import GenerationConfig, generate_manifest
from .manifest import ManifestWriter, load_manifest, verify_lockfile, write_lockfile
from .vocabulary import harvest_vocabulary

__all__ = [
    "CandidateFile",
    "DefinitionChecker",
    "Violation",
    "GenerationConfig",
    "generate_manifest",
    "ManifestWriter",
    "load_manifest",
    "verify_lockfile",
    "write_lockfile",
    "harvest_vocabulary",
]
