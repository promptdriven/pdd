"""Conformance gates for PDD code generation.

Each gate judges a generated artifact before it reaches disk and raises a
typed error from :mod:`pdd.conformance.gate_errors` when it refuses the write.
Extracted from ``code_generator_main`` so callers can catch these types
without importing the generation pipeline.
"""
