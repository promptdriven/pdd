#!/usr/bin/env python3
"""
Example: How to use the render_tts batch TTS synthesis script.

This example demonstrates:
  1. Creating a properly formatted tts_script.md input file
  2. Parsing NARRATOR: blocks into Segment objects
  3. Using the audio utility functions (silence generation, WAV writing)
  4. Running the full CLI pipeline
  5. Consuming the JSON progress output programmatically

Directory structure (relative to project root):
    project_root/
    ├── narrative/
    │   └── tts_script.md          # Input script with NARRATOR: blocks
    ├── outputs/
    │   └── tts/                   # Generated WAV files land here
    └── scripts/
        └── render_tts.py          # The module being demonstrated
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

# ---------------------------------------------------------------------------
# Adjust sys.path so we can import from the scripts directory.
# This assumes the example lives alongside or near the scripts/ folder.
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)
# render_tts.py lives in the sibling "scripts/" directory relative to project root
sys.path.insert(0, os.path.join(PROJECT_ROOT, "scripts"))

try:
    # Import key components from render_tts
    from render_tts import (
        Segment,
        parse_tts_script,
        generate_silence_wav_bytes,
        write_wav,
        concatenate_pcm,
        SAMPLE_RATE,
    )
except ImportError:
    # Fallback or mock for demonstration if the module isn't actually present
    print("Warning: render_tts module not found. Some examples may fail.")


# ===================================================================
# Example 1: Create a sample tts_script.md and parse it
# ===================================================================
def example_parse_script():
    """
    Demonstrates how to create a TTS script file and parse it into
    Segment objects.
    """
    print("=" * 60)
    print("Example 1: Parsing a TTS script")
    print("=" * 60)

    # Create a temporary project directory with the expected structure
    with tempfile.TemporaryDirectory() as tmpdir:
        narrative_dir = os.path.join(tmpdir, "narrative")
        os.makedirs(narrative_dir)

        script_content = """\
# Episode 1 — The Discovery

NARRATOR: [TONE: dramatic] [PACE: slow] The old lighthouse stood alone
on the cliff, its beam cutting through the fog like a blade of light.
[PAUSE: 1.5s] No one had visited it in years.

NARRATOR: [EMOTION: excitement] But tonight was different. Tonight,
the door was open. [PAUSE: 0.8s] And from within, a faint melody
drifted out into the cold night air.

NARRATOR: [TONE: somber] [PACE: moderate] She stepped inside,
her footsteps echoing against the stone walls. The melody grew louder.
"""

        script_path = os.path.join(narrative_dir, "tts_script.md")
        with open(script_path, "w", encoding="utf-8") as f:
            f.write(script_content)

        # Parse the script
        segments = parse_tts_script(script_path)

        print(f"\nFound {len(segments)} NARRATOR segments:\n")

        for seg in segments:
            print(f"  Segment ID : {seg.segment_id}")
            print(f"  Annotations: {seg.annotations}")
            print(f"  Clean text : {seg.clean_text[:80]}...")
            print(f"  Chunks     : {len(seg.text_chunks)} "
                  f"(text + pause blocks)")
            for i, chunk in enumerate(seg.text_chunks):
                if chunk["type"] == "pause":
                    print(f"    chunk[{i}]: PAUSE {chunk['duration']}s")
                else:
                    preview = chunk["content"][:50]
                    print(f"    chunk[{i}]: TEXT \"{preview}...\"")
            print()

    return segments


# ===================================================================
# Example 2: Working with audio utilities (no model required)
# ===================================================================
def example_audio_utilities():
    """
    Demonstrates the audio helper functions that do NOT require the
    TTS model to be loaded.
    """
    print("=" * 60)
    print("Example 2: Audio utility functions")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        # Generate 2 seconds of silence
        silence_2s = generate_silence_wav_bytes(2.0, SAMPLE_RATE)
        print(f"\n  2s silence: {len(silence_2s)} bytes "
              f"({len(silence_2s) // 2} samples at {SAMPLE_RATE}Hz)")

        # Generate a short silence gap
        gap = generate_silence_wav_bytes(0.5)
        print(f"  0.5s gap:   {len(gap)} bytes")

        # Concatenate multiple chunks (simulating text audio + pause + text audio)
        fake_audio_chunk_1 = generate_silence_wav_bytes(1.0)  # placeholder
        fake_audio_chunk_2 = generate_silence_wav_bytes(1.5)  # placeholder
        combined = concatenate_pcm([fake_audio_chunk_1, gap, fake_audio_chunk_2])
        print(f"  Combined:   {len(combined)} bytes "
              f"(1.0s + 0.5s + 1.5s = 3.0s expected)")

        # Write to WAV file
        wav_path = os.path.join(tmpdir, "test_output.wav")
        duration = write_wav(wav_path, combined)
        file_size = os.path.getsize(wav_path)
        print(f"\n  Written WAV: {wav_path}")
        print(f"  Duration:    {duration:.2f}s")
        print(f"  File size:   {file_size} bytes")
        print()


# ===================================================================
# Example 3: Working with Segment objects directly
# ===================================================================
def example_segment_object():
    """
    Demonstrates creating and inspecting a Segment object manually.
    """
    print("=" * 60)
    print("Example 3: Segment object construction")
    print("=" * 60)

    raw = (
        "[TONE: mysterious] [EMOTION: curiosity] "
        "The map revealed a hidden path. "
        "[PAUSE: 2s] "
        "She traced her finger along the faded ink. "
        "[PAUSE: 0.5s] "
        "And then she saw it — the X that marked the spot."
    )

    seg = Segment("seg_042", raw)

    print(f"\n  segment_id:  {seg.segment_id}")
    print(f"  annotations: {seg.annotations}")
    print(f"  clean_text:  {seg.clean_text}")
    print(f"  text_chunks ({len(seg.text_chunks)}):")
    for i, chunk in enumerate(seg.text_chunks):
        print(f"    [{i}] {chunk}")
    print()


# ===================================================================
# Example 4: Running the full CLI as a subprocess
# ===================================================================
def example_cli_subprocess():
    """
    Demonstrates how to invoke render_tts.py as a subprocess and consume its JSON progress output.
    """
    print("=" * 60)
    print("Example 4: CLI subprocess invocation")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        # Set up project structure
        narrative_dir = os.path.join(tmpdir, "narrative")
        output_dir = os.path.join(tmpdir, "outputs", "tts")
        os.makedirs(narrative_dir)

        script_content = """\
NARRATOR: [TONE: warm] Welcome to the story. This is segment one.

NARRATOR: [PAUSE: 1s] This is segment two, with a pause at the start.

NARRATOR: [EMOTION: joy] And this is the final segment. The end!
"""
        with open(os.path.join(narrative_dir, "tts_script.md"), "w") as f:
            f.write(script_content)

        # Find the render_tts.py script
        candidates = [
            os.path.join(PROJECT_ROOT, "scripts", "render_tts.py"),
            os.path.join(SCRIPT_DIR, "render_tts.py"),
        ]
        script_file = None
        for c in candidates:
            if os.path.exists(c):
                script_file = c
                break

        if script_file is None:
            print("\n  [SKIPPED] render_tts.py not found on disk.")
            return

        # Build the command — render only segments 1 and 3
        cmd = [
            sys.executable,
            script_file,
            "--project-dir", tmpdir,
            "--output-dir", output_dir,
            "--segments", "seg_001,seg_003",
        ]

        print(f"\n  Command: {' '.join(cmd)}\n")

        # Run and capture output line by line
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

        # Stream stdout lines (each is a JSON progress event)
        if process.stdout:
            for line in process.stdout:
                line = line.strip()
                if line:
                    try:
                        event = json.loads(line)
                        print(f"  SSE event: {json.dumps(event, indent=2)}")
                    except json.JSONDecodeError:
                        print(f"  [raw] {line}")

        process.wait()
        print(f"\n  Exit code: {process.returncode}")

        # Show any stderr
        if process.stderr:
            stderr_output = process.stderr.read().strip()
            if stderr_output:
                print(f"  Stderr: {stderr_output[:200]}")
        print()


# ===================================================================
# Example 5: Programmatic rendering (without CLI)
# ===================================================================
def example_programmatic_rendering():
    """
    Shows how to use the module's components programmatically.
    """
    print("=" * 60)
    print("Example 5: Programmatic rendering pipeline (no model)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmpdir:
        # Create input
        narrative_dir = os.path.join(tmpdir, "narrative")
        output_dir = os.path.join(tmpdir, "outputs", "tts")
        os.makedirs(narrative_dir)
        os.makedirs(output_dir)

        script_content = """\
NARRATOR: [TONE: epic] In the beginning, there was silence.
[PAUSE: 2s] And then, the universe spoke.

NARRATOR: [PACE: fast] [EMOTION: urgency] Run! The walls are closing in!
"""
        script_path = os.path.join(narrative_dir, "tts_script.md")
        with open(script_path, "w") as f:
            f.write(script_content)

        # Step 1: Parse
        segments = parse_tts_script(script_path)
        print(f"\n  Parsed {len(segments)} segments")

        # Step 2-5: Render each segment (using silence as placeholder)
        for seg in segments:
            audio_chunks = []

            for chunk in seg.text_chunks:
                if chunk["type"] == "pause":
                    audio_chunks.append(
                        generate_silence_wav_bytes(chunk["duration"])
                    )
                    print(f"    [{seg.segment_id}] pause: {chunk['duration']}s")
                elif chunk["type"] == "text":
                    # Placeholder for engine.synthesize
                    pcm = generate_silence_wav_bytes(1.0)
                    audio_chunks.append(pcm)
                    print(f"    [{seg.segment_id}] text: "
                          f"\"{chunk['content'][:40]}...\"")

            combined = concatenate_pcm(audio_chunks)
            wav_path = os.path.join(output_dir, f"{seg.segment_id}.wav")
            duration = write_wav(wav_path, combined)

            # Emit the same JSON format the CLI would produce
            result = {
                "segmentId": seg.segment_id,
                "status": "done",
                "duration": round(duration, 2),
            }
            print(f"    -> {json.dumps(result)}")

        # List generated files
        print(f"\n  Generated files in {output_dir}:")
        for fname in sorted(os.listdir(output_dir)):
            fpath = os.path.join(output_dir, fname)
            print(f"    {fname} ({os.path.getsize(fpath)} bytes)")
        print()


# ===================================================================
# Main
# ===================================================================
if __name__ == "__main__":
    print("\nrender_tts.py — Usage Examples\n")

    try:
        example_parse_script()
        example_segment_object()
        example_audio_utilities()
        example_programmatic_rendering()
        example_cli_subprocess()
    except NameError as e:
        print(f"Error: {e}. Ensure render_tts.py is available for import.")

    print("All examples complete.")