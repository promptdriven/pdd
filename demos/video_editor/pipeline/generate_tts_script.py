#!/usr/bin/env python3
"""Generate TTS script from the main narrative script using Claude.

Takes the narrative/main_script.md and produces narrative/tts_script.md
with tone/pace/emotion annotations for the TTS engine.

Usage:
    python generate_tts_script.py
    python generate_tts_script.py --script path/to/script.md
"""

import argparse
import subprocess
import sys
from pathlib import Path

from utils import (
    NARRATIVE_DIR, emit_progress, emit_error, emit_done,
)

TTS_SCRIPT_PROMPT = """Convert this video script into a TTS-annotated script.

For each speech line, add annotations:
- [TONE: description] - the vocal quality (e.g., "casual, observational", "emphatic, memorable")
- [PACE: description] - speaking speed (e.g., "moderate", "slightly slower", "deliberate")
- [EMOTION: description] - emotional quality (e.g., "genuine curiosity", "quiet conviction")
- [PAUSE: Ns] - silence pauses between segments (e.g., [PAUSE: 1.5s])

Group lines by video section using ## headers.
Keep the actual speech text clean and natural.
Output as markdown.

SCRIPT:
{script_content}
"""


def main():
    parser = argparse.ArgumentParser(description="Generate TTS script from narrative")
    parser.add_argument("--script", help="Path to main script (default: narrative/main_script.md)")
    args = parser.parse_args()

    script_path = Path(args.script) if args.script else NARRATIVE_DIR / "main_script.md"
    output_path = NARRATIVE_DIR / "tts_script.md"

    if not script_path.exists():
        emit_error("tts-script", f"Main script not found: {script_path}")
        sys.exit(1)

    emit_progress("tts-script", 10, "Reading main script...")
    script_content = script_path.read_text()

    prompt = TTS_SCRIPT_PROMPT.format(script_content=script_content)

    emit_progress("tts-script", 20, "Generating TTS script with Claude...")

    try:
        result = subprocess.run(
            ["claude", "--print", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=180,
        )

        if result.returncode != 0:
            emit_error("tts-script", f"Claude failed: {result.stderr[:200]}")
            sys.exit(1)

        output = result.stdout.strip()
        if not output:
            emit_error("tts-script", "Claude returned empty output")
            sys.exit(1)

        NARRATIVE_DIR.mkdir(parents=True, exist_ok=True)
        output_path.write_text(output)

        emit_done("tts-script", f"Generated TTS script: {output_path.name}")

    except subprocess.TimeoutExpired:
        emit_error("tts-script", "Claude timed out (3 min)")
        sys.exit(1)
    except FileNotFoundError:
        emit_error("tts-script", "Claude CLI not found. Install: npm install -g @anthropic-ai/claude-code")
        sys.exit(1)


if __name__ == "__main__":
    main()
