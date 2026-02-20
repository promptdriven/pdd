#!/bin/bash
# Setup script for the video editor pipeline.
#
# Usage:
#   cd pipeline && bash setup.sh
#
# Prerequisites:
#   - Python 3.11+
#   - ffmpeg (brew install ffmpeg)
#   - Claude Code CLI (npm install -g @anthropic-ai/claude-code)

set -e

echo "=== Video Editor Pipeline Setup ==="

# Check Python version
python3 -c "import sys; assert sys.version_info >= (3, 11), 'Python 3.11+ required'" 2>/dev/null || {
    echo "Error: Python 3.11+ required"
    exit 1
}

# Check ffmpeg
command -v ffmpeg >/dev/null 2>&1 || {
    echo "Warning: ffmpeg not found. Install: brew install ffmpeg"
}

# Check Claude CLI
command -v claude >/dev/null 2>&1 || {
    echo "Warning: Claude CLI not found. Install: npm install -g @anthropic-ai/claude-code"
}

# Create virtual environment
if [ ! -d "venv" ]; then
    echo "Creating virtual environment..."
    python3 -m venv venv
fi

echo "Installing dependencies..."
source venv/bin/activate
pip install -r requirements.txt

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Activate the environment:"
echo "  source pipeline/venv/bin/activate"
echo ""
echo "Set credentials for Veo/Imagen:"
echo "  export GOOGLE_APPLICATION_CREDENTIALS=/path/to/service-account.json"
echo "  # or: export GOOGLE_API_KEY=your-api-key"
