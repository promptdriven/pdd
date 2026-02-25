#!/usr/bin/env bash
set -euo pipefail

# ============================================================================
# Video Editor PDD — Setup Script
# ============================================================================
# Validates prerequisites, installs dependencies, creates required directories,
# and initializes the SQLite database.
# ============================================================================

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

ok()   { echo -e "  ${GREEN}[ok]${NC} $1"; }
warn() { echo -e "  ${YELLOW}[warn]${NC} $1"; }
fail() { echo -e "  ${RED}[FAIL]${NC} $1"; exit 1; }

# ---- 1. Check prerequisites ----
echo ""
echo "=== Checking prerequisites ==="

# Node.js 20+
if command -v node &>/dev/null; then
  NODE_VERSION=$(node -v | sed 's/^v//')
  NODE_MAJOR=$(echo "$NODE_VERSION" | cut -d. -f1)
  if [ "$NODE_MAJOR" -ge 20 ]; then
    ok "Node.js $NODE_VERSION"
  else
    fail "Node.js 20+ required, found $NODE_VERSION"
  fi
else
  fail "Node.js not found. Install Node.js 20+ from https://nodejs.org"
fi

# Python 3.11+
if command -v python3 &>/dev/null; then
  PY_VERSION=$(python3 --version | sed 's/Python //')
  PY_MAJOR=$(echo "$PY_VERSION" | cut -d. -f1)
  PY_MINOR=$(echo "$PY_VERSION" | cut -d. -f2)
  if [ "$PY_MAJOR" -ge 3 ] && [ "$PY_MINOR" -ge 11 ]; then
    ok "Python $PY_VERSION"
  else
    fail "Python 3.11+ required, found $PY_VERSION"
  fi
else
  fail "Python 3 not found. Install Python 3.11+ from https://python.org"
fi

# ffmpeg
if command -v ffmpeg &>/dev/null; then
  FFMPEG_VERSION=$(ffmpeg -version 2>&1 | head -n1 | awk '{print $3}')
  ok "ffmpeg $FFMPEG_VERSION"
else
  fail "ffmpeg not found. Install via: brew install ffmpeg (macOS) or apt install ffmpeg (Linux)"
fi

# git
if command -v git &>/dev/null; then
  GIT_VERSION=$(git --version | sed 's/git version //')
  ok "git $GIT_VERSION"
else
  warn "git not found — git integration features will be disabled"
fi

# Claude CLI (optional)
if command -v claude &>/dev/null; then
  ok "Claude CLI found"
else
  warn "Claude CLI not found — annotation fixes require: npm install -g @anthropic-ai/claude-code"
fi

# ---- 2. Install Node.js dependencies ----
echo ""
echo "=== Installing Node.js dependencies ==="

echo "  Installing root project dependencies..."
npm install

if [ -d "remotion" ]; then
  echo "  Installing Remotion project dependencies..."
  (cd remotion && npm install)
  ok "Remotion dependencies installed"
else
  warn "remotion/ directory not found — skipping Remotion deps"
fi

ok "Node.js dependencies installed"

# ---- 3. Install Python dependencies ----
echo ""
echo "=== Installing Python dependencies ==="

if [ -f "requirements.txt" ]; then
  pip3 install -r requirements.txt 2>&1 | tail -n1
  ok "Python dependencies installed"
else
  warn "requirements.txt not found — skipping Python deps"
fi

# ---- 4. Create required directories ----
echo ""
echo "=== Creating directories ==="

for dir in outputs references audits data models; do
  mkdir -p "$dir"
done
ok "Created: outputs/ references/ audits/ data/ models/"

# ---- 5. Initialize SQLite database ----
echo ""
echo "=== Initializing database ==="

if command -v npx &>/dev/null; then
  npx tsx -e "require('./lib/db').getDb()" 2>/dev/null && ok "SQLite database initialized (pipeline.db)" || warn "Database init skipped (tsx not available or lib/db not built)"
else
  warn "npx not found — skipping database initialization"
fi

# ---- 6. Summary ----
echo ""
echo "=== Setup complete ==="
echo ""
echo "  Next steps:"
echo "    1. Copy .env.example to .env and fill in API keys"
echo "    2. Run 'npm run dev' to start the development server"
echo "    3. Download Qwen3-TTS model weights if using local TTS"
echo ""
