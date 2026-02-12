FROM python:3.12-slim

# System deps for building packages and git operations (regression tests use git)
RUN apt-get update && apt-get install -y --no-install-recommends \
    git \
    build-essential \
    curl \
    zsh \
    fish \
    tcsh \
    nodejs \
    && rm -rf /var/lib/apt/lists/*

# Install Claude Code CLI (standalone binary, no npm required)
# Installer puts binary at ~/.local/bin/claude
RUN curl -fsSL https://claude.ai/install.sh | bash \
    && ln -sf /root/.local/bin/claude /usr/local/bin/claude \
    && claude --version

# Git config needed by regression tests that do git init/commit
RUN git config --global user.email "ci@pdd.dev" && \
    git config --global user.name "PDD CI" && \
    git config --global init.defaultBranch main

# Install Python dependencies (rebuild image only when these change)
WORKDIR /app
COPY requirements.txt pyproject.toml ./
RUN pip install --no-cache-dir -r requirements.txt && \
    pip install --no-cache-dir pytest-xdist pytest-mock pytest-asyncio httpx build

# Entrypoint script
COPY ci/cloud-batch/entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
