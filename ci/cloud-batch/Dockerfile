FROM python:3.12-slim

# System deps for building packages and git operations (regression tests use git)
RUN apt-get update && apt-get install -y --no-install-recommends \
    git \
    gh \
    build-essential \
    curl \
    zsh \
    fish \
    tcsh \
    nodejs \
    npm \
    bubblewrap \
    sudo \
    util-linux \
    && rm -rf /var/lib/apt/lists/*

# Protected pytest shards must enter the sandbox as non-root so RLIMIT_NPROC
# remains kernel-enforced. Trusted bind staging still requires passwordless
# sudo before setpriv drops back to this user inside the namespace.
RUN useradd --create-home --uid 1000 --shell /bin/bash pdd && \
    printf '%s\n' 'pdd ALL=(ALL) NOPASSWD: ALL' > /etc/sudoers.d/pdd && \
    chmod 0440 /etc/sudoers.d/pdd

# Install Gemini CLI and Codex CLI for agentic fix tests
RUN npm install -g @google/gemini-cli @openai/codex

# Install Claude Code CLI (standalone binary, no npm required)
# Installer puts binary at ~/.local/bin/claude
RUN curl -fsSL https://claude.ai/install.sh | bash \
    && ln -sf /root/.local/bin/claude /usr/local/bin/claude \
    && claude --version

# Git config needed by regression tests that do git init/commit
RUN git config --system user.email "ci@pdd.dev" && \
    git config --system user.name "PDD CI" && \
    git config --system init.defaultBranch main

# Install Python dependencies (rebuild image only when these change)
WORKDIR /app
COPY requirements.txt pyproject.toml ./
RUN pip install --no-cache-dir -r requirements.txt && \
    pip install --no-cache-dir pytest-xdist pytest-mock pytest-asyncio pytest-timeout httpx build

# Entrypoint script
COPY ci/cloud-batch/entrypoint.sh /entrypoint.sh
COPY ci/cloud-batch/runtime-secrets.py /runtime-secrets.py
COPY ci/cloud-batch/firebase-token-exchange.py /firebase-token-exchange.py
COPY ci/cloud-batch/source-identity.py /source-identity.py
RUN chmod +x /entrypoint.sh /runtime-secrets.py /firebase-token-exchange.py /source-identity.py

ENTRYPOINT ["/runtime-secrets.py"]
