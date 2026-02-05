#!/bin/bash
#
# PDD Developer Setup Script
#
# This script sets up a development environment for contributing to PDD.
# It handles:
#   1. Optional worktree creation from main branch
#   2. Conda environment creation with Python 3.12
#   3. Symbolic links for prompts/ and data/
#   4. .env file with PDD_PATH
#   5. Conda environment variable for PDD_PATH
#   6. Development dependencies installation
#
# Usage:
#   ./scripts/dev-setup.sh [options]
#
# Options:
#   --worktree <name>    Create a git worktree with this name
#   --env-name <name>    Name for the conda environment (default: worktree name or "pdd")
#   --python <version>   Python version (default: 3.12)
#   --no-worktree        Skip worktree creation prompts
#   --help               Show this help message
#

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default values
PYTHON_VERSION="3.12"
WORKTREE_NAME=""
ENV_NAME=""
NO_WORKTREE=false
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# PROJECT_ROOT is the main git repository root (where worktrees will be created)
# This works even when run from within a worktree
PROJECT_ROOT=""

# REPO_ROOT is the working directory for setup (may be a worktree)
REPO_ROOT=""

# Print functions
info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

success() {
    echo -e "${GREEN}[OK]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
    exit 1
}

show_help() {
    cat << EOF
PDD Developer Setup Script

Usage: $(basename "$0") [options]

Options:
  --worktree <name>    Create a git worktree with this name
  --env-name <name>    Name for the conda environment (default: worktree name or "pdd")
  --python <version>   Python version (default: 3.12)
  --no-worktree        Skip worktree creation, set up current directory
  --help               Show this help message

Examples:
  # Interactive setup in current directory
  $(basename "$0")

  # Create worktree and set up
  $(basename "$0") --worktree fix-issue-123

  # Set up current directory with custom env name
  $(basename "$0") --no-worktree --env-name my-pdd-dev

EOF
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --worktree)
            WORKTREE_NAME="$2"
            shift 2
            ;;
        --env-name)
            ENV_NAME="$2"
            shift 2
            ;;
        --python)
            PYTHON_VERSION="$2"
            shift 2
            ;;
        --no-worktree)
            NO_WORKTREE=true
            shift
            ;;
        --help)
            show_help
            exit 0
            ;;
        *)
            error "Unknown option: $1. Use --help for usage."
            ;;
    esac
done

# Check prerequisites
check_prerequisites() {
    info "Checking prerequisites..."

    # Check for git
    if ! command -v git &> /dev/null; then
        error "git is not installed. Please install git first."
    fi

    # Check for conda
    if ! command -v conda &> /dev/null; then
        error "conda is not installed. Please install Miniconda or Anaconda first."
    fi

    # Check we're in a git repo
    if ! git rev-parse --git-dir &> /dev/null; then
        error "Not in a git repository. Please run from within the PDD repo."
    fi

    # Determine PROJECT_ROOT (main repository root, works from worktrees too)
    # git-common-dir points to the shared .git directory across all worktrees
    local git_common_dir
    git_common_dir="$(git rev-parse --git-common-dir)"
    PROJECT_ROOT="$(cd "$git_common_dir/.." && pwd)"
    info "Project root: $PROJECT_ROOT"

    # Default REPO_ROOT to current git toplevel (may change if we create a worktree)
    REPO_ROOT="$(git rev-parse --show-toplevel)"

    success "Prerequisites check passed"
}

# Prompt for worktree creation
prompt_worktree() {
    if [[ "$NO_WORKTREE" == "true" ]]; then
        return
    fi

    if [[ -n "$WORKTREE_NAME" ]]; then
        return
    fi

    echo ""
    echo -e "${BLUE}Would you like to create a git worktree?${NC}"
    echo "Worktrees allow you to work on multiple branches simultaneously."
    echo ""
    read -p "Create worktree? [y/N]: " response

    if [[ "$response" =~ ^[Yy]$ ]]; then
        read -p "Enter worktree name (e.g., fix-issue-123): " WORKTREE_NAME
        if [[ -z "$WORKTREE_NAME" ]]; then
            warn "No worktree name provided, skipping worktree creation"
        fi
    fi
}

# Create git worktree
create_worktree() {
    if [[ -z "$WORKTREE_NAME" ]]; then
        return
    fi

    info "Creating git worktree '$WORKTREE_NAME'..."

    # Worktrees are always created under the main project root
    WORKTREES_DIR="$PROJECT_ROOT/.pdd/worktrees"
    WORKTREE_PATH="$WORKTREES_DIR/$WORKTREE_NAME"

    info "Worktrees directory: $WORKTREES_DIR"

    # Check if worktree already exists
    if [[ -d "$WORKTREE_PATH" ]]; then
        warn "Worktree already exists at $WORKTREE_PATH"
        read -p "Use existing worktree? [Y/n]: " response
        if [[ "$response" =~ ^[Nn]$ ]]; then
            error "Worktree already exists. Choose a different name."
        fi
    else
        # Create worktrees directory if needed
        mkdir -p "$WORKTREES_DIR"

        # Fetch latest main (run from project root to ensure we're in the right context)
        info "Fetching latest from origin..."
        git -C "$PROJECT_ROOT" fetch origin main

        # Create worktree from main
        git -C "$PROJECT_ROOT" worktree add -b "$WORKTREE_NAME" "$WORKTREE_PATH" origin/main
        success "Created worktree at $WORKTREE_PATH"
    fi

    # Change to worktree directory
    cd "$WORKTREE_PATH"
    REPO_ROOT="$WORKTREE_PATH"

    success "Now working in worktree: $WORKTREE_PATH"
}

# Determine conda environment name
determine_env_name() {
    if [[ -n "$ENV_NAME" ]]; then
        return
    fi

    # If we created a worktree, use its name
    if [[ -n "$WORKTREE_NAME" ]]; then
        ENV_NAME="$WORKTREE_NAME"
        info "Using worktree name for conda environment: $ENV_NAME"
        return
    fi

    # Check if we're under a worktrees directory
    PARENT_DIR=$(basename "$(dirname "$REPO_ROOT")")
    CURRENT_DIR=$(basename "$REPO_ROOT")

    if [[ "$PARENT_DIR" == "worktrees" ]]; then
        ENV_NAME="$CURRENT_DIR"
        info "Detected worktree directory, using name: $ENV_NAME"
        return
    fi

    # Default to "pdd"
    ENV_NAME="pdd"
    info "Using default conda environment name: $ENV_NAME"
}

# Create conda environment
create_conda_env() {
    info "Setting up conda environment '$ENV_NAME' with Python $PYTHON_VERSION..."

    # Check if environment already exists
    if conda env list | grep -q "^$ENV_NAME "; then
        warn "Conda environment '$ENV_NAME' already exists"
        read -p "Recreate environment? [y/N]: " response
        if [[ "$response" =~ ^[Yy]$ ]]; then
            info "Removing existing environment..."
            conda env remove -n "$ENV_NAME" -y
        else
            info "Using existing environment"
            return
        fi
    fi

    # Create the environment
    conda create -n "$ENV_NAME" python="$PYTHON_VERSION" -y
    success "Created conda environment '$ENV_NAME'"
}

# Create symbolic links
create_symlinks() {
    info "Creating symbolic links for prompts/ and data/..."

    cd "$REPO_ROOT"

    # Create prompts symlink in pdd/
    if [[ -L "pdd/prompts" ]]; then
        info "Symlink pdd/prompts already exists"
    elif [[ -e "pdd/prompts" ]]; then
        warn "pdd/prompts exists but is not a symlink"
    else
        if [[ -d "prompts" ]]; then
            ln -s ../prompts pdd/prompts
            success "Created symlink: pdd/prompts -> ../prompts"
        else
            warn "prompts/ directory not found, skipping symlink"
        fi
    fi

    # Create data symlink in pdd/
    if [[ -L "pdd/data" ]]; then
        info "Symlink pdd/data already exists"
    elif [[ -e "pdd/data" ]]; then
        warn "pdd/data exists but is not a symlink"
    else
        if [[ -d "data" ]]; then
            ln -s ../data pdd/data
            success "Created symlink: pdd/data -> ../data"
        else
            warn "data/ directory not found, skipping symlink"
        fi
    fi
}

# Create .env file
create_env_file() {
    info "Setting up .env file..."

    cd "$REPO_ROOT"
    PDD_PATH="$REPO_ROOT/pdd"

    # Check if .env exists
    if [[ -f ".env" ]]; then
        # Check if PDD_PATH is already set
        if grep -q "^PDD_PATH=" ".env"; then
            info "PDD_PATH already set in .env"
        else
            # Append PDD_PATH
            echo "" >> .env
            echo "# PDD source directory path" >> .env
            echo "PDD_PATH=$PDD_PATH" >> .env
            success "Added PDD_PATH to existing .env"
        fi
    else
        # Create new .env
        cat > .env << EOF
# PDD Environment Configuration
# This file is auto-generated by dev-setup.sh

# PDD source directory path
PDD_PATH=$PDD_PATH

# Add your API keys below:
# OPENAI_API_KEY=sk-your-key-here
# ANTHROPIC_API_KEY=sk-ant-your-key-here
# GOOGLE_API_KEY=your-google-api-key
EOF
        success "Created .env file with PDD_PATH"
    fi

    # Add .env to .gitignore if not already there
    if [[ -f ".gitignore" ]]; then
        if ! grep -q "^\.env$" ".gitignore"; then
            echo "" >> .gitignore
            echo "# Local environment file" >> .gitignore
            echo ".env" >> .gitignore
            success "Added .env to .gitignore"
        else
            info ".env already in .gitignore"
        fi
    else
        echo ".env" > .gitignore
        success "Created .gitignore with .env"
    fi
}

# Set PDD_PATH in conda environment
set_conda_env_var() {
    info "Setting PDD_PATH in conda environment '$ENV_NAME'..."

    PDD_PATH="$REPO_ROOT/pdd"

    # Use conda to set the environment variable
    conda env config vars set PDD_PATH="$PDD_PATH" -n "$ENV_NAME"

    success "Set PDD_PATH=$PDD_PATH in conda environment"
    info "Note: You'll need to reactivate the environment for this to take effect"
}

# Install development dependencies
install_dev_deps() {
    info "Installing development dependencies..."

    cd "$REPO_ROOT"

    # Run pip install in the conda environment
    conda run -n "$ENV_NAME" --no-capture-output pip install -e '.[dev]'

    success "Installed development dependencies"
}

# Print summary
print_summary() {
    echo ""
    echo -e "${GREEN}========================================${NC}"
    echo -e "${GREEN}  PDD Developer Setup Complete!${NC}"
    echo -e "${GREEN}========================================${NC}"
    echo ""
    echo "Environment Details:"
    echo "  Conda environment: $ENV_NAME"
    echo "  Python version:    $PYTHON_VERSION"
    echo "  Main project root: $PROJECT_ROOT"
    echo "  Working directory: $REPO_ROOT"
    echo "  PDD_PATH:          $REPO_ROOT/pdd"
    echo ""
    echo "Next Steps:"
    echo "  1. Activate the environment:"
    echo -e "     ${YELLOW}conda activate $ENV_NAME${NC}"
    echo ""
    echo "  2. Verify setup:"
    echo -e "     ${YELLOW}echo \$PDD_PATH${NC}"
    echo -e "     ${YELLOW}pdd --version${NC}"
    echo ""
    echo "  3. Run tests:"
    echo -e "     ${YELLOW}make test${NC}"
    echo ""
    if [[ -n "$WORKTREE_NAME" ]]; then
        echo "  4. Your worktree is at:"
        echo -e "     ${YELLOW}$REPO_ROOT${NC}"
        echo ""
        echo "  Worktrees are stored under:"
        echo -e "     ${YELLOW}$PROJECT_ROOT/.pdd/worktrees/${NC}"
        echo ""
    fi
    echo "For more information, see docs/ONBOARDING.md"
    echo ""
}

# Main execution
main() {
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}  PDD Developer Setup Script${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo ""

    check_prerequisites
    prompt_worktree
    create_worktree
    determine_env_name
    create_conda_env
    create_symlinks
    create_env_file
    set_conda_env_var
    install_dev_deps
    print_summary
}

main "$@"
