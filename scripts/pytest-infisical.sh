#!/bin/bash
# Wrapper script to run pytest with infisical secrets injection
# Used by VS Code Test Explorer to ensure tests have access to secrets
exec infisical run -- pytest "$@"
