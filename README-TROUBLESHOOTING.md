
## Troubleshooting

Here are some common issues and their solutions:

1. **Command not found**: Ensure PDD is properly installed and added to your system's PATH.

2. **Permission denied errors**: Check that you have the necessary permissions to read input files and write to output locations.

3. **AI model not responding**: Verify your internet connection and check the status of the AI service.

4. **Unexpected output**: Try adjusting the `--strength` and `--temperature` parameters to fine-tune the AI model's behavior.

5. **High costs**: Use the `--output-cost` option to track usage and set appropriate budgets for the `fix` command's `--budget` option.

6. **Dependency scanning issues**: If the `auto-deps` command fails to identify relevant dependencies:
   - Check that the file paths and glob patterns are correct
   - Use the `--force-scan` option to ensure all files are re-analyzed
   - Verify the CSV file format and content
   - Check file permissions for the dependency directory

7. **Command Timeout**:
   - Check internet connection
   - Try running with `--local` flag to compare
   - If persistent, check PDD Cloud status page

8. **Sync-Specific Issues**:
   - **"Another sync is running"**: Check for stale locks in `.pdd/locks/` directory and remove if process no longer exists
   - **Complex conflict resolution problems**: Use `pdd --verbose sync --dry-run basename` to see detailed LLM reasoning and decision analysis
   - **State corruption or unexpected behavior**: Delete `.pdd/meta/{basename}_{language}.json` to reset fingerprint state
   - **Animation display issues**: Sync operations work in background; animation is visual feedback only and doesn't affect functionality
   - **Fingerprint mismatches**: Use `pdd sync --dry-run basename` to see what changes were detected and why operations were recommended

If you encounter persistent issues, consult the PDD documentation or post an issue on GitHub for assistance.



## Troubleshooting Common Installation Issues

1. **Command not found**
   ```bash
   # Add to PATH if needed
   export PATH="$HOME/.local/bin:$PATH"
   ```

2. **Permission errors**
   ```bash
   # Install with user permissions
   pip install --user pdd-cli
   ```

3. **macOS-specific issues**
   - **Xcode Command Line Tools not found**: Run `xcode-select --install` to install the required development tools
   - **Homebrew not found**: Install Homebrew using the command in the prerequisites section above
   - **Python not found or wrong version**: Install Python 3 via Homebrew: `brew install python`
   - **Permission denied during compilation**: Ensure Xcode Command Line Tools are properly installed and you have write permissions to the installation directory
   - **uv installation fails**: Try installing uv through Homebrew: `brew install uv`
   - **Python version conflicts**: If you have multiple Python versions, ensure `python3` points to Python 3.8+: `which python3 && python3 --version`
