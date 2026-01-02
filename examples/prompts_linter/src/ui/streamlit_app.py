import streamlit as st
import requests
import os
import json
from typing import Dict, Any

# --- Configuration ---
# Default to localhost, but allow env var override
API_URL = os.getenv("PDD_API_URL", "http://localhost:8000/lint")

# --- Helper Functions ---

def get_severity_color(severity: str) -> str:
    """Returns a color hex or name based on severity."""
    severity = severity.lower()
    if severity == "error":
        return "red"
    elif severity == "warning":
        return "orange"
    elif severity == "info":
        return "blue"
    return "grey"

def render_finding(finding: Dict[str, Any]):
    """Renders a single finding using Streamlit containers."""
    severity = finding.get("severity", "info").lower()
    
    # Choose the appropriate container based on severity
    if severity == "error":
        container = st.error
    elif severity == "warning":
        container = st.warning
    else:
        container = st.info

    with container(f"[{finding.get('rule_id', 'N/A')}] {finding.get('title', 'Untitled Issue')}"):
        st.markdown(f"**Message:** {finding.get('message', '')}")
        
        # Handle Line Numbers
        # Support both 'line_numbers' (list) and 'evidence' (dict with start/end)
        lines_str = ""
        if 'line_numbers' in finding:
            lines = finding['line_numbers']
            if lines:
                lines_str = ', '.join(map(str, lines))
        elif 'evidence' in finding:
            evidence = finding['evidence']
            if isinstance(evidence, dict):
                start = evidence.get('line_start')
                end = evidence.get('line_end')
                if start is not None:
                    if end is not None and end != start:
                        lines_str = f"{start}-{end}"
                    else:
                        lines_str = str(start)
        
        if lines_str:
            st.markdown(f"**Line(s):** {lines_str}")
        
        # Handle Suggested Edits
        # Support both 'suggestion' (str) and 'suggested_edits' (list of dicts)
        suggestion = finding.get('suggestion')
        if not suggestion and 'suggested_edits' in finding:
            edits = finding['suggested_edits']
            if isinstance(edits, list) and edits:
                # Display the first suggestion's snippet
                first_edit = edits[0]
                if isinstance(first_edit, dict):
                    suggestion = first_edit.get('snippet')

        if suggestion:
            st.markdown("**Suggested Edit:**")
            st.code(suggestion, language="markdown")

def call_lint_api(content: str, resolve_includes: bool) -> Dict[str, Any]:
    """Sends the content to the backend API for linting."""
    payload = {
        "prompt_text": content,
        "options": {"resolve_includes": resolve_includes}
    }
    
    try:
        response = requests.post(API_URL, json=payload)
        response.raise_for_status()
        return response.json()
    except requests.exceptions.ConnectionError:
        st.error(f"Could not connect to the backend API at `{API_URL}`. Is the server running?")
        return None
    except requests.exceptions.HTTPError as e:
        st.error(f"API returned an error: {e}")
        return None
    except Exception as e:
        st.error(f"An unexpected error occurred: {e}")
        return None

# --- Main Application ---

def main():
    st.set_page_config(
        page_title="PDD Prompt Linter",
        page_icon="🔍",
        layout="wide"
    )

    # 1. Header
    st.title("🔍 PDD Prompt Linter")
    st.markdown("Analyze your prompts for best practices, potential errors, and token usage.")

    # 2. Sidebar Configuration
    with st.sidebar:
        st.header("Configuration")
        resolve_includes = st.checkbox(
            "Resolve Includes", 
            value=False, 
            help="Attempt to resolve file includes for more accurate token estimation."
        )
        
        st.divider()
        st.caption(f"Backend API: `{API_URL}`")

    # 3. Input Area
    st.subheader("Input Prompt")
    
    # File Uploader
    uploaded_file = st.file_uploader("Upload a file (.prompt, .md, .txt)", type=["prompt", "md", "txt"])
    
    # Logic to populate text area from file
    if uploaded_file is not None:
        # Read file as string
        string_data = uploaded_file.getvalue().decode("utf-8")
        # Update session state to populate the text area
        if "prompt_input" not in st.session_state or st.session_state["prompt_input"] != string_data:
             st.session_state["prompt_input"] = string_data
    
    # Text Area (bound to session state for persistence/updates)
    prompt_text = st.text_area(
        "Or paste your prompt text here:", 
        height=300, 
        key="prompt_input"
    )

    # 4. Action Button
    if st.button("Lint Prompt", type="primary"):
        if not prompt_text.strip():
            st.warning("Please enter some text or upload a file to lint.")
        else:
            with st.spinner("Analyzing prompt..."):
                result = call_lint_api(prompt_text, resolve_includes)
                if result:
                    st.session_state['lint_result'] = result

    # 5. Result Rendering
    if 'lint_result' in st.session_state:
        report = st.session_state['lint_result']
        summary = report.get("summary", {})
        
        st.divider()
        st.header("Analysis Results")

        # Summary Metrics
        col1, col2, col3, col4 = st.columns(4)
        
        # Calculate counts safely
        findings = report.get("findings", [])
        error_count = sum(1 for f in findings if f.get("severity") == "error")
        warn_count = sum(1 for f in findings if f.get("severity") == "warning")
        info_count = sum(1 for f in findings if f.get("severity") == "info")
        
        with col1:
            st.metric("Overall Score", f"{summary.get('score', 0)}/100")
        with col2:
            st.metric("Errors", error_count)
        with col3:
            st.metric("Warnings", warn_count)
        with col4:
            # Handle token count structure
            token_count = summary.get("token_count_estimate", "N/A")
            st.metric("Est. Tokens", token_count)

        # Findings List
        st.subheader("Findings")
        
        if not findings:
            st.success("No issues found! Your prompt looks clean.")
        else:
            # Sort findings by severity (Error > Warning > Info)
            severity_order = {"error": 0, "warning": 1, "info": 2}
            sorted_findings = sorted(
                findings, 
                key=lambda x: severity_order.get(x.get("severity", "info").lower(), 3)
            )

            for finding in sorted_findings:
                render_finding(finding)

        # 7. Export
        st.divider()
        json_str = json.dumps(report, indent=2)
        st.download_button(
            label="Download JSON Report",
            data=json_str,
            file_name="lint_report.json",
            mime="application/json"
        )

if __name__ == "__main__":
    main()