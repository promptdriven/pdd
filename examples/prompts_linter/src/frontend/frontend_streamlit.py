import sys
import os
import logging
import streamlit as st

# --- Path Setup ---
# Add the project root to sys.path to allow imports from 'src'
# This assumes the script is running from src/frontend/
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..', '..'))

if project_root not in sys.path:
    sys.path.insert(0, project_root)

# --- Imports ---
try:
    from src.utils.pipeline import lint_text, LintConfig
    from src.utils.models import Severity
except ImportError as e:
    # We use st.error and st.stop to handle this gracefully in the UI
    # Note: st.set_page_config must be the first Streamlit command, 
    # but we can't call it if imports fail before main. 
    # However, for the specific unit test scenario, we handle the import inside the try/except block.
    if "streamlit" in sys.modules:
        st.error(f"Critical Import Error: {e}. Please ensure the application is running from the correct directory structure.")
        st.stop()
    else:
        raise

def main():
    st.set_page_config(
        page_title="PDD Prompt Linter",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    
    st.title("PDD Prompt Linter")

    # --- Sidebar Configuration ---
    with st.sidebar:
        st.header("Configuration")
        
        llm_provider_input = st.selectbox(
            "LLM Provider", 
            ["Auto", "OpenAI", "Anthropic", "Google", "Custom"]
        )
        
        llm_model_input = st.text_input("Model Name (Optional)", help="Override the default model for the selected provider.")
        
        api_key_input = st.text_input("API Key", type="password", help="API Key for the selected provider. Not stored persistently.")

    # --- Input Section ---
    # Layout: File uploader and Text area
    # Logic: File takes precedence
    
    uploaded_file = st.file_uploader("Upload Prompt File", type=['txt', 'md', 'prompt'])
    text_area_input = st.text_area("Or paste prompt text here", height=300)
    
    if st.button("Lint Prompt", type="primary"):
        prompt_text = ""
        
        # Input Precedence Logic
        if uploaded_file is not None:
            # Decode bytes to string
            prompt_text = uploaded_file.getvalue().decode("utf-8")
            st.success(f"Loaded content from **{uploaded_file.name}**")
        elif text_area_input:
            prompt_text = text_area_input
        
        # Validation
        if not prompt_text.strip():
            st.warning("Please provide prompt text via file upload or text area.")
        else:
            # Prepare Configuration
            # Map empty strings to None
            model = llm_model_input.strip() if llm_model_input.strip() else None
            
            # Create config with correct parameter names
            config = LintConfig(
                use_llm=True,  # Always use LLM
                llm_model_override=model,  # Correct parameter name
                generate_fix=True  # Always generate fix
            )
            
            # Execute Pipeline
            with st.spinner("Analyzing prompt..."):
                try:
                    # Clear old report to ensure fresh results and score updates
                    if 'report' in st.session_state:
                        del st.session_state['report']
                    
                    report = lint_text(prompt_text, config=config)
                    st.session_state['report'] = report
                    
                    # Log the report
                    logger = logging.getLogger(__name__)
                    logger.info(f"Report generated - Score: {report.score}/100, Issues: {len(report.issues)}, Clean: {report.is_clean}, Summary: {report.summary}")
                    if report.issues:
                        error_count = sum(1 for i in report.issues if i.severity == Severity.ERROR)
                        warning_count = sum(1 for i in report.issues if i.severity == Severity.WARNING)
                        info_count = sum(1 for i in report.issues if i.severity == Severity.INFO)
                        logger.info(f"Issue breakdown - Errors: {error_count}, Warnings: {warning_count}, Info: {info_count}")
                    if hasattr(report, 'suggested_fix') and report.suggested_fix:
                        logger.info(f"Suggested fix generated (length: {len(report.suggested_fix)} chars)")
                except Exception as e:
                    st.error(f"An error occurred during linting: {e}")

    # --- Results Visualization ---
    if 'report' in st.session_state:
        report = st.session_state['report']
        
        st.divider()
        
        # 1. Top Metrics
        col1, col2, col3 = st.columns(3)
        col1.metric("PDD Score", f"{report.score}/100")
        col2.metric("Issues Detected", len(report.issues))
        
        status_label = "Clean" if report.is_clean else "Needs Review"
        col3.metric("Status", status_label)
        
        # 2. Tabs for Report and Fix
        tab_analysis, tab_fix = st.tabs(["Analysis Report", "Refactored Prompt"])
        
        with tab_analysis:
            st.subheader("Executive Summary")
            st.info(report.summary)
            
            st.subheader("Detailed Issues")
            if not report.issues:
                st.success("No issues detected. The prompt follows PDD guidelines.")
            
            for issue in report.issues:
                # Determine UI element based on severity
                severity_label = f"[{issue.rule_id}] {issue.description}"
                
                if issue.severity == Severity.ERROR:
                    st.error(severity_label)
                elif issue.severity == Severity.WARNING:
                    st.warning(severity_label)
                else:
                    st.info(severity_label)
                
                # Details expander
                with st.expander("See details & rationale"):
                    if hasattr(issue, 'category') and issue.category:
                        st.write(f"**Category:** {issue.category}")
                    
                    # Some issues might have a rationale attached (from LLM) or just a description
                    # We display the fix suggestion if available as part of the rationale
                    if issue.fix_suggestion:
                        st.write(f"**Suggestion:** {issue.fix_suggestion}")
                    
                    # If the issue object has a specific rationale field (depends on implementation), display it
                    if hasattr(issue, 'rationale') and issue.rationale:
                         st.write(f"**Rationale:** {issue.rationale}")

        with tab_fix:
            st.subheader("Suggested Fix")
            # Check if a fix was generated
            if hasattr(report, 'suggested_fix') and report.suggested_fix:
                st.code(report.suggested_fix, language="markdown")
            else:
                st.info("No automated fix was generated for this prompt. This might be because the score is high or the LLM was not configured.")

if __name__ == "__main__":
    main()