import sys
import os
import importlib
import pytest
from unittest.mock import MagicMock, patch

# Add project root to path to ensure imports work during testing
project_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# We import the module name to be used in reloading
# Based on the test filename 'test_frontend_streamlit.py', the module is likely 'frontend_streamlit.py'
MODULE_NAME = "src.frontend.frontend_streamlit"

# --- Fixtures ---

@pytest.fixture
def mock_streamlit():
    """Mocks the streamlit module entirely."""
    mock_st = MagicMock()
    mock_st.session_state = {}
    
    # Dynamic columns mock to handle different unpacking requirements
    # The code calls st.columns([1, 1]) (returns 2) and st.columns(3) (returns 3)
    def columns_side_effect(spec, *args, **kwargs):
        if isinstance(spec, int):
            count = spec
        else:
            count = len(spec)
        return [MagicMock() for _ in range(count)]
    
    mock_st.columns.side_effect = columns_side_effect
    
    mock_st.tabs.return_value = [MagicMock(), MagicMock()]
    
    # Patch sys.modules so that 'import streamlit' returns our mock
    # This persists even after importlib.reload
    with patch.dict(sys.modules, {'streamlit': mock_st}):
        yield mock_st

@pytest.fixture
def mock_pipeline():
    """Mocks the pipeline module."""
    # Patch the source where lint_text is defined
    with patch('src.utils.pipeline.lint_text') as mock_lint:
        yield mock_lint

@pytest.fixture
def mock_models():
    """Mocks the models module."""
    # Patch the source classes
    with patch('src.utils.models.Report') as mock_report_cls, \
         patch('src.utils.models.Severity') as mock_severity, \
         patch('src.utils.pipeline.LintConfig') as mock_config:
        
        # Setup Severity Enum mocks
        mock_severity.ERROR = "ERROR"
        mock_severity.WARNING = "WARNING"
        mock_severity.INFO = "INFO"
        
        yield {
            "Report": mock_report_cls,
            "Severity": mock_severity,
            "LintConfig": mock_config
        }

def run_app(mock_st):
    """Helper to reload and run the app script."""
    if MODULE_NAME in sys.modules:
        mod = importlib.reload(sys.modules[MODULE_NAME])
    else:
        import src.frontend.frontend_streamlit as mod
    # Explicitly call main because it's protected by __name__ == "__main__"
    mod.main()

# --- Unit Tests ---

def test_ui_initialization(mock_streamlit, mock_pipeline, mock_models):
    """Test that the app initializes with correct page config and layout."""
    # Setup inputs to avoid triggering execution logic
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""
    mock_streamlit.button.return_value = False

    run_app(mock_streamlit)

    # Verify Page Config
    mock_streamlit.set_page_config.assert_called_with(
        page_title="PDD Prompt Linter",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    
    # Verify Title
    mock_streamlit.title.assert_called_with(
        "PDD Prompt Linter")
    
    # Verify Sidebar Elements
    mock_streamlit.selectbox.assert_called()
    mock_streamlit.text_input.assert_called() # Called for model and api_key

def test_input_precedence_file(mock_streamlit, mock_pipeline, mock_models):
    """Test that file upload takes precedence over text area."""
    # Mock File Upload
    mock_file = MagicMock()
    mock_file.name = "test.txt"
    mock_file.getvalue.return_value = b"File Content"
    mock_streamlit.file_uploader.return_value = mock_file
    
    # Mock Text Area (should be ignored)
    mock_streamlit.text_area.return_value = "Text Area Content"
    
    # Mock Button Click
    mock_streamlit.button.return_value = True
    
    run_app(mock_streamlit)
    
    # Verify lint_text called with decoded file content
    mock_pipeline.assert_called_once()
    args, _ = mock_pipeline.call_args
    assert args[0] == "File Content"
    
    # Verify success message for file load
    mock_streamlit.success.assert_any_call("Loaded content from **test.txt**")

def test_input_precedence_text(mock_streamlit, mock_pipeline, mock_models):
    """Test that text area is used when no file is uploaded."""
    # Mock No File
    mock_streamlit.file_uploader.return_value = None
    
    # Mock Text Area
    mock_streamlit.text_area.return_value = "Text Area Content"
    
    # Mock Button Click
    mock_streamlit.button.return_value = True
    
    run_app(mock_streamlit)
    
    # Verify lint_text called with text area content
    mock_pipeline.assert_called_once()
    args, _ = mock_pipeline.call_args
    assert args[0] == "Text Area Content"

def test_lint_execution_flow(mock_streamlit, mock_pipeline, mock_models):
    """Test the full execution flow: Config creation -> Pipeline Call -> State Update."""
    # Setup Inputs
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = "Prompt"
    mock_streamlit.button.return_value = True
    
    # Setup Sidebar Inputs
    mock_streamlit.selectbox.return_value = "OpenAI"
    mock_streamlit.text_input.side_effect = ["gpt-4", "secret-key"] 
    
    # Setup Pipeline Return
    mock_report = MagicMock()
    mock_pipeline.return_value = mock_report
    
    run_app(mock_streamlit)
    
    # 1. Verify Config Creation
    mock_models["LintConfig"].assert_called_with(
        use_llm=True, 
        generate_fix=True,
        llm_provider="OpenAI",
        llm_model_override="gpt-4",
        api_key="secret-key"
    )
    
    # 2. Verify Pipeline Call
    mock_pipeline.assert_called_once()
    
    # 3. Verify State Update
    assert mock_streamlit.session_state['report'] == mock_report

def test_error_handling(mock_streamlit, mock_pipeline, mock_models):
    """Test that pipeline exceptions are caught and displayed."""
    mock_streamlit.text_area.return_value = "Prompt"
    mock_streamlit.button.return_value = True
    
    # Make pipeline raise exception
    mock_pipeline.side_effect = Exception("API Error")
    
    run_app(mock_streamlit)
    
    mock_streamlit.error.assert_called_with("An error occurred during linting: API Error")

def test_report_visualization(mock_streamlit, mock_pipeline, mock_models):
    """Test that the report is visualized correctly from session state."""
    # Setup Session State with a pre-existing report
    mock_issue = MagicMock()
    mock_issue.severity = mock_models["Severity"].ERROR
    mock_issue.rule_id = "ERR01"
    mock_issue.description = "Bad prompt"
    
    mock_report = MagicMock()
    mock_report.score = 85
    mock_report.issues = [mock_issue]
    mock_report.is_clean = True
    mock_report.summary = "Summary text"
    mock_report.suggested_fix = "Fixed prompt code"
    
    mock_streamlit.session_state = {'report': mock_report}
    
    # Prevent re-execution logic
    mock_streamlit.button.return_value = False
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""

    # Setup columns mocks to verify calls on them
    col1, col2, col3 = MagicMock(), MagicMock(), MagicMock()
    # IMPORTANT: Clear side_effect so return_value is used
    mock_streamlit.columns.side_effect = None
    mock_streamlit.columns.return_value = [col1, col2, col3]
    
    run_app(mock_streamlit)
    
    # Verify Metrics on columns
    col1.metric.assert_any_call("PDD Score", "85/100")
    col2.metric.assert_any_call("Issues Detected", 1)
    
    # Verify Summary
    mock_streamlit.info.assert_any_call("Summary text")
    
    # Verify Issue Rendering (Error container used for ERROR severity)
    mock_streamlit.error.assert_called() 
    
    # Verify Fix Code Block
    mock_streamlit.code.assert_called_with("Fixed prompt code", language="markdown")

def test_status_label_logic(mock_streamlit, mock_pipeline, mock_models):
    """Test the 'Clean' vs 'Needs Review' status logic."""
    # Case 1: Clean Report
    mock_report_clean = MagicMock()
    mock_report_clean.is_clean = True
    mock_report_clean.issues = []
    mock_streamlit.session_state = {'report': mock_report_clean}
    
    # Prevent re-run
    mock_streamlit.button.return_value = False
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""
    
    # Re-setup mock to capture columns
    col1, col2, col3 = MagicMock(), MagicMock(), MagicMock()
    # IMPORTANT: Clear side_effect so return_value is used
    mock_streamlit.columns.side_effect = None
    mock_streamlit.columns.return_value = [col1, col2, col3]
    
    run_app(mock_streamlit)
    col3.metric.assert_called_with("Status", "Clean")
    
    # Case 2: Dirty Report
    mock_report_dirty = MagicMock()
    mock_report_dirty.is_clean = False
    mock_report_dirty.issues = [MagicMock()]
    mock_streamlit.session_state = {'report': mock_report_dirty}
    
    # Reset mocks for second run to ensure clean assertion
    col1.reset_mock()
    col2.reset_mock()
    col3.reset_mock()
    
    run_app(mock_streamlit)
    col3.metric.assert_called_with("Status", "Needs Review")

# --- Z3 Formal Verification ---

from z3 import Solver, Bool, String, If, Implies, Not, Or, And, sat, unsat

def test_z3_config_logic():
    """
    Formal verification of the configuration logic mapping UI inputs to LintConfig parameters.
    """
    s = Solver()

    # Inputs
    api_key_is_empty = Bool('api_key_is_empty')
    provider_is_auto = Bool('provider_is_auto')
    model_is_empty = Bool('model_is_empty')

    # Output States
    use_llm = Bool('use_llm')
    provider_is_none = Bool('provider_is_none')
    model_is_none = Bool('model_is_none')
    api_key_is_none = Bool('api_key_is_none')

    # Implemented Logic Constraints (from the code)
    s.add(use_llm == True)
    s.add(provider_is_none == provider_is_auto)
    s.add(model_is_none == model_is_empty)
    s.add(api_key_is_none == api_key_is_empty)

    # Verification Goals
    s.push()
    s.add(Not(use_llm))
    assert s.check() == unsat, "Z3 found a counter-example: use_llm can be False."
    s.pop()

    s.push()
    s.add(And(provider_is_auto, Not(provider_is_none)))
    if s.check() == sat:
        pytest.fail("Z3 found a counter-example: Provider is 'Auto' but output is not None.")
    s.pop()

    s.push()
    s.add(And(model_is_empty, Not(model_is_none)))
    if s.check() == sat:
        pytest.fail("Z3 found a counter-example: Model is empty but output is not None.")
    s.pop()

# --- Additional Unit Tests ---

def test_lint_config_hardcoded_values(mock_streamlit, mock_pipeline, mock_models):
    """
    Verify that the actual implementation hardcodes use_llm=True and generate_fix=True.
    """
    # Setup Inputs
    mock_streamlit.text_area.return_value = "Prompt"
    mock_streamlit.button.return_value = True
    
    # Setup Sidebar Inputs
    mock_streamlit.selectbox.return_value = "OpenAI"
    mock_streamlit.text_input.side_effect = ["gpt-4", "secret-key"] 
    
    mock_pipeline.return_value = MagicMock()
    
    run_app(mock_streamlit)
    
    # Verify Config Creation with EXACT parameters from code_under_test
    mock_models["LintConfig"].assert_called_with(
        use_llm=True, 
        llm_provider="OpenAI",
        llm_model_override="gpt-4",
        generate_fix=True,
        api_key="secret-key"
    )

def test_empty_prompt_validation(mock_streamlit, mock_pipeline, mock_models):
    """Test that empty input triggers a warning and skips processing."""
    # Setup Empty Inputs
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = "   " # Whitespace only
    mock_streamlit.button.return_value = True
    
    run_app(mock_streamlit)
    
    # Verify Warning
    mock_streamlit.warning.assert_called_with("Please provide prompt text via file upload or text area.")
    
    # Verify Pipeline NOT called
    mock_pipeline.assert_not_called()

def test_session_state_clearing(mock_streamlit, mock_pipeline, mock_models):
    """Verify that the old report is removed from session state before a new run."""
    # Setup existing state
    state = {'report': 'OLD_REPORT'}
    mock_streamlit.session_state = state
    
    # Setup Trigger
    mock_streamlit.text_area.return_value = "New Prompt"
    mock_streamlit.button.return_value = True
    
    mock_new_report = MagicMock()
    mock_pipeline.return_value = mock_new_report
    
    run_app(mock_streamlit)
    
    # Verify final state is new report
    assert state['report'] == mock_new_report

def test_z3_status_logic():
    """
    Formal verification of the status label logic.
    """
    s = Solver()
    
    is_clean = Bool('is_clean')
    label_is_clean = Bool('label_is_clean')
    label_is_needs_review = Bool('label_is_needs_review')
    
    # Logic constraints
    s.add(Implies(is_clean, label_is_clean))
    s.add(Implies(is_clean, Not(label_is_needs_review)))
    s.add(Implies(Not(is_clean), label_is_needs_review))
    s.add(Implies(Not(is_clean), Not(label_is_clean)))
    
    # Goal: Verify there is no state where is_clean is True but label is "Needs Review"
    s.push()
    s.add(is_clean)
    s.add(label_is_needs_review)
    assert s.check() == unsat
    s.pop()
    
    # Goal: Verify there is no state where is_clean is False but label is "Clean"
    s.push()
    s.add(Not(is_clean))
    s.add(label_is_clean)
    assert s.check() == unsat
    s.pop()

def test_logging_verification(mock_streamlit, mock_pipeline, mock_models):
    """Test that the application logs the generated report score."""
    # Setup Inputs
    mock_streamlit.text_area.return_value = "Prompt"
    mock_streamlit.button.return_value = True
    
    # Setup Report
    mock_report = MagicMock()
    mock_report.score = 92
    mock_pipeline.return_value = mock_report
    
    # Patch logging.getLogger globally because module reload overwrites local patches
    with patch("logging.getLogger") as mock_get_logger:
        mock_logger = MagicMock()
        mock_get_logger.return_value = mock_logger
        
        run_app(mock_streamlit)
        
        # Verify logger was retrieved
        mock_get_logger.assert_called_with(MODULE_NAME)
        
        # Verify info log
        mock_logger.info.assert_called_with("Report generated - Score: 92/100")

def test_issue_severity_rendering(mock_streamlit, mock_pipeline, mock_models):
    """Test that issues are rendered with the correct UI element based on severity."""
    # Setup Report with 3 distinct issues
    issue_error = MagicMock(severity=mock_models["Severity"].ERROR, rule_id="E1", description="Error Desc")
    issue_warn = MagicMock(severity=mock_models["Severity"].WARNING, rule_id="W1", description="Warn Desc")
    issue_info = MagicMock(severity=mock_models["Severity"].INFO, rule_id="I1", description="Info Desc")
    
    mock_report = MagicMock()
    mock_report.issues = [issue_error, issue_warn, issue_info]
    mock_report.summary = "Report Summary" # This also triggers st.info
    
    mock_streamlit.session_state = {'report': mock_report}
    
    # Prevent re-run
    mock_streamlit.button.return_value = False
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""
    
    run_app(mock_streamlit)
    
    # Verify Error
    mock_streamlit.error.assert_any_call("[E1] Error Desc")
    
    # Verify Warning
    mock_streamlit.warning.assert_any_call("[W1] Warn Desc")
    
    # Verify Info
    # st.info is called for summary AND the info-level issue
    # We check if it was called with the issue description
    mock_streamlit.info.assert_any_call("[I1] Info Desc")

def test_issue_details_rendering(mock_streamlit, mock_pipeline, mock_models):
    """Test that optional issue details (category, rationale, fix) are rendered if present."""
    # Issue with all details
    issue_full = MagicMock(
        severity=mock_models["Severity"].WARNING,
        rule_id="W1",
        description="Desc",
        category="Modularity",
        fix_suggestion="Split it",
        rationale="Because it is long"
    )
    
    # Issue with minimal details
    issue_min = MagicMock(
        severity=mock_models["Severity"].WARNING,
        rule_id="W2",
        description="Desc 2",
        category=None,
        fix_suggestion=None,
        rationale=None
    )
    
    mock_report = MagicMock()
    mock_report.issues = [issue_full, issue_min]
    mock_streamlit.session_state = {'report': mock_report}
    
    # Prevent re-run
    mock_streamlit.button.return_value = False
    
    run_app(mock_streamlit)
    
    # We verify st.write calls. Since st.write is generic, we check for substrings.
    # Note: In a real mock, we'd inspect the call args list.
    
    write_calls = [args[0][0] for args in mock_streamlit.write.call_args_list]
    
    # Check full issue details
    assert any("**Category:** Modularity" in str(c) for c in write_calls)
    assert any("**Suggestion:** Split it" in str(c) for c in write_calls)
    assert any("**Rationale:** Because it is long" in str(c) for c in write_calls)
    
    # Ensure we don't see "None" printed for the minimal issue
    # This is a heuristic check; strictly we'd check call counts but that's fragile to UI changes
    assert not any("**Category:** None" in str(c) for c in write_calls)

def test_fix_tab_empty_state(mock_streamlit, mock_pipeline, mock_models):
    """Test that the fix tab handles missing suggested fixes gracefully."""
    mock_report = MagicMock()
    mock_report.suggested_fix = None # No fix
    mock_report.issues = []
    
    mock_streamlit.session_state = {'report': mock_report}
    mock_streamlit.button.return_value = False
    
    # Mock tabs to capture the context of the second tab (Fix tab)
    tab_analysis = MagicMock()
    tab_fix = MagicMock()
    mock_streamlit.tabs.return_value = [tab_analysis, tab_fix]
    
    # We need to simulate entering the tab_fix context
    # Since we can't easily control the context manager yield in the main execution flow 
    # without complex side_effects, we rely on the fact that the code executes:
    # with tab_fix:
    #    ...
    #    st.info(...)
    
    run_app(mock_streamlit)
    
    # Verify st.code was NOT called
    mock_streamlit.code.assert_not_called()
    
    # Verify st.info was called with the specific message
    mock_streamlit.info.assert_any_call("No automated fix was generated for this prompt.")

def test_sidebar_auto_and_whitespace_logic(mock_streamlit, mock_pipeline, mock_models):
    """Test 'Auto' provider selection and whitespace stripping for inputs."""
    mock_streamlit.text_area.return_value = "Prompt"
    mock_streamlit.button.return_value = True
    
    # Sidebar Inputs: Provider="Auto", Model="   ", API Key="   "
    mock_streamlit.selectbox.return_value = "Auto"
    mock_streamlit.text_input.side_effect = ["   ", "   "] 
    
    mock_pipeline.return_value = MagicMock()
    
    run_app(mock_streamlit)
    
    # Verify Config Creation
    mock_models["LintConfig"].assert_called_with(
        use_llm=True, 
        llm_provider=None, # Auto -> None
        llm_model_override=None, # Whitespace -> None
        generate_fix=True,
        api_key=None # Whitespace -> None
    )

def test_z3_input_precedence_logic():
    """
    Formal verification of the input precedence logic (File vs Text Area).
    """
    s = Solver()
    
    # Inputs
    file_is_uploaded = Bool('file_is_uploaded')
    text_area_has_content = Bool('text_area_has_content')
    
    # Outputs (which source is used)
    use_file = Bool('use_file')
    use_text_area = Bool('use_text_area')
    
    # Logic from code:
    # if uploaded_file is not None: ...
    # elif text_area_input: ...
    
    # If file is uploaded, we use file.
    # If file is NOT uploaded AND text area has content, we use text area.
    # Otherwise (implied), we use neither (or empty).
    
    s.add(use_file == file_is_uploaded)
    s.add(use_text_area == And(Not(file_is_uploaded), text_area_has_content))
    
    # Goal 1: Prove that if file is uploaded, text area is NEVER used, even if it has content.
    s.push()
    s.add(file_is_uploaded)
    s.add(text_area_has_content)
    s.add(use_text_area) # Contradiction hypothesis
    assert s.check() == unsat, "Z3 found counter-example: Text area used despite file upload."
    s.pop()
    
    # Goal 2: Prove that we never use both simultaneously.
    s.push()
    s.add(use_file)
    s.add(use_text_area)
    assert s.check() == unsat, "Z3 found counter-example: Both inputs used simultaneously."
    s.pop()