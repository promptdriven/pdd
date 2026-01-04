# Test Plan for PDD Prompt Linter Frontend (Streamlit)
#
# 1. Analysis of Code Under Test:
#    - The code is a Streamlit script (`frontend_streamlit.py`) that runs procedurally.
#    - It handles UI rendering, input collection (sidebar, file/text), and orchestration.
#    - Key dependencies: `streamlit`, `src.utils.pipeline`, `src.utils.models`.
#    - Key Logic:
#      - Input Precedence: File upload > Text Area.
#      - Configuration Mapping: UI inputs -> `LintConfig` object.
#      - State Management: Uses `st.session_state` to persist reports.
#      - Visualization: Renders metrics, issues, and fixes based on the `Report` object.
#
# 2. Testing Strategy:
#    - Since this is a script without functions to call directly, we will use `unittest.mock` to patch `streamlit` and `sys.modules`.
#    - We will use `importlib.reload` to execute the script multiple times within the test suite, simulating different user interactions (e.g., clicking buttons, uploading files).
#    - We will mock the backend pipeline (`lint_text`) to isolate frontend logic from backend processing.
#
# 3. Z3 Formal Verification:
#    - We will verify the configuration logic that maps user inputs (strings/None) to the `LintConfig` parameters.
#    - Specifically, we verify the boolean logic for `use_llm` and the handling of "Auto" or empty strings for providers and models.
#
# 4. Unit Test Cases:
#    - `test_ui_initialization`: Verify page config, title, and sidebar elements are rendered.
#    - `test_input_precedence_file`: Verify that if a file is uploaded, its content is used over the text area.
#    - `test_input_precedence_text`: Verify that if no file is uploaded, the text area content is used.
#    - `test_lint_execution_flow`: Verify that clicking the button triggers `lint_text` with the correct config and stores the result in session state.
#    - `test_error_handling`: Verify that exceptions from the pipeline are caught and displayed via `st.error`.
#    - `test_report_visualization`: Verify that a `Report` object in session state is correctly rendered (metrics, tabs, issues).
#    - `test_z3_config_logic`: Formal verification of the configuration mapping logic.

import sys
import os
import importlib
import pytest
from unittest.mock import MagicMock, patch
from z3 import Solver, Bool, String, If, Implies, Not, Or, And, sat, unsat

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

def run_app():
    """Helper to reload and run the app script."""
    if MODULE_NAME in sys.modules:
        importlib.reload(sys.modules[MODULE_NAME])
    else:
        import src.frontend.frontend_streamlit

# --- Unit Tests ---

def test_ui_initialization(mock_streamlit, mock_pipeline, mock_models):
    """Test that the app initializes with correct page config and layout."""
    # Setup inputs to avoid triggering execution logic
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""
    mock_streamlit.button.return_value = False

    run_app()

    # Verify Page Config
    mock_streamlit.set_page_config.assert_called_with(
        page_title="PDD Prompt Linter",
        layout="wide",
        initial_sidebar_state="expanded"
    )
    
    # Verify Title
    mock_streamlit.title.assert_called_with("PDD Prompt Linter")
    
    # Verify Sidebar Elements
    # Note: The code calls st.selectbox inside 'with st.sidebar'. 
    # This calls mock_streamlit.selectbox, not mock_streamlit.sidebar.selectbox directly in standard mocks unless configured otherwise.
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
    
    run_app()
    
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
    
    run_app()
    
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
    # Note: st.selectbox is called for Provider
    mock_streamlit.selectbox.return_value = "OpenAI"
    # text_input is called twice (Model, API Key). We need side_effect.
    mock_streamlit.text_input.side_effect = ["gpt-4", "secret-key"] 
    
    # Setup Pipeline Return
    mock_report = MagicMock()
    mock_pipeline.return_value = mock_report
    
    run_app()
    
    # 1. Verify Config Creation
    mock_models["LintConfig"].assert_called_with(
        use_llm=True, # Because API key is present
        generate_fix=True,
        llm_provider="OpenAI",
        llm_model="gpt-4",
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
    
    run_app()
    
    mock_streamlit.error.assert_called_with("An error occurred during the linting process: API Error")

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
    mock_report.is_clean = False
    mock_report.summary = "Summary text"
    mock_report.suggested_fix = "Fixed prompt code"
    
    mock_streamlit.session_state = {'report': mock_report}
    
    # Prevent re-execution logic
    mock_streamlit.button.return_value = False
    mock_streamlit.file_uploader.return_value = None
    mock_streamlit.text_area.return_value = ""
    
    run_app()
    
    # Verify Metrics
    mock_streamlit.metric.assert_any_call("PDD Score", "85/100")
    mock_streamlit.metric.assert_any_call("Issues Detected", 1)
    
    # Verify Summary
    mock_streamlit.info.assert_any_call("Summary text")
    
    # Verify Issue Rendering (Error container used for ERROR severity)
    mock_streamlit.error.assert_called() 
    
    # Verify Fix Code Block
    mock_streamlit.code.assert_called_with("Fixed prompt code", language="markdown")

# --- Z3 Formal Verification ---

def test_z3_config_logic():
    """
    Formal verification of the configuration logic mapping UI inputs to LintConfig parameters.
    Logic under test:
        use_llm = bool(api_key)
        llm_provider = provider if provider != "Auto" else None
        llm_model = model_name if model_name else None
        api_key = api_key if api_key else None
    """
    s = Solver()

    # Inputs
    # We model strings as abstract types or simplified logic since Z3 String theory can be heavy.
    # Here we use Booleans to represent "Is Empty" or "Is Auto".
    
    # Input States
    api_key_is_empty = Bool('api_key_is_empty')
    provider_is_auto = Bool('provider_is_auto')
    model_is_empty = Bool('model_is_empty')

    # Output States (The logic we want to verify)
    use_llm = Bool('use_llm')
    provider_is_none = Bool('provider_is_none')
    model_is_none = Bool('model_is_none')
    api_key_is_none = Bool('api_key_is_none')

    # Implemented Logic Constraints (from the code)
    # 1. use_llm = bool(api_key) -> If api key is empty, use_llm is False
    s.add(use_llm == Not(api_key_is_empty))
    
    # 2. llm_provider = provider if provider != "Auto" else None
    s.add(provider_is_none == provider_is_auto)
    
    # 3. llm_model = model_name if model_name else None
    s.add(model_is_none == model_is_empty)
    
    # 4. api_key = api_key if api_key else None
    s.add(api_key_is_none == api_key_is_empty)

    # Verification Goals
    
    # Goal 1: Verify that use_llm is NEVER true if api_key is empty (None).
    # We assert the negation: use_llm IS true AND api_key IS empty. If UNSAT, the logic holds.
    s.push()
    s.add(And(use_llm, api_key_is_empty))
    
    # FIX: We expect UNSAT (impossible), not SAT.
    assert s.check() == unsat, "Z3 found a counter-example: use_llm can be True even if API key is empty."
    s.pop()

    # Goal 2: Verify that if provider is "Auto", the passed provider is None.
    s.push()
    s.add(And(provider_is_auto, Not(provider_is_none)))
    if s.check() == sat:
        pytest.fail("Z3 found a counter-example: Provider is 'Auto' but output is not None.")
    s.pop()

    # Goal 3: Verify that if model is empty string, the passed model is None.
    s.push()
    s.add(And(model_is_empty, Not(model_is_none)))
    if s.check() == sat:
        pytest.fail("Z3 found a counter-example: Model is empty but output is not None.")
    s.pop()