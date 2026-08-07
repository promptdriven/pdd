<!-- pdd-story-prompts: prompts/conformance/declared_surface_python.prompt, prompts/conformance/directives_python.prompt, prompts/conformance/gate_errors_python.prompt, prompts/conformance/interface_check_python.prompt, prompts/conformance/surface_python.prompt, prompts/conformance/test_churn_python.prompt, prompts/code_generator_main_python.prompt -->
<!-- pdd-story-dev-units: prompts/conformance/declared_surface_python.prompt, prompts/conformance/directives_python.prompt, prompts/conformance/gate_errors_python.prompt, prompts/conformance/interface_check_python.prompt, prompts/conformance/surface_python.prompt, prompts/conformance/test_churn_python.prompt, prompts/code_generator_main_python.prompt -->

# User Story: Generation safety checks must survive PDD's own internal reorganisation

## Story
As a developer, I can rely on PDD to consistently enforce its safety checks during code generation regardless of its internal changes, so that my existing work is never silently corrupted or overwritten by invalid model output.
