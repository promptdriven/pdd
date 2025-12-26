

# Prompt-Driven Workflows
Refer to these workflows as needed throughout your Prompt-Driven product development lifecycle.

Each workflow in PDD addresses a fundamental development need:

"Daily-driver" workflows

* [Initial Development Workflow](#initial-development) - build up your PDD codebase
* [Feature Enhancement](#feature-enhancement) - enhance a feature
* [Code-to-Prompt Update](#code-to-prompt-update) - sync direct code changes back to your prompt base
* [Prompt Refactoring](#prompt-refactoring) - reorganize prompts for maintainabliity and reusability
* [Multi-Prompt Architecture](#multi-prompt-architecture) - coordinating systems with multiple prompts

Debugging Workflows

* [Prompt Context Issues](#prompt-context-issues) - resolve issues with misunderstandings in prompt interpretation or preprocessing
* [Runtime Crash Debugging](#runtime-crash-debugging) - fix code that fails to execute
* [Logical Bug Fixing](#logical-bug-fixing) - correct code that runs but produces incorrect results
* [Debugger Guided Analysis](#debugger-guided-analysis) - identify which prompt sections produce problematic code

More
* [Critical Dependencies](#critical-dependencies) - important constraints / requirements for any workflow
* [Workflow Selection Principles](#workflow-selection-principles) - how to choose a workflow depending on your development phase
<br>
<br>
----


<a name="initial-development"></a>
### Initial Development

**Purpose**: Create new functionality from scratch with proper testing and verification.

**Conceptual Flow**: Define dependencies → Generate implementation → Create interfaces → Ensure runtime functionality → Verify correctness

**Command Flow**: `auto-deps → generate → example → crash → verify → test → fix`

**Process**:
1. Identify and inject dependencies for your prompt (`auto-deps`).
2. Generate full implementation code from the prompt (`generate`).
3. Create reusable interface examples (`example`).
4. Ensure the code runs without crashing and fix runtime errors (`crash`).
5. Run the example and use an LLM to check if the output aligns with the prompt's intent, attempting iterative fixes if necessary (`verify`).
6. Generate comprehensive unit tests for the implementation (`test`).
7. Fix any issues revealed by the unit tests (`fix`).

**Key Insight**: This workflow follows a progression from concept to verified implementation, ensuring the code runs (`crash`) before checking functional output (`verify`) and detailed unit testing (`test`).

---

<a name="feature-enhancement"></a>
### Feature Enhancement

Use when adding capabilities to existing modules.

**Purpose**: Add new capabilities to existing functionality.

**Command Flow**: `change → generate → example → test → fix`

**Process**:
1. Modify prompts to describe new features
2. Regenerate code with enhanced functionality
3. Update examples to demonstrate new features
4. Test to verify correct implementation
5. Fix any issues that arise

**Key Insight**: Feature additions should flow from prompt changes rather than direct code modifications.

---

<a name="code-to-prompt-update"></a>
### Code-to-Prompt Update

This workflow ensures the information flow from code back to prompts, preserving prompts as the source of truth.

**Conceptual Flow**: Sync code changes to prompt → Identify impacts → Propagate changes

**Command Flow**: `update → detect → change`

**Purpose**: Maintain prompt as source of truth after code changes.

**Process**:
1. Synchronize direct code changes back to the original prompt
2. Detect other prompts that might be affected by these changes
3. Apply necessary changes to dependent prompts

**Key Insight**: This bidirectional flow ensures prompts remain the source of truth even when code changes happen first.

---
<a name="prompt-refactoring"></a>
### Prompt Refactoring

This workflow parallels code refactoring but operates at the prompt level.

**Purpose**: Break large prompts into modular components, improving organization and reusability.

**Conceptual Flow**: Extract functionality → Ensure dependencies → Create interfaces

**Command Flow**: `split → auto-deps → example`


**Process**:
1. Extract specific functionality from a large prompt into a separate prompt
2. Ensure the new prompt has all dependencies it needs
3. Create interface examples for the extracted functionality

**Key Insight**: Just as code should be modular, prompts benefit from decomposition into focused, reusable components.

---

### Debugging Workflows

<a name="prompt-context-issues"></a>
#### Prompt Context Issues

**Purpose**: Resolve issues with misunderstandings in prompt interpretation or preprocessing.

**Comamnd Flow**: `preprocess → generate`

**Process**:
1. Examine how the prompt is being preprocessed
2. Regenerate code with improved prompt clarity

---

<a name="runtime-crash-debugging"></a>
#### Runtime Crash Debugging

**Runtime Issues**: Fix code that fails to execute.

**Command Flow**: `generate → example → crash`

**Process**:
1. Generate initial code from prompt
2. Create examples and test programs
3. Fix runtime errors to make code executable

---

<a name="logical-bug-fixing"></a>
#### Logical Bug Fixing

**Purpose**: Correct code that runs but produces incorrect results.

**Command Flow**: `bug → fix`

**Process**:
1. Generate test cases that demonstrate the bug
2. Fix the code to pass the tests

---

<a name="debugger-guided-analysis"></a>
#### Debugger-Guided Analysis

**Traceability Issues**: Connecting code problems back to prompt sections - Identify which prompt sections produce problematic code.

**Command Flow**: `trace → [edit prompt]`

**Process**:
1. Locate the relationship between code lines and prompt sections
2. Update relevant prompt sections



---

**Multi-Prompt Architecture Workflow**

**Purpose**: Coordinating systems with multiple prompts
**Conceptual Flow**: Detect conflicts → Resolve incompatibilities → Regenerate code → Update interfaces → Verify system
   
This workflow addresses the complexity of managing multiple interdependent prompts.


--- 

<a name="multi-prompt-architecture"></a>
### Multi-Prompt Architecture

**Command Flow**: `conflicts/detect → change → generate → example → test`

**Purpose**: Coordinate multiple prompts derived from higher-level requirements.

**Process**:
1. Identify conflicts or dependencies between prompts
2. Harmonize the prompts to work together
3. Regenerate code from updated prompts
4. Update interface examples after changes
5. Verify system integration with tests

**Key Insight**: Complex systems require coordination between prompts, just as they do between code modules.

--- 



<a name="critical-dependencies"></a>
### Critical Dependencies

When using these workflows, remember these crucial tool dependencies:

- 'generate' must be done before 'example' or 'test'
- 'crash' is used to fix runtime errors and make code runnable
- 'fix' requires runnable code created/verified by 'crash'
- 'test' must be created before using 'fix'
- Always update 'example' after major prompt interface changes

For detailed command examples for each workflow, see the respective command documentation sections.

---


<a name="workflow-selection-principles"></a>
### Workflow Selection Principles

The choice of workflow should be guided by your current development phase:

1. **Creation Phase**: Use Initial Development when building new functionality.

2. **Maintenance Phase**: Use Code-to-Prompt Update when existing code changes.

3. **Problem-Solving Phase**: Choose the appropriate Debugging workflow based on the issue type:
   - Preprocess → Generate for prompt interpretation issues
   - Crash for runtime errors
   - Bug → Fix for logical errors
   - Trace for locating problematic prompt sections

4. **Restructuring Phase**: Use Refactoring when prompts grow too large or complex.

5. **System Design Phase**: Use Multi-Prompt Architecture when coordinating multiple components.

6. **Enhancement Phase**: Use Feature Enhancement when adding capabilities to existing modules.
