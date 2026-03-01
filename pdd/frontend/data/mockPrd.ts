export const mockPrd = `
# Product Requirements: Prompt Driven Development IDE

## 1. Overview
The Prompt Driven Development IDE is a web-based graphical user interface (GUI) designed to help developers construct and understand command-line instructions for the Prompt-Driven Development (pdd) tool. It provides a user-friendly way to generate commands for scaffolding, code generation, testing, and more, without needing to memorize all the available flags and options.

## 2. Core Features

### 2.1. Command Builder View
- **Objective**: Allow users to visually build a \`pdd\` command.
- **Components**:
  - A tabbed interface to select the command type (\`scaffold\`, \`gen\`, \`review\`, \`commit\`, \`test\`).
  - A dynamic form that displays the relevant options for the selected command.
  - Input fields for each option with clear descriptions and placeholders.
  - A real-time display of the generated command string.
  - A "Copy" button to easily copy the command to the clipboard.

### 2.2. Dependency Graph View
- **Objective**: Visualize the relationships between different development prompts (\`*.prompt\` files).
- **Components**:
  - A node-based graph where each node represents a prompt file.
  - Edges (arrows) connecting nodes to represent \`# Imports\` dependencies.
  - Nodes should be clickable to view the content of the prompt (the "DevUnit").
  - A modal view to display the DevUnit, separated into tabs for Prompt, Code, Example, and Test.
  - The layout should automatically arrange nodes in a hierarchical manner.

## 3. Non-Functional Requirements
- **UI/UX**: The interface should be clean, modern, and intuitive, using a dark theme.
- **Responsiveness**: The application should be usable on a variety of screen sizes, particularly standard desktop resolutions.
- **Performance**: The graph rendering should be smooth, even with a moderate number of nodes.

`.trim();