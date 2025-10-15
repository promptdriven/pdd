#!/usr/bin/env python3
"""
Example usage of render_mermaid.py to visualize architecture.json files.

This example demonstrates how to use the render_mermaid module to convert
architecture.json files into interactive HTML Mermaid diagrams.
"""

import json
import sys
import os
from pathlib import Path

# Import the render_mermaid functions
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from render_mermaid import generate_mermaid_code, generate_html


def create_sample_architecture():
    """Create a sample architecture.json for demonstration purposes."""
    return [
        {
            "reason": "Main application entry point",
            "description": "FastAPI application with main routes and middleware",
            "dependencies": ["config", "database"],
            "priority": 1,
            "filename": "main.py",
            "filepath": "src/main.py",
            "tags": ["backend", "api", "fastapi"]
        },
        {
            "reason": "Database configuration and models",
            "description": "SQLAlchemy models and database connection setup",
            "dependencies": [],
            "priority": 2,
            "filename": "database.py",
            "filepath": "src/database.py", 
            "tags": ["backend", "database", "sqlalchemy"]
        },
        {
            "reason": "Application configuration",
            "description": "Environment variables and app settings",
            "dependencies": [],
            "priority": 3,
            "filename": "config.py",
            "filepath": "src/config.py",
            "tags": ["backend", "config"]
        },
        {
            "reason": "React frontend components",
            "description": "Main React application with routing and state management",
            "dependencies": ["api"],
            "priority": 1,
            "filename": "App.tsx",
            "filepath": "src/components/App.tsx",
            "tags": ["frontend", "react", "ui", "component"]
        },
        {
            "reason": "API client for backend communication",
            "description": "Axios-based API client with error handling",
            "dependencies": [],
            "priority": 2,
            "filename": "api.ts",
            "filepath": "src/api.ts",
            "tags": ["frontend", "api"]
        }
    ]


def example_basic_usage():
    """Example 1: Basic usage with command line arguments."""
    print("=== Example 1: Basic Usage ===")
    print("Command line usage:")
    print("python render_mermaid.py architecture.json 'My App' output.html")
    print()


def example_programmatic_usage():
    """Example 2: Programmatic usage with the module functions."""
    print("=== Example 2: Programmatic Usage ===")
    
    # Create sample architecture
    architecture = create_sample_architecture()
    app_name = "Sample Application"
    
    # Generate Mermaid code
    mermaid_code = generate_mermaid_code(architecture, app_name)
    print("Generated Mermaid code:")
    print(mermaid_code[:200] + "..." if len(mermaid_code) > 200 else mermaid_code)
    print()
    
    # Generate HTML
    html = generate_html(mermaid_code, architecture, app_name)
    
    # Save to file
    output_file = "sample_architecture_diagram.html"
    with open(output_file, 'w') as f:
        f.write(html)
    
    print(f"✅ Generated: {output_file}")
    print(f"📊 Modules: {len(architecture)}")
    print(f"🌐 Open {output_file} in your browser!")
    print()


def example_with_real_architecture_file():
    """Example 3: Using an existing architecture.json file."""
    print("=== Example 3: Using Existing Architecture File ===")
    
    # Look for architecture.json files in common locations
    possible_files = [
        "architecture.json",
        "examples/tictactoe/tictactoe_architecture.json",
        "examples/arch/architecture.json"
    ]
    
    architecture_file = None
    for file_path in possible_files:
        if Path(file_path).exists():
            architecture_file = file_path
            break
    
    if not architecture_file:
        print("No architecture.json file found. Create one first using:")
        print("pdd generate pdd/templates/architecture/architecture_json.prompt -e PRD_FILE=your_prd.md -e APP_NAME='Your App' --output architecture.json")
        return
    
    print(f"Using architecture file: {architecture_file}")
    
    # Load and process
    with open(architecture_file) as f:
        architecture = json.load(f)
    
    app_name = Path(architecture_file).stem.replace('_architecture', '').title()
    mermaid_code = generate_mermaid_code(architecture, app_name)
    html = generate_html(mermaid_code, architecture, app_name)
    
    output_file = f"{app_name.lower()}_diagram.html"
    with open(output_file, 'w') as f:
        f.write(html)
    
    print(f"✅ Generated: {output_file}")
    print(f"📊 Modules: {len(architecture)}")
    print(f"🌐 Open {output_file} in your browser!")
    print()


def example_customization():
    """Example 4: Customizing the diagram appearance."""
    print("=== Example 4: Customization ===")
    print("The render_mermaid module supports:")
    print("- Automatic module categorization (Frontend/Backend/Shared)")
    print("- Priority indicators in module labels")
    print("- Dependency arrows with 'uses' labels")
    print("- Color-coded subgraphs")
    print("- Interactive hover tooltips")
    print("- Responsive HTML output")
    print()


def main():
    """Main function demonstrating various usage patterns."""
    print("render_mermaid.py Usage Examples")
    print("=" * 40)
    print()
    
    example_basic_usage()
    example_programmatic_usage()
    example_with_real_architecture_file()
    example_customization()
    
    print("For more information, see the render_mermaid.py documentation.")


if __name__ == "__main__":
    main()
