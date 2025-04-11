from pdd_mcp_server.tools.definitions import (
    PDD_GENERATE, PDD_TEST, PDD_FIX, PDD_EXAMPLE, 
    PDD_CONTINUE, PDD_ANALYZE, PDD_TOOLS, get_tool_by_name
)

def demonstrate_pdd_tools():
    """
    Demonstrates the usage of various tools defined in the PDD module.
    
    This function shows how to access different tools, examine their schemas,
    and prepare parameters for tool invocation.
    """
    # 1. Basic tool usage - Generate code from a prompt file
    print(f"Using tool: {PDD_GENERATE.name}")
    generate_params = {
        "prompt_file": "calculator.prompt",
        "output": "calculator.py",
        "strength": 0.7,
        "temperature": 0.2,
        "local": False,
        "force": True,
        "verbose": True
    }
    
    print(f"Invoking {PDD_GENERATE.name} with parameters: {generate_params}")
    # client.invoke_tool(PDD_GENERATE.name, generate_params)
    
    # 2. Generate tests for a source file
    test_params = {
        "source_file": "calculator.py",
        "prompt_file": "calculator_test.prompt",  # Optional
        "output": "test_calculator.py",
        "strength": 0.6
    }
    print(f"\nInvoking {PDD_TEST.name} with parameters: {test_params}")
    # client.invoke_tool(PDD_TEST.name, test_params)
    
    # 3. Fix issues in a source file
    fix_params = {
        "prompt_file": "calculator_fix.prompt",
        "source_file": "calculator.py",
        "test_file": "test_calculator.py",
        "loop": True,
        "max_attempts": 3,
        "force": True
    }
    print(f"\nInvoking {PDD_FIX.name} with parameters: {fix_params}")
    # client.invoke_tool(PDD_FIX.name, fix_params)
    
    # 4. Generate example usage of a module
    example_params = {
        "source_file": "calculator.py",
        "output": "calculator_example.py",
        "strength": 0.8,
        "local": True
    }
    print(f"\nInvoking {PDD_EXAMPLE.name} with parameters: {example_params}")
    # client.invoke_tool(PDD_EXAMPLE.name, example_params)
    
    # 5. Analyze code for insights
    analyze_params = {
        "source_file": "calculator.py",
        "output": "calculator_analysis.md",
        "format": "markdown",
        "strength": 0.9
    }
    print(f"\nInvoking {PDD_ANALYZE.name} with parameters: {analyze_params}")
    # client.invoke_tool(PDD_ANALYZE.name, analyze_params)
    
    # 6. Continue generation of partially completed output
    continue_params = {
        "prompt_file": "calculator.prompt",
        "output_file": "calculator_partial.py",
        "result_file": "calculator_complete.py",
        "temperature": 0.1
    }
    print(f"\nInvoking {PDD_CONTINUE.name} with parameters: {continue_params}")
    # client.invoke_tool(PDD_CONTINUE.name, continue_params)
    
    # 7. Get tool by name and inspect its schema
    tool = get_tool_by_name("pdd-generate")
    print(f"\nTool name: {tool.name}")
    print(f"Tool description: {tool.description}")
    print(f"Required parameters: {tool.inputSchema['required']}")
    
    # 8. List all available tools
    print("\nAll available tools:")
    for tool in PDD_TOOLS:
        print(f" - {tool.name}: {tool.description}")

if __name__ == "__main__":
    demonstrate_pdd_tools()