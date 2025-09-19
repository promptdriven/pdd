#!/usr/bin/env python3
"""
100% confirmation test to identify the exact issue.
This will capture and analyze the EXACT API calls and responses.
"""

import asyncio
import json
import os
import shutil
from pathlib import Path

from edit_file_tool.core import edit_file
from edit_file_tool import claude_api

# Global capture variables
captured_calls = []
original_call_claude_api = None

async def debug_call_claude_api(*args, **kwargs):
    """Wrapper that captures exact API calls and responses."""
    global captured_calls, original_call_claude_api
    
    print(f"\n🔍 API CALL #{len(captured_calls) + 1}")
    print(f"   Model: {kwargs.get('model', 'unknown')}")
    print(f"   Messages count: {len(kwargs.get('messages', []))}")
    print(f"   Use cache: {kwargs.get('use_cache', 'unknown')}")
    
    try:
        # Call the original function
        result = await original_call_claude_api(*args, **kwargs)
        response, cost_info = result
        
        # Capture the call details
        call_data = {
            "call_number": len(captured_calls) + 1,
            "kwargs": {
                "model": kwargs.get('model'),
                "messages": kwargs.get('messages'),
                "system_prompt": kwargs.get('system_prompt'),
                "use_cache": kwargs.get('use_cache'),
            },
            "response": {
                "role": response.role,
                "content": [{"type": getattr(block, 'type', 'unknown'), 
                           "text": getattr(block, 'text', None)[:200] if hasattr(block, 'text') else None,
                           "name": getattr(block, 'name', None),
                           "id": getattr(block, 'id', None)} for block in response.content],
                "stop_reason": response.stop_reason,
            },
            "cost_info": cost_info,
            "success": True,
            "error": None
        }
        
        captured_calls.append(call_data)
        
        print(f"   ✅ Success: {response.stop_reason}")
        print(f"   Content blocks: {len(response.content)}")
        for i, block in enumerate(response.content):
            print(f"      Block {i}: {getattr(block, 'type', 'unknown')}")
            if hasattr(block, 'name'):
                print(f"         Tool: {block.name}")
        print(f"   Cost: ${cost_info['total_cost']:.4f}")
        
        return result
        
    except Exception as e:
        # Capture the error
        call_data = {
            "call_number": len(captured_calls) + 1,
            "kwargs": {
                "model": kwargs.get('model'),
                "messages": kwargs.get('messages'),
                "system_prompt": kwargs.get('system_prompt'),
                "use_cache": kwargs.get('use_cache'),
            },
            "response": None,
            "cost_info": None,
            "success": False,
            "error": str(e)
        }
        
        captured_calls.append(call_data)
        
        print(f"   ❌ Error: {e}")
        raise

def enable_debug_capture():
    """Enable API call capture."""
    global original_call_claude_api
    if original_call_claude_api is None:
        original_call_claude_api = claude_api.call_claude_api
        claude_api.call_claude_api = debug_call_claude_api

def disable_debug_capture():
    """Disable API call capture."""
    global original_call_claude_api
    if original_call_claude_api is not None:
        claude_api.call_claude_api = original_call_claude_api
        original_call_claude_api = None

def save_debug_data(filename: str):
    """Save captured data to file."""
    with open(filename, 'w') as f:
        json.dump(captured_calls, f, indent=2, default=str)

async def test_specific_model(model_name: str, test_file: str, temp_file: str):
    """Test specific model with detailed capture."""
    global captured_calls
    captured_calls = []
    
    print(f"\n{'='*60}")
    print(f"🧪 TESTING MODEL: {model_name}")
    print(f"{'='*60}")
    
    # Create temp file
    shutil.copy2(test_file, temp_file)
    
    enable_debug_capture()
    
    try:
        success, message, total_cost = await edit_file(
            file_path=temp_file,
            edit_instructions="Change the function name 'add' to 'sum_numbers' throughout the file.",
            model=model_name,
            use_cache=False,
            verbose=False,  # Keep quiet to see our debug output
            max_iterations=5,
        )
        
        print(f"\n📊 FINAL RESULT:")
        print(f"   Success: {success}")
        print(f"   Message: {message}")
        print(f"   Total Cost: ${total_cost:.4f}")
        print(f"   Total API Calls: {len(captured_calls)}")
        
        return {
            "model": model_name,
            "success": success,
            "message": message,
            "total_cost": total_cost,
            "api_calls": len(captured_calls),
            "captured_calls": captured_calls.copy()
        }
        
    finally:
        disable_debug_capture()

def analyze_file_changes(original_file: str, edited_file: str):
    """Check what actually changed in the file."""
    with open(original_file, 'r') as f:
        original = f.read()
    
    with open(edited_file, 'r') as f:
        edited = f.read()
    
    print(f"\n📄 FILE ANALYSIS:")
    print(f"   Original file size: {len(original)} chars")
    print(f"   Edited file size: {len(edited)} chars")
    print(f"   Files identical: {original == edited}")
    print(f"   Contains 'sum_numbers': {'sum_numbers' in edited}")
    print(f"   Contains 'def add(': {'def add(' in edited}")

async def main():
    """Run comprehensive debug test."""
    
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("❌ ANTHROPIC_API_KEY not set")
        return
    
    test_file = "test_example.py"
    if not Path(test_file).exists():
        print(f"❌ Test file {test_file} not found")
        return
    
    print("🚀 STARTING 100% CONFIRMATION TEST")
    print("This will capture EXACT API calls and responses")
    
    # Test Claude 3.5 (working model)
    claude_35_file = "debug_35_temp.py"
    result_35 = await test_specific_model("claude-3-5-sonnet-20240620", test_file, claude_35_file)
    analyze_file_changes(test_file, claude_35_file)
    
    # Test Claude 3.7 (problem model)
    claude_37_file = "debug_37_temp.py" 
    result_37 = await test_specific_model("claude-3-7-sonnet-20250219", test_file, claude_37_file)
    analyze_file_changes(test_file, claude_37_file)
    
    # Save detailed data
    save_debug_data("debug_claude_35_calls.json")
    captured_calls = result_37["captured_calls"]
    save_debug_data("debug_claude_37_calls.json")
    
    print(f"\n{'='*60}")
    print("🎯 100% CONFIRMATION ANALYSIS")
    print(f"{'='*60}")
    
    print(f"\n🔵 Claude 3.5 Results:")
    print(f"   Success: {result_35['success']}")
    print(f"   API Calls: {result_35['api_calls']}")
    print(f"   Cost: ${result_35['total_cost']:.4f}")
    
    print(f"\n🔴 Claude 3.7 Results:")
    print(f"   Success: {result_37['success']}")
    print(f"   API Calls: {result_37['api_calls']}")
    print(f"   Cost: ${result_37['total_cost']:.4f}")
    
    # 100% confirmation logic
    if result_35['success'] and not result_37['success']:
        print(f"\n✅ 100% CONFIRMED: Claude 3.7 model is broken, Claude 3.5 works")
        print(f"   Root cause: Model-specific tool compatibility issue")
    elif result_37['success'] and not result_35['success']:
        print(f"\n🤔 UNEXPECTED: Claude 3.7 works, Claude 3.5 broken")
    elif result_35['success'] and result_37['success']:
        if result_35['api_calls'] != result_37['api_calls']:
            print(f"\n⚠️  Both work but different behavior:")
            print(f"   Claude 3.5: {result_35['api_calls']} calls")
            print(f"   Claude 3.7: {result_37['api_calls']} calls")
        else:
            print(f"\n✅ Both models work identically - issue is elsewhere")
    else:
        print(f"\n❌ Both models fail - deeper issue")
    
    print(f"\n📁 Debug files created:")
    print(f"   debug_claude_35_calls.json")
    print(f"   debug_claude_37_calls.json")
    print(f"   {claude_35_file}")
    print(f"   {claude_37_file}")

if __name__ == "__main__":
    asyncio.run(main())