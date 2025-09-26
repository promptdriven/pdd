# Development Prompts Collection

This document contains all the prompts used during the development of the enhanced PDD example command functionality. These prompts can be used to replicate similar improvements in the future.

## 🎯 **Optimized Primary Development Prompts**

### **1. Branch Creation with Specific Issue Reference**
```
Create a new branch named 'fix/enhance-pdd-example-imports' for GitHub issue #52 and #64. The issue involves fixing incorrect import statements in generated examples and adding default output path to examples/ directory.
```

### **2. Fresh Development Start**
```
Reset to main branch and create a completely new branch 'fix/pdd-example-import-fix' to start fresh development for the import statement issue in pdd example command.
```

### **3. Specific Issue Analysis with Technical Details**
```
Analyze and fix this specific issue: The pdd example command generates incorrect import statements causing ModuleNotFoundError. 

PROBLEM: Generated examples use wrong module names (e.g., 'from greeting_module import hello' instead of 'from hello import hello')

REQUIREMENTS:
- Fix import statements to use correct module names
- Add file path information to LLM prompt for better context
- Change default output path from current directory to examples/ directory
- Ensure solution works for all programming languages, not just Python
- Maintain backward compatibility with existing functionality

TECHNICAL CONTEXT:
- Issue #52: Enhance pdd example with richer sections + default output path
- Issue #64: Documentation for pdd example command
- Current behavior: Examples go to current working directory by default
- Desired behavior: Examples go to examples/ directory by default
- Import problem: LLM generates incorrect module names in import statements

IMPLEMENTATION APPROACH:
- Modify pdd/prompts/example_generator_LLM.prompt to include file path context
- Update pdd/context_generator.py to pass source_file_path, example_file_path, module_name
- Update pdd/generate_output_paths.py to default examples to examples/ directory
- Ensure language independence for Python, JavaScript, C++, Java, etc.
```

### **4. API Configuration with Specific Model**
```
Set GEMINI_API_KEY="AIzaSyBb9VqwWVKSUNTBzJWGAeAklYmZgq_5QMI" for testing the enhanced pdd example command with Gemini 2.5 Pro model.
```

### **5. Functionality Verification with Specific Test**
```
Test if the pdd example command was working correctly before implementing the import fix changes. Run: pdd example examples/hello/hello_python.prompt examples/hello/pdd/hello.py and verify the generated example executes without ModuleNotFoundError.
```

### **6. Cleanup with Specific File Types**
```
Remove all firecrawl-related database files and cache directories from the project. Look for files with 'firecrawl' in the name and delete cache/ directories that contain .db files.
```

### **7. Language Independence with Specific Implementation**
```
Modify the prompt template to be truly language independent. Remove Python-specific import syntax examples and replace with language-agnostic instructions that work for Python, JavaScript, C++, Java, and other programming languages. The LLM should generate appropriate import syntax based on the detected language.
```

### **8. Comprehensive Testing with Specific Test Suites**
```
Run comprehensive testing across all test suites:
1. tests/test_enhanced_example_command.py (10 tests)
2. tests/test_generated_examples.py (9 tests) 
3. tests/test_context_generator.py (7 tests)
4. tests/test_generate_output_paths.py (34 tests)

Verify all 60 tests pass and test actual functionality with Python and JavaScript examples.
```

### **9. Documentation with Specific Deliverables**
```
Create comprehensive documentation including:
1. All prompts used during development session
2. Step-by-step replication guidelines
3. Technical implementation details
4. Test coverage summary
5. Language independence verification
6. Backward compatibility confirmation

Format as markdown files for future reference and replication.
```

## 🔧 **Optimized Technical Implementation Prompts**

### **Code Analysis with Specific Criteria**
```
Analyze the current implementation for language independence. Check if the prompt template and import generation logic works correctly for Python, JavaScript, C++, and Java. Verify that no language-specific assumptions are hardcoded and that the LLM can generate appropriate import syntax for each language.
```

### **Comprehensive Testing with Specific Test Cases**
```
Execute the complete test suite with these specific requirements:
- Run all 60 tests across 4 test files
- Test Python example generation with correct imports
- Test JavaScript example generation with correct imports  
- Verify examples directory default behavior
- Confirm backward compatibility with existing functionality
- Test actual execution of generated examples
```

### **Debugging with Specific Error Analysis**
```
Debug the pdd example command by testing before and after the import fix changes. Identify if the original command was generating ModuleNotFoundError due to incorrect import statements, and verify that the fix resolves this issue while maintaining all existing functionality.
```

### **Cleanup with Specific File Patterns**
```
Remove specific file types and directories:
- Delete cache/firecrawl/ directory and all .db files
- Remove any temporary test files (test_*.py, test_*.js, test_*.prompt)
- Clean up example output files in examples/ directory
- Remove any symbolic links created for testing
```

## 📋 **Optimized Development Workflow Prompts**

### **Branch Management with Specific Naming**
```
Create a new feature branch with descriptive naming:
- Branch name: 'fix/enhance-pdd-example-imports' 
- Reference issues: #52, #64
- Include specific functionality: import fix + default output path
- Ensure branch name clearly indicates the purpose
```

### **Fresh Development Start with Clean State**
```
Reset development environment for clean start:
- Switch to main branch
- Create new branch: 'fix/pdd-example-import-fix'
- Ensure no uncommitted changes carry over
- Start with minimal, focused changes
```

### **Issue Analysis with Structured Requirements**
```
Analyze issue with structured approach:
- Problem: ModuleNotFoundError in generated examples
- Root cause: Incorrect import statements in LLM output
- Requirements: Fix imports + add default output path
- Constraints: Maintain backward compatibility
- Success criteria: All tests pass, examples execute correctly
```

### **API Configuration with Specific Model**
```
Configure LLM API for testing:
- Provider: Google Gemini
- Model: gemini-2.5-pro
- API Key: [specific key for testing]
- Purpose: Test enhanced pdd example command
- Validation: Verify API key works with test commands
```

### **Quality Assurance with Specific Metrics**
```
Execute comprehensive quality assurance:
- Test coverage: 60 tests across 4 test suites
- Functionality: Python and JavaScript example generation
- Compatibility: Backward compatibility verification
- Performance: All tests must pass
- Documentation: Complete test results and summaries
```

### **Documentation with Specific Deliverables**
```
Create comprehensive documentation package:
- Development prompts collection (this file)
- Technical implementation summary
- Test coverage report
- Language independence verification
- Replication guidelines
- All documentation in markdown format
```

## 🎯 **Optimized Key Development Patterns**

### **1. Issue-First Development with Structured Analysis**
- **Problem Definition**: Clearly identify the specific issue (e.g., ModuleNotFoundError)
- **Root Cause Analysis**: Determine why the issue occurs (incorrect import statements)
- **Requirements Gathering**: List specific requirements and constraints
- **Success Criteria**: Define measurable success metrics (all tests pass, examples execute)
- **Context Documentation**: Include related issues, discussions, and technical context

### **2. Incremental Enhancement with Validation Gates**
- **Minimal Viable Changes**: Start with the smallest change that addresses the core issue
- **Validation Gates**: Test after each change to ensure functionality is preserved
- **Iterative Refinement**: Build upon working changes rather than making large modifications
- **Rollback Strategy**: Maintain ability to revert changes if issues arise
- **Feedback Integration**: Incorporate feedback from testing and validation

### **3. Language Independence with Multi-Language Testing**
- **Design Principles**: Create language-agnostic solutions that work across programming languages
- **Testing Strategy**: Test with Python, JavaScript, C++, Java, and other target languages
- **Implementation Approach**: Use language detection and appropriate syntax generation
- **Validation Process**: Verify correct import syntax for each supported language
- **Extensibility**: Design for easy addition of new language support

### **4. Comprehensive Testing with Specific Metrics**
- **Test Coverage**: Achieve 100% test coverage across all test suites
- **Functionality Testing**: Test actual execution of generated examples
- **Compatibility Testing**: Verify backward compatibility with existing functionality
- **Performance Testing**: Ensure all tests pass within acceptable time limits
- **Integration Testing**: Test end-to-end functionality with real-world scenarios

### **5. Documentation-Driven Development with Specific Deliverables**
- **Technical Documentation**: Document all code changes and their rationale
- **Test Documentation**: Create comprehensive test coverage reports
- **User Documentation**: Provide clear usage instructions and examples
- **Development Documentation**: Maintain prompts and replication guidelines
- **Quality Documentation**: Document validation results and success metrics

## 🚀 **Optimized Replication Guidelines**

### **Step-by-Step Replication Process:**

#### **Phase 1: Issue Analysis and Setup**
1. **Issue Analysis**
   - Use the "Specific Issue Analysis with Technical Details" prompt
   - Identify the core problem (ModuleNotFoundError in generated examples)
   - Define specific requirements and success criteria
   - Document technical context and constraints

2. **Development Environment Setup**
   - Use the "Fresh Development Start with Clean State" prompt
   - Create branch: 'fix/pdd-example-import-fix'
   - Configure API key using "API Configuration with Specific Model" prompt
   - Set up testing environment with all required dependencies

#### **Phase 2: Implementation**
3. **Core Functionality Implementation**
   - Modify `pdd/prompts/example_generator_LLM.prompt` to include file path context
   - Update `pdd/context_generator.py` to pass source_file_path, example_file_path, module_name
   - Update `pdd/generate_output_paths.py` to default examples to examples/ directory
   - Ensure language independence using "Language Independence with Specific Implementation" prompt

4. **Validation and Testing**
   - Use "Comprehensive Testing with Specific Test Suites" prompt
   - Run all 60 tests across 4 test files
   - Test Python and JavaScript example generation
   - Verify examples directory default behavior
   - Confirm backward compatibility

#### **Phase 3: Quality Assurance**
5. **Code Analysis and Debugging**
   - Use "Code Analysis with Specific Criteria" prompt
   - Verify language independence for Python, JavaScript, C++, Java
   - Use "Debugging with Specific Error Analysis" prompt
   - Test before and after changes to confirm fix

6. **Cleanup and Documentation**
   - Use "Cleanup with Specific File Patterns" prompt
   - Remove temporary files and cache directories
   - Use "Documentation with Specific Deliverables" prompt
   - Create comprehensive documentation package

### **Success Metrics and Validation:**
- ✅ **All 60 tests pass** across 4 test suites
- ✅ **Python examples execute** without ModuleNotFoundError
- ✅ **JavaScript examples execute** with correct import syntax
- ✅ **Examples directory default** behavior works correctly
- ✅ **Backward compatibility** maintained for existing functionality
- ✅ **Language independence** verified for multiple programming languages
- ✅ **Comprehensive documentation** created for future reference

### **Critical Success Factors:**
- **Specific Problem Focus**: Target the exact issue (incorrect import statements)
- **Minimal Change Approach**: Make only necessary changes to fix the core issue
- **Comprehensive Testing**: Test all functionality thoroughly before considering complete
- **Language Independence**: Ensure solution works for all target programming languages
- **Documentation Quality**: Create detailed documentation for future replication

## 📝 **Optimized Prompt Usage Tips**

### **For Issue Analysis:**
- **Use "Specific Issue Analysis with Technical Details" prompt**
- Include complete problem description with specific error messages
- Add technical context from GitHub issues and discussions
- Reference related issues, PRs, and commit history
- Define clear success criteria and measurable outcomes

### **For Testing and Validation:**
- **Use "Comprehensive Testing with Specific Test Suites" prompt**
- Test all functionality with specific test cases and expected outcomes
- Verify backward compatibility with existing functionality
- Ensure all test suites pass with specific metrics (60 tests across 4 files)
- Test actual execution of generated examples, not just syntax validation

### **For Documentation and Replication:**
- **Use "Documentation with Specific Deliverables" prompt**
- Document all prompts used with specific context and outcomes
- Include step-by-step development workflow with phase-based approach
- Provide detailed replication guidelines with success metrics
- Create comprehensive test coverage reports and validation summaries

### **For Language Independence:**
- **Use "Language Independence with Specific Implementation" prompt**
- Design for multi-language support with specific language examples
- Test with Python, JavaScript, C++, Java, and other target languages
- Avoid language-specific assumptions and hardcoded syntax
- Implement language detection and appropriate syntax generation

### **For Quality Assurance:**
- **Use "Code Analysis with Specific Criteria" prompt**
- Analyze implementation against specific technical requirements
- Verify language independence with concrete test cases
- Validate backward compatibility with existing functionality
- Ensure comprehensive test coverage with measurable metrics

This collection of prompts provides a complete roadmap for replicating similar development work in the future, ensuring consistent quality and comprehensive functionality.
