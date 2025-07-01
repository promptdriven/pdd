# PDD Tutorials

This document provides step-by-step tutorials for common tasks in the PDD workflow.

## How to Create a New Test Case

1) Ensure that all existing test cases pass in your PDD repo. If they do not all pass, that could be the root cause of your issues.
2) Once you have ensured that all other test cases have passed, figure out which module/compoenet of PDD you want to add the test case to. PDD's tests are situated in a specific format. In the "tests" directory, each test file correpsonds to an corresponding module file located in the pdd directory. Figure out which module of PDD you want to create the test case of. You can use external tools such as Cursor or other agentic agents to help you determine where to create the test cases.
    Example: If I wanted to create a test case that tested verify working across several loops, I would create a new test case in test_fix_error_loop.py rather than test_fix_verification_errors.py or test_fix_verificaiton_main.py
3) TO BE CONTINUED