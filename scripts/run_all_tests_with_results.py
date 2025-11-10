#!/usr/bin/env python3
"""
Run all PDD test suites and capture results for GitHub PR comments.
This script runs unit tests, regression tests, and sync regression tests,
capturing pass/fail counts and reasons for failures.
"""

import os
import sys
import subprocess
import json
import re
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Tuple, Union


class TestRunner:
    """Orchestrates test execution and result collection."""
    
    def __init__(self, project_root: Path, pr_number: str = None, pr_url: str = None):
        self.project_root = project_root
        self.pr_number = pr_number
        self.pr_url = pr_url
        self.base_env = os.environ.copy()
        self.base_env.setdefault("SKIP_MAKEFILE_REGEN", "1")
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "pr_number": pr_number,
            "pr_url": pr_url,
            "test_suites": {},
            "summary": {
                "total_passed": 0,
                "total_failed": 0,
                "total_skipped": 0,
                "duration_seconds": 0
            }
        }

    def _build_infisical_command(self, base_command: List[str]) -> List[str]:
        """Wrap a shell command with Infisical so secrets are available."""
        cmd = ["infisical", "run"]
        token = os.getenv("INFISICAL_TOKEN")
        if token:
            cmd.extend(["--token", token])
        cmd.append("--")
        cmd.extend(base_command)
        return cmd
        
    def run_unit_tests(self) -> Dict:
        """Run pytest unit tests and capture results."""
        print("=" * 60)
        print("Running Unit Tests (pytest)")
        print("=" * 60)
        
        start_time = datetime.now()
        
        cmd = self._build_infisical_command(["make", "test"])
        log_path = self.project_root / "test_results" / "unit_tests.log"
        
        log_path.parent.mkdir(exist_ok=True)
        with log_path.open("w") as log_file:
            start_msg = f"[{start_time:%H:%M:%S}] [unit_tests] starting…"
            print(start_msg, flush=True)
            print(start_msg, file=log_file, flush=True)
            result = subprocess.run(
                cmd,
                cwd=self.project_root,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                text=True,
                env=self.base_env
            )
            end_msg = f"[{datetime.now():%H:%M:%S}] [unit_tests] finished (rc={result.returncode})"
            print(end_msg, flush=True)
            print(end_msg, file=log_file, flush=True)
        log_contents = log_path.read_text()
        log_output = log_contents[-5000:]
        
        duration = (datetime.now() - start_time).total_seconds()
        
        # Parse pytest output
        passed, failed, skipped, failures = self._parse_pytest_output(log_contents)
        
        test_result = {
            "name": "Unit Tests (pytest)",
            "command": " ".join(cmd),
            "exit_code": result.returncode,
            "passed": passed,
            "failed": failed,
            "skipped": skipped,
            "duration_seconds": duration,
            "failures": failures,
            "stdout": log_output,
            "stderr": ""
        }
        
        self.results["test_suites"]["unit_tests"] = test_result
        return test_result
        
    def run_regression_tests(self) -> Dict:
        """Run regression tests and capture results."""
        print("\n" + "=" * 60)
        print("Running Regression Tests")
        print("=" * 60)
        
        start_time = datetime.now()
        
        cmd = self._build_infisical_command(["make", "regression"])
        log_path = self.project_root / "test_results" / "regression_tests.log"
        
        log_path.parent.mkdir(exist_ok=True)
        with log_path.open("w") as log_file:
            start_msg = f"[{start_time:%H:%M:%S}] [regression_tests] starting…"
            print(start_msg, flush=True)
            print(start_msg, file=log_file, flush=True)
            result = subprocess.run(
                cmd,
                cwd=self.project_root,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                text=True,
                env=self.base_env
            )
            end_msg = f"[{datetime.now():%H:%M:%S}] [regression_tests] finished (rc={result.returncode})"
            print(end_msg, flush=True)
            print(end_msg, file=log_file, flush=True)
        log_contents = log_path.read_text()
        log_output = log_contents[-5000:]
        
        duration = (datetime.now() - start_time).total_seconds()
        
        # Parse regression script output; include underlying regression log if available
        log_paths = [log_path]
        additional_logs = self._extract_log_paths(log_contents, keyword="Log file:")
        log_paths.extend(additional_logs)
        passed, failed, errors = self._parse_regression_output_full(log_paths)
        
        test_result = {
            "name": "Regression Tests",
            "command": " ".join(cmd),
            "exit_code": result.returncode,
            "passed": passed,
            "failed": failed,
            "errors": errors,
            "duration_seconds": duration,
            "stdout": log_output,
            "stderr": ""
        }
        
        self.results["test_suites"]["regression_tests"] = test_result
        return test_result
        
    def run_sync_regression_tests(self) -> Dict:
        """Run sync regression tests and capture results."""
        print("\n" + "=" * 60)
        print("Running Sync Regression Tests")
        print("=" * 60)
        
        start_time = datetime.now()
        start_timestamp = start_time.timestamp()
        
        cmd = self._build_infisical_command(["make", "sync-regression"])
        log_path = self.project_root / "test_results" / "sync_regression_tests.log"
        
        log_path.parent.mkdir(exist_ok=True)
        with log_path.open("w") as log_file:
            start_msg = f"[{start_time:%H:%M:%S}] [sync_regression_tests] starting…"
            print(start_msg, flush=True)
            print(start_msg, file=log_file, flush=True)
            result = subprocess.run(
                cmd,
                cwd=self.project_root,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                text=True,
                env=self.base_env
            )
            end_msg = f"[{datetime.now():%H:%M:%S}] [sync_regression_tests] finished (rc={result.returncode})"
            print(end_msg, flush=True)
            print(end_msg, file=log_file, flush=True)
        log_contents = log_path.read_text()
        log_output = log_contents[-5000:]
        
        duration = (datetime.now() - start_time).total_seconds()
        
        # Parse sync regression output; include per-case logs when running in parallel
        log_paths = [log_path]
        parallel_log_dir = log_path.parent / "sync_parallel_logs"
        if parallel_log_dir.exists():
            case_logs = []
            for path in sorted(parallel_log_dir.glob("case_*.log")):
                if not path.is_file():
                    continue
                try:
                    if path.stat().st_mtime >= start_timestamp:
                        case_logs.append(path)
                except FileNotFoundError:
                    continue
            log_paths.extend(case_logs)
        
        base_passed, base_failed, base_errors = self._parse_regression_output_full(log_paths)
        case_summary = self._parse_sync_parallel_summary(log_contents)
        if case_summary:
            case_passed, case_failed, case_errors = case_summary
            passed, failed = case_passed, case_failed
            errors = self._combine_errors(case_errors, base_errors)
        else:
            passed, failed, errors = base_passed, base_failed, base_errors
        
        test_result = {
            "name": "Sync Regression Tests",
            "command": " ".join(cmd),
            "exit_code": result.returncode,
            "passed": passed,
            "failed": failed,
            "errors": errors,
            "duration_seconds": duration,
            "stdout": log_output,
            "stderr": ""
        }
        
        self.results["test_suites"]["sync_regression_tests"] = test_result
        return test_result
        
    def _parse_pytest_output(self, output: str) -> Tuple[int, int, int, List[Dict]]:
        """Parse pytest output to extract test counts and failures."""
        passed = 0
        failed = 0
        skipped = 0
        failures = []
        
        # Look for pytest summary line like "5 passed, 2 failed, 1 skipped in 10.5s"
        summary_pattern = r'(\d+)\s+passed'
        if match := re.search(summary_pattern, output):
            passed = int(match.group(1))
            
        fail_pattern = r'(\d+)\s+failed'
        if match := re.search(fail_pattern, output):
            failed = int(match.group(1))
            
        skip_pattern = r'(\d+)\s+skipped'
        if match := re.search(skip_pattern, output):
            skipped = int(match.group(1))
            
        # Extract failure details with more comprehensive patterns
        # Pattern 1: FAILED test_file.py::test_name - error
        failure_sections = re.findall(
            r'FAILED\s+([\w/]+\.py::[\w_\[\]]+)(?:\s+-\s+(.+?))?(?=FAILED|\n\n|$)',
            output,
            re.DOTALL
        )
        
        for test_name, error_msg in failure_sections:
            # Extract test number if present in test name (e.g., test_regression[5])
            test_num_match = re.search(r'\[(\d+)\]', test_name)
            test_number = test_num_match.group(1) if test_num_match else None
            
            failure_info = {
                "test": test_name.strip(),
                "test_number": test_number,
                "error": error_msg.strip()[:500] if error_msg else "No error message captured"
            }
            failures.append(failure_info)
        
        # Also look for FAILED lines in verbose output (test_file.py::test_name FAILED)
        if not failures:
            verbose_failures = re.findall(
                r'([\w/]+\.py::[\w_\[\]]+)\s+FAILED',
                output
            )
            for test_name in verbose_failures:
                test_num_match = re.search(r'\[(\d+)\]', test_name)
                test_number = test_num_match.group(1) if test_num_match else None
                
                failures.append({
                    "test": test_name.strip(),
                    "test_number": test_number,
                    "error": "Failed (see logs for details)"
                })
            
        return passed, failed, skipped, failures
        
    def _parse_regression_output_full(self, log_paths: Union[Path, List[Path]]) -> Tuple[int, int, List[str]]:
        """Parse regression test output to extract results."""
        if isinstance(log_paths, Path):
            paths = [log_paths]
        else:
            paths = list(log_paths)
        
        combined_text = ""
        for path in paths:
            if path.exists():
                combined_text += path.read_text()
        
        passed = combined_text.count("Validation success:")
        failed = combined_text.count("Validation failed:")
        errors = []
        
        for match in re.findall(r'\[ERROR\]\s+(.*)', combined_text):
            errors.append(match.strip())
            if len(errors) >= 20:
                break
        
        return passed, failed, errors

    def _parse_sync_parallel_summary(self, log_text: str):
        """Parse sync-regression parallel launcher output for per-case results."""
        success_matches = re.findall(r'\[sync-regression\]\s+Case\s+(\d+)\s+completed successfully', log_text)
        failure_matches = re.findall(r'\[sync-regression\]\s+Case\s+(\d+)\s+failed \(exit\s+([^)]+)\)', log_text)
        
        if not success_matches and not failure_matches:
            return None
        
        def unique(items):
            seen = set()
            ordered = []
            for item in items:
                if item not in seen:
                    seen.add(item)
                    ordered.append(item)
            return ordered
        
        success_cases = unique(success_matches)
        failure_cases = unique(failure_matches)
        
        case_errors = [f"Case {case} failed (exit {code})" for case, code in failure_cases]
        return len(success_cases), len(failure_cases), case_errors

    def _combine_errors(self, *error_lists: List[str]) -> List[str]:
        """Merge multiple error lists while preserving order and limiting duplicates."""
        merged: List[str] = []
        seen = set()
        for errors in error_lists:
            for error in errors:
                if not error or error in seen:
                    continue
                merged.append(error)
                seen.add(error)
                if len(merged) >= 20:
                    return merged
        return merged

    def _extract_log_paths(self, text: str, keyword: str) -> List[Path]:
        """Extract filesystem paths from log output that match the given keyword."""
        paths: List[Path] = []
        seen = set()
        pattern = rf'{re.escape(keyword)}\s*(.+)'
        for match in re.findall(pattern, text, flags=re.IGNORECASE):
            candidate = match.strip()
            if not candidate:
                continue
            # Take the first whitespace-separated token to avoid trailing messages
            candidate = candidate.split()[0]
            path = Path(candidate)
            if not path.is_absolute():
                path = (self.project_root / path).resolve()
            else:
                path = path.resolve()
            if path.exists() and str(path) not in seen:
                seen.add(str(path))
                paths.append(path)
        return paths

    def run_all_suites(self):
        """Run all suites concurrently to reduce total runtime."""
        suites = [
            ("unit_tests", self.run_unit_tests),
            ("regression_tests", self.run_regression_tests),
            ("sync_regression_tests", self.run_sync_regression_tests),
        ]
        with ThreadPoolExecutor(max_workers=len(suites)) as executor:
            future_map = {executor.submit(func): name for name, func in suites}
            for future in as_completed(future_map):
                suite_name = future_map[future]
                try:
                    future.result()
                except Exception as exc:
                    print(f"ERROR: Failed running {suite_name}: {exc}")
        
    def calculate_summary(self):
        """Calculate overall test summary."""
        total_passed = 0
        total_failed = 0
        total_skipped = 0
        total_duration = 0
        
        for suite_name, suite_data in self.results["test_suites"].items():
            total_passed += suite_data.get("passed", 0)
            total_failed += suite_data.get("failed", 0)
            total_skipped += suite_data.get("skipped", 0)
            total_duration += suite_data.get("duration_seconds", 0)
            
        self.results["summary"] = {
            "total_passed": total_passed,
            "total_failed": total_failed,
            "total_skipped": total_skipped,
            "duration_seconds": total_duration,
            "all_passed": total_failed == 0
        }
        
    def generate_github_comment(self) -> str:
        """Generate a formatted GitHub comment from test results."""
        summary = self.results["summary"]
        
        # Determine overall status
        status = "PASS" if summary["all_passed"] else "FAIL"
        
        comment = f"""## Test Results - {status}
"""
        
        # Add PR link if available
        if self.pr_url:
            comment += f"\n**Pull Request:** {self.pr_url}\n"
        elif self.pr_number:
            # Construct URL from PR number (assumes GitHub)
            comment += f"\n**Pull Request:** #{self.pr_number}\n"
        
        comment += f"""
**Overall Summary:**
- Passed: {summary['total_passed']}
- Failed: {summary['total_failed']}
- Skipped: {summary['total_skipped']}
- Duration: {summary['duration_seconds']:.1f}s
"""
        
        # Collect all failed test numbers across all suites
        all_failed_test_numbers = []
        for suite_name, suite_data in self.results["test_suites"].items():
            if "failures" in suite_data and suite_data["failures"]:
                for failure in suite_data["failures"]:
                    if failure.get("test_number"):
                        all_failed_test_numbers.append(failure["test_number"])
        
        # Show failed test numbers prominently if any exist
        if all_failed_test_numbers:
            comment += f"\n**FAILED TEST NUMBERS:** {', '.join(sorted(set(all_failed_test_numbers)))}\n"
        
        comment += "\n---\n\n"
        
        log_snippets = []

        # Add details for each test suite
        for suite_name, suite_data in self.results["test_suites"].items():
            suite_status = "PASS" if suite_data["exit_code"] == 0 else "FAIL"
            
            comment += f"""### {suite_data['name']} - {suite_status}

**Results:**
- Passed: {suite_data.get('passed', 0)}
- Failed: {suite_data.get('failed', 0)}
"""
            
            if suite_data.get("skipped"):
                comment += f"- Skipped: {suite_data['skipped']}\n"
                
            comment += f"- Duration: {suite_data['duration_seconds']:.1f}s\n"
            
            # Add failure details for unit tests
            if "failures" in suite_data and suite_data["failures"]:
                comment += "\n**Failed Tests:**\n"
                
                # Group by test number if available
                numbered_failures = [f for f in suite_data["failures"] if f.get("test_number")]
                unnumbered_failures = [f for f in suite_data["failures"] if not f.get("test_number")]
                
                if numbered_failures:
                    test_numbers = [f["test_number"] for f in numbered_failures]
                    comment += f"\n**Failed Test Numbers:** {', '.join(test_numbers)}\n\n"
                
                # Show details (limit to 10)
                for failure in suite_data["failures"][:10]:
                    if failure.get("test_number"):
                        comment += f"- Test #{failure['test_number']}: `{failure['test']}`\n"
                    else:
                        comment += f"- `{failure['test']}`\n"
                    if failure.get('error'):
                        error_preview = failure['error'][:200].replace('\n', ' ')
                        comment += f"  ```\n  {error_preview}...\n  ```\n"
                    
            # Add error details for regression tests
            if "errors" in suite_data and suite_data["errors"]:
                comment += "\n**Errors:**\n"
                for error in suite_data["errors"][:10]:  # Limit to 10 errors
                    comment += f"- {error}\n"
                    log_snippets.append(error)
                    
            comment += "\n---\n\n"
            
            # Capture a snippet of raw log output for detail view
            if suite_data.get("stdout"):
                snippet = suite_data["stdout"][-3000:]
                log_snippets.append(f"### {suite_data['name']}\n```\n{snippet}\n```")
        
        log_details = "\n\n".join(log_snippets) if log_snippets else "No additional log output captured."

        comment += f"""
<details>
<summary>View Full Logs</summary>

Test run completed at: {self.results['timestamp']}

{log_details}

</details>
"""
        
        return comment
        
    def save_results(self, output_file: Path):
        """Save detailed results to JSON file."""
        with open(output_file, 'w') as f:
            json.dump(self.results, f, indent=2)
        print(f"\nDetailed results saved to: {output_file}")
        
    def save_github_comment(self, output_file: Path):
        """Save GitHub comment to file."""
        comment = self.generate_github_comment()
        with open(output_file, 'w') as f:
            f.write(comment)
        print(f"GitHub comment saved to: {output_file}")


def main():
    """Main entry point for test runner."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Run all PDD test suites and capture results')
    parser.add_argument('--pr-number', type=str, help='GitHub PR number')
    parser.add_argument('--pr-url', type=str, help='GitHub PR URL')
    args = parser.parse_args()
    
    project_root = Path(__file__).parent.parent
    
    # Initialize runner with PR information
    runner = TestRunner(project_root, pr_number=args.pr_number, pr_url=args.pr_url)
    
    # Run all test suites (in parallel)
    runner.run_all_suites()
        
    # Calculate summary
    runner.calculate_summary()
    
    # Save results
    output_dir = project_root / "test_results"
    output_dir.mkdir(exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    runner.save_results(output_dir / f"test_results_{timestamp}.json")
    runner.save_github_comment(output_dir / f"github_comment_{timestamp}.md")
    
    # Also save latest results
    runner.save_results(output_dir / "latest_results.json")
    runner.save_github_comment(output_dir / "latest_comment.md")
    
    # Print summary
    print("\n" + "=" * 60)
    print("TEST RUN COMPLETE")
    print("=" * 60)
    print(f"Total Passed: {runner.results['summary']['total_passed']}")
    print(f"Total Failed: {runner.results['summary']['total_failed']}")
    print(f"Total Skipped: {runner.results['summary']['total_skipped']}")
    print(f"Duration: {runner.results['summary']['duration_seconds']:.1f}s")
    
    # Show failed test numbers if any
    failed_test_numbers = []
    for suite_name, suite_data in runner.results["test_suites"].items():
        if "failures" in suite_data and suite_data["failures"]:
            for failure in suite_data["failures"]:
                if failure.get("test_number"):
                    failed_test_numbers.append(failure["test_number"])
    
    if failed_test_numbers:
        print("\n" + "=" * 60)
        print("FAILED TEST NUMBERS")
        print("=" * 60)
        print(f"Test Numbers: {', '.join(sorted(set(failed_test_numbers)))}")
        print("\nTo rerun specific tests:")
        for num in sorted(set(failed_test_numbers)):
            print(f"  make regression TEST_NUM={num}")
    
    # Exit with appropriate code
    sys.exit(0 if runner.results['summary']['all_passed'] else 1)


if __name__ == "__main__":
    main()
