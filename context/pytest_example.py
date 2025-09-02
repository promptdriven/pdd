import pytest
import io
import sys
import os

class TestResultCollector:
    def __init__(self):
        self.failures = 0
        self.errors = 0
        self.warnings = 0
        self.logs = io.StringIO()  # Capture logs in memory

    def pytest_runtest_logreport(self, report):
        """Capture test failures and errors"""
        if report.when == "call":
            if report.failed:
                self.failures += 1
            elif report.outcome == "error":
                self.errors += 1
        if report.when == "setup" and report.failed:
            self.errors += 1
        if report.when == "teardown" and report.failed:
            self.errors += 1

    def pytest_sessionfinish(self, session):
        """Capture warnings from pytest session"""
        terminal_reporter = session.config.pluginmanager.get_plugin("terminalreporter")
        if terminal_reporter:
            self.warnings = len(terminal_reporter.stats.get("warnings", []))

    def capture_logs(self):
        """Redirect stdout and stderr to capture logs"""
        sys.stdout = self.logs
        sys.stderr = self.logs

    def get_logs(self):
        """Return captured logs"""
        sys.stdout = sys.__stdout__  # Reset stdout
        sys.stderr = sys.__stderr__  # Reset stderr
        return self.logs.getvalue()

def run_pytest():
    print("Starting run_pytest function...")
    collector = TestResultCollector()
    
    try:
        print("About to capture logs...")
        collector.capture_logs()
        
        print("About to run pytest...")
        result = pytest.main(["-v", "tests/test_get_extension.py"], plugins=[collector])
        
    finally:
        print("Resetting stdout/stderr...")
        logs = collector.get_logs()

    print(f"Pytest return code: {result}")
    print(f"Captured Logs:\n{logs}")
    
    return collector.failures, collector.errors, collector.warnings, logs

if __name__ == "__main__":
    print(f"Current working directory: {os.getcwd()}")  # Add at start of __main__
    print("Starting main...")  # Debug print
    print("Running pytest...")
    failures, errors, warnings, logs = run_pytest()
    print("After run_pytest()...")  # Debug print
    print(f"Failures: {failures}")
    print(f"Errors: {errors}")
    print(f"Warnings: {warnings}")
    print("Captured Logs:\n", logs)