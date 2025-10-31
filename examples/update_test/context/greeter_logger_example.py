# context/greeter_logger_example.py

class GreeterLogger:
    def debug(self, message: str):
        """Logs a debug message."""
        print(f"DEBUG: {message}")

# --- How to use ---
# logger = GreeterLogger()
# logger.debug("This is a test log.")
