#!/usr/bin/env python
"""
Script to regenerate all test files in the output directory.
This script creates all the necessary test files that are used by the handler examples.
"""

import os
import shutil
import logging

# Set up logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("regenerate_test_files")

# Path to the output directory
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'output')

def ensure_dir(dir_path):
    """Ensure that a directory exists, creating it if necessary."""
    if not os.path.exists(dir_path):
        os.makedirs(dir_path)
        logger.info(f"Created directory: {dir_path}")
    return dir_path

def write_file(file_path, content):
    """Write content to a file, creating any necessary directories."""
    dir_path = os.path.dirname(file_path)
    if dir_path:
        ensure_dir(dir_path)
    
    with open(file_path, 'w') as f:
        f.write(content)
    logger.info(f"Created file: {file_path}")

def main():
    """Main function to regenerate all test files."""
    logger.info("Starting to regenerate test files...")
    
    # Ensure the output directory exists
    ensure_dir(OUTPUT_DIR)
    
    # Create the my_prompt.prompt file for generate command
    write_file(os.path.join(OUTPUT_DIR, "my_prompt.prompt"), """Create a simple Python function that calculates the factorial of a number recursively.

Requirements:
- Function name: factorial
- Should handle negative numbers by returning None
- Should handle 0 by returning 1
- Should use recursion for positive numbers""")
    
    # Create the api_prompt.prompt file for test and fix commands
    write_file(os.path.join(OUTPUT_DIR, "api_prompt.prompt"), """Create a simple REST API weather service with the following endpoints:

1. GET /weather/current - Returns the current weather for a given city
   - Query parameter: city (string)
   - Returns JSON with temperature, humidity, and conditions

2. GET /weather/forecast - Returns the 5-day forecast for a given city
   - Query parameter: city (string)
   - Returns JSON array with date, temperature, and conditions for each day

3. POST /weather/alert - Register for weather alerts
   - Request body: JSON with city, email, and alert_type (rain, snow, extreme)
   - Returns JSON with success status and alert_id

Use a dictionary as an in-memory database. No need for actual weather data - use mock data.""")
    
    # Create the api.py file (the working one)
    write_file(os.path.join(OUTPUT_DIR, "api.py"), """from flask import Flask, request, jsonify
import uuid

app = Flask(__name__)

# In-memory database
weather_data = {
    "New York": {
        "current": {
            "temperature": 72,
            "humidity": 50,
            "conditions": "Sunny"
        },
        "forecast": [
            {"date": "2023-07-01", "temperature": 75, "conditions": "Sunny"},
            {"date": "2023-07-02", "temperature": 77, "conditions": "Partly Cloudy"},
            {"date": "2023-07-03", "temperature": 80, "conditions": "Sunny"},
            {"date": "2023-07-04", "temperature": 82, "conditions": "Sunny"},
            {"date": "2023-07-05", "temperature": 81, "conditions": "Partly Cloudy"}
        ]
    },
    "Los Angeles": {
        "current": {
            "temperature": 85,
            "humidity": 40,
            "conditions": "Sunny"
        },
        "forecast": [
            {"date": "2023-07-01", "temperature": 86, "conditions": "Sunny"},
            {"date": "2023-07-02", "temperature": 88, "conditions": "Sunny"},
            {"date": "2023-07-03", "temperature": 90, "conditions": "Sunny"},
            {"date": "2023-07-04", "temperature": 91, "conditions": "Sunny"},
            {"date": "2023-07-05", "temperature": 89, "conditions": "Sunny"}
        ]
    }
}

alerts = {}

@app.route('/weather/current', methods=['GET'])
def get_current_weather():
    city = request.args.get('city')
    
    if not city:
        return jsonify({"error": "City parameter is required"}), 400
    
    if city not in weather_data:
        return jsonify({"error": "City not found"}), 404
    
    return jsonify(weather_data[city]["current"])

@app.route('/weather/forecast', methods=['GET'])
def get_weather_forecast():
    city = request.args.get('city')
    
    if not city:
        return jsonify({"error": "City parameter is required"}), 400
    
    if city not in weather_data:
        return jsonify({"error": "City not found"}), 404
    
    return jsonify(weather_data[city]["forecast"])

@app.route('/weather/alert', methods=['POST'])
def register_weather_alert():
    data = request.json
    
    if not data:
        return jsonify({"error": "Request body is required"}), 400
    
    required_fields = ['city', 'email', 'alert_type']
    for field in required_fields:
        if field not in data:
            return jsonify({"error": f"Missing required field: {field}"}), 400
    
    city = data['city']
    email = data['email']
    alert_type = data['alert_type']
    
    if city not in weather_data:
        return jsonify({"error": "City not found"}), 404
    
    valid_alert_types = ['rain', 'snow', 'extreme']
    if alert_type not in valid_alert_types:
        return jsonify({"error": f"Invalid alert_type. Must be one of: {', '.join(valid_alert_types)}"}), 400
    
    alert_id = str(uuid.uuid4())
    alerts[alert_id] = {
        "city": city,
        "email": email,
        "alert_type": alert_type
    }
    
    return jsonify({"success": True, "alert_id": alert_id})

if __name__ == '__main__':
    app.run(debug=True)""")
    
    # Create the buggy_api.py file (with intentional bugs)
    write_file(os.path.join(OUTPUT_DIR, "buggy_api.py"), """from flask import Flask, request, jsonify
import uuid

app = Flask(__name__)

# In-memory database
weather_data = {
    "New York": {
        "current": {
            "temperature": 72,
            "humidity": 50,
            "conditions": "Sunny"
        },
        "forecast": [
            {"date": "2023-07-01", "temperature": 75, "conditions": "Sunny"},
            {"date": "2023-07-02", "temperature": 77, "conditions": "Partly Cloudy"},
            {"date": "2023-07-03", "temperature": 80, "conditions": "Sunny"},
            {"date": "2023-07-04", "temperature": 82, "conditions": "Sunny"},
            {"date": "2023-07-05", "temperature": 81, "conditions": "Partly Cloudy"}
        ]
    },
    "Los Angeles": {
        "current": {
            "temperature": 85,
            "humidity": 40,
            "conditions": "Sunny"
        },
        "forecast": [
            {"date": "2023-07-01", "temperature": 86, "conditions": "Sunny"},
            {"date": "2023-07-02", "temperature": 88, "conditions": "Sunny"},
            {"date": "2023-07-03", "temperature": 90, "conditions": "Sunny"},
            {"date": "2023-07-04", "temperature": 91, "conditions": "Sunny"},
            {"date": "2023-07-05", "temperature": 89, "conditions": "Sunny"}
        ]
    }
}

alerts = {}

@app.route('/weather/current', methods=['GET'])
def get_current_weather():
    city = request.args.get('city')
    
    # BUG: Missing city parameter check
    
    # BUG: Doesn't check if city exists in weather_data
    return jsonify(weather_data[city]["current"])

@app.route('/weather/forecast', methods=['GET'])
def get_weather_forecast():
    city = request.args.get('city')
    
    if not city:
        return jsonify({"error": "City parameter is required"}), 400
    
    # BUG: Incorrect key name, should be "forecast"
    return jsonify(weather_data[city]["forecasts"])

@app.route('/weather/alert', methods=['POST'])
def register_weather_alert():
    # BUG: Incorrectly accessing request body
    data = request.form
    
    if not data:
        return jsonify({"error": "Request body is required"}), 400
    
    required_fields = ['city', 'email', 'alert_type']
    for field in required_fields:
        if field not in data:
            return jsonify({"error": f"Missing required field: {field}"}), 400
    
    city = data['city']
    email = data['email']
    alert_type = data['alert_type']
    
    if city not in weather_data:
        return jsonify({"error": "City not found"}), 404
    
    valid_alert_types = ['rain', 'snow', 'extreme']
    if alert_type not in valid_alert_types:
        return jsonify({"error": f"Invalid alert_type. Must be one of: {', '.join(valid_alert_types)}"}), 400
    
    # BUG: Not storing the alert properly
    alert_id = str(uuid.uuid4())
    # Missing code to store alert in alerts dictionary
    
    return jsonify({"success": True, "alert_id": alert_id})

if __name__ == '__main__':
    app.run(debug=True)""")
    
    # Create the existing_tests.py file
    write_file(os.path.join(OUTPUT_DIR, "existing_tests.py"), """import unittest
import json
from api import app

class WeatherAPITest(unittest.TestCase):
    def setUp(self):
        self.app = app.test_client()
        self.app.testing = True

    def test_get_current_weather_success(self):
        response = self.app.get('/weather/current?city=New York')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 200)
        self.assertIn('temperature', data)
        self.assertIn('humidity', data)
        self.assertIn('conditions', data)

    def test_get_current_weather_missing_city(self):
        response = self.app.get('/weather/current')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 400)
        self.assertIn('error', data)
        self.assertEqual(data['error'], 'City parameter is required')

if __name__ == '__main__':
    unittest.main()""")
    
    # Create the test_weather_api.py file
    write_file(os.path.join(OUTPUT_DIR, "test_weather_api.py"), """import unittest
import json
from buggy_api import app

class WeatherAPITest(unittest.TestCase):
    def setUp(self):
        self.app = app.test_client()
        self.app.testing = True

    def test_get_current_weather_success(self):
        response = self.app.get('/weather/current?city=New York')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 200)
        self.assertIn('temperature', data)
        self.assertIn('humidity', data)
        self.assertIn('conditions', data)

    def test_get_current_weather_missing_city(self):
        response = self.app.get('/weather/current')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 400)
        self.assertIn('error', data)
        self.assertEqual(data['error'], 'City parameter is required')
        
    def test_get_forecast_with_valid_city(self):
        response = self.app.get('/weather/forecast?city=New York')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 200)
        self.assertTrue(isinstance(data, list))
        self.assertEqual(len(data), 5)  # 5-day forecast
        self.assertIn('date', data[0])
        self.assertIn('temperature', data[0])
        self.assertIn('conditions', data[0])
        
    def test_get_forecast_with_invalid_city(self):
        response = self.app.get('/weather/forecast?city=InvalidCity')
        data = json.loads(response.data)
        
        self.assertEqual(response.status_code, 404)
        self.assertIn('error', data)
        self.assertEqual(data['error'], 'City not found')
        
    def test_register_alert_success(self):
        data = {
            'city': 'New York',
            'email': 'user@example.com',
            'alert_type': 'rain'
        }
        response = self.app.post('/weather/alert', 
                                json=data,
                                content_type='application/json')
        result = json.loads(response.data)
        
        self.assertEqual(response.status_code, 200)
        self.assertTrue(result['success'])
        self.assertIn('alert_id', result)
        
    def test_register_alert_missing_data(self):
        data = {
            'city': 'New York',
            'email': 'user@example.com'
            # Missing alert_type
        }
        response = self.app.post('/weather/alert', 
                                json=data,
                                content_type='application/json')
        result = json.loads(response.data)
        
        self.assertEqual(response.status_code, 400)
        self.assertIn('error', result)
        self.assertIn('Missing required field', result['error'])

if __name__ == '__main__':
    unittest.main()""")
    
    # Create the error_output.log file
    write_file(os.path.join(OUTPUT_DIR, "error_output.log"), """ERROR: Test failures in test_weather_api.py

======================================================================
ERROR: test_get_current_weather_missing_city (test_weather_api.WeatherAPITest)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "test_weather_api.py", line 17, in test_get_current_weather_missing_city
    data = json.loads(response.data)
  File "/usr/lib/python3.8/json/__init__.py", line 357, in loads
    return _default_decoder.decode(s)
  File "/usr/lib/python3.8/json/decoder.py", line 337, in decode
    obj, end = self.raw_decode(s, idx=_w(s, 0).end())
  File "/usr/lib/python3.8/json/decoder.py", line 355, in raw_decode
    raise JSONDecodeError("Expecting value", s, err.value) from None
json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)

======================================================================
ERROR: test_get_current_weather_success (test_weather_api.WeatherAPITest)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "test_weather_api.py", line 12, in test_get_current_weather_success
    response = self.app.get('/weather/current?city=New York')
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1135, in get
    return self.open(*args, **kw)
  File "/usr/local/lib/python3.8/site-packages/flask/testing.py", line 222, in open
    return super().open(*args, **kwargs)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1090, in open
    response = self.run_wsgi_app(environ, buffered=buffered)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 891, in run_wsgi_app
    rv = run_wsgi_app(self.application, environ, buffered=buffered)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1077, in run_wsgi_app
    app_rv = app(environ, start_response)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2503, in __call__
    return self.wsgi_app(environ, start_response)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2489, in wsgi_app
    response = self.handle_exception(e)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2486, in wsgi_app
    response = self.full_dispatch_request()
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 1834, in full_dispatch_request
    rv = self.dispatch_request()
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 1820, in dispatch_request
    return self.ensure_sync(self.view_functions[rule.endpoint])(**view_args)
  File "buggy_api.py", line 51, in get_current_weather
    return jsonify(weather_data[city]["current"])
KeyError: None

======================================================================
ERROR: test_get_forecast_with_invalid_city (test_weather_api.WeatherAPITest)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "test_weather_api.py", line 31, in test_get_forecast_with_invalid_city
    data = json.loads(response.data)
  File "/usr/lib/python3.8/json/__init__.py", line 357, in loads
    return _default_decoder.decode(s)
  File "/usr/lib/python3.8/json/decoder.py", line 337, in decode
    obj, end = self.raw_decode(s, idx=_w(s, 0).end())
  File "/usr/lib/python3.8/json/decoder.py", line 355, in raw_decode
    raise JSONDecodeError("Expecting value", s, err.value) from None
json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)

======================================================================
ERROR: test_get_forecast_with_valid_city (test_weather_api.WeatherAPITest)
----------------------------------------------------------------------
Traceback (most recent call last):
  File "test_weather_api.py", line 24, in test_get_forecast_with_valid_city
    response = self.app.get('/weather/forecast?city=New York')
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1135, in get
    return self.open(*args, **kw)
  File "/usr/local/lib/python3.8/site-packages/flask/testing.py", line 222, in open
    return super().open(*args, **kwargs)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1090, in open
    response = self.run_wsgi_app(environ, buffered=buffered)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 891, in run_wsgi_app
    rv = run_wsgi_app(self.application, environ, buffered=buffered)
  File "/usr/local/lib/python3.8/site-packages/werkzeug/test.py", line 1077, in run_wsgi_app
    app_rv = app(environ, start_response)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2503, in __call__
    return self.wsgi_app(environ, start_response)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2489, in wsgi_app
    response = self.handle_exception(e)
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 2486, in wsgi_app
    response = self.full_dispatch_request()
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 1834, in full_dispatch_request
    rv = self.dispatch_request()
  File "/usr/local/lib/python3.8/site-packages/flask/app.py", line 1820, in dispatch_request
    return self.ensure_sync(self.view_functions[rule.endpoint])(**view_args)
  File "buggy_api.py", line 62, in get_weather_forecast
    return jsonify(weather_data[city]["forecasts"])
KeyError: 'forecasts'""")
    
    # Create verify_weather_api.py file
    verify_api_content = '''#!/usr/bin/env python

"""Verification program for the weather API.
This program checks if the basic functionality of the API is working correctly.
It returns exit code 0 if all checks pass, non-zero otherwise.
"""

import sys
import unittest
import json
from importlib.util import spec_from_file_location, module_from_spec
import os

def import_module_from_file(file_path, module_name="dynamic_module"):
    """Import a module from a file path."""
    spec = spec_from_file_location(module_name, file_path)
    if spec is None:
        raise ImportError(f"Could not find module at {file_path}")
    
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def run_tests(code_file, test_file):
    """Run tests and return True if all tests pass, False otherwise."""
    # Get the directory of the code file and test file
    code_dir = os.path.dirname(os.path.abspath(code_file))
    # Add code directory to path to ensure imports work
    sys.path.insert(0, code_dir)
    
    try:
        # Dynamically import the test module
        test_module = import_module_from_file(test_file)
        
        # Create a test suite and run the tests
        test_suite = unittest.defaultTestLoader.loadTestsFromModule(test_module)
        test_runner = unittest.TextTestRunner(verbosity=0)
        test_result = test_runner.run(test_suite)
        
        # Return True if all tests pass, False otherwise
        return test_result.wasSuccessful()
    except Exception as e:
        print(f"Error running tests: {e}")
        return False
    finally:
        # Remove the code directory from path
        if code_dir in sys.path:
            sys.path.remove(code_dir)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python verify_weather_api.py <code_file> <test_file>")
        sys.exit(1)
    
    code_file = sys.argv[1]
    test_file = sys.argv[2]
    
    success = run_tests(code_file, test_file)
    
    # Exit with code 0 if tests pass, 1 otherwise
    sys.exit(0 if success else 1)
'''
    write_file(os.path.join(OUTPUT_DIR, "verify_weather_api.py"), verify_api_content)
    
    # Create the coverage.xml file
    write_file(os.path.join(OUTPUT_DIR, "coverage.xml"), """<?xml version="1.0" ?>
<coverage version="6.5.0" timestamp="1682592307" lines-valid="105" lines-covered="87" line-rate="0.829" branches-covered="0" branches-valid="0" branch-rate="0" complexity="0">
	<sources>
		<source>/Users/gregtanaka/pdd/output</source>
	</sources>
	<packages>
		<package name="." line-rate="0.829" branch-rate="0" complexity="0">
			<classes>
				<class name="api.py" filename="api.py" complexity="0" line-rate="0.829" branch-rate="0">
					<methods/>
					<lines>
						<line number="1" hits="1"/>
						<line number="2" hits="1"/>
						<line number="4" hits="1"/>
						<line number="7" hits="1"/>
						<line number="42" hits="1"/>
						<line number="44" hits="1"/>
						<line number="45" hits="1"/>
						<line number="47" hits="1"/>
						<line number="49" hits="1"/>
						<line number="51" hits="1"/>
						<line number="53" hits="1"/>
						<line number="55" hits="1"/>
						<line number="57" hits="1"/>
						<line number="59" hits="1"/>
						<line number="60" hits="1"/>
						<line number="62" hits="1"/>
						<line number="64" hits="1"/>
						<line number="66" hits="1"/>
						<line number="68" hits="1"/>
						<line number="70" hits="1"/>
						<line number="72" hits="1"/>
						<line number="73" hits="1"/>
						<line number="75" hits="1"/>
						<line number="77" hits="1"/>
						<line number="79" hits="1"/>
						<line number="81" hits="1"/>
						<line number="82" hits="0"/>
						<line number="84" hits="1"/>
						<line number="85" hits="0"/>
						<line number="87" hits="1"/>
						<line number="88" hits="0"/>
						<line number="90" hits="1"/>
						<line number="91" hits="0"/>
						<line number="93" hits="1"/>
						<line number="94" hits="0"/>
						<line number="96" hits="1"/>
						<line number="98" hits="1"/>
						<line number="99" hits="0"/>
						<line number="101" hits="1"/>
						<line number="102" hits="0"/>
						<line number="104" hits="1"/>
						<line number="105" hits="0"/>
						<line number="107" hits="0"/>
						<line number="108" hits="0"/>
						<line number="109" hits="0"/>
						<line number="110" hits="0"/>
						<line number="111" hits="0"/>
						<line number="112" hits="0"/>
						<line number="113" hits="0"/>
						<line number="114" hits="0"/>
						<line number="116" hits="0"/>
					</lines>
				</class>
			</classes>
		</package>
	</packages>
</coverage>""")
    
    # Create the complex_prompt.prompt file for preprocess command
    write_file(os.path.join(OUTPUT_DIR, "complex_prompt.prompt"), """Create a sophisticated task management application with the following features:

# User Features
- User registration and authentication
- User profiles with customizable settings
- Role-based access control (admin, manager, user)

# Task Management
- Create, read, update, delete tasks
- Assign tasks to users
- Set due dates, priorities, and categories
- Add attachments and comments to tasks

# Project Organization
- Group tasks into projects
- Set project deadlines and milestones
- Track project progress and statistics

# Notifications
- Email notifications for task assignments and deadlines
- In-app notification center
- Scheduled reminders

# Reporting
- Generate reports on task completion rates
- User productivity metrics
- Project timeline visualization

## Technical Requirements
- Use a modern web framework
- Implement RESTful API for all features
- Mobile-responsive design
- Data persistence with proper database design
- Comprehensive test coverage

## Additional Notes
@include("security_requirements.txt")
@include("ui_guidelines.txt")""")
    
    # Create security_requirements.txt for inclusion in complex prompt
    write_file(os.path.join(OUTPUT_DIR, "security_requirements.txt"), """# Security Requirements

1. Authentication:
   - Implement strong password policies (minimum length, complexity)
   - Support multi-factor authentication
   - Secure session management with proper timeout

2. Authorization:
   - Role-based access control for all resources
   - Proper permission validation on all API endpoints
   - Audit logging for sensitive operations

3. Data Protection:
   - Encrypt sensitive data at rest
   - Use HTTPS for all communications
   - Implement proper input validation to prevent injection attacks
   - Apply output encoding to prevent XSS vulnerabilities

4. API Security:
   - Rate limiting to prevent abuse
   - API key management
   - JWT tokens with proper expiration

5. Infrastructure:
   - Regular security updates for all dependencies
   - Environment isolation (development, staging, production)
   - Secure configuration management (no hardcoded secrets)

6. Compliance:
   - GDPR compliance for user data handling
   - Data retention policies
   - Right to be forgotten implementation""")
    
    # Create ui_guidelines.txt for inclusion in complex prompt
    write_file(os.path.join(OUTPUT_DIR, "ui_guidelines.txt"), """# UI/UX Design Guidelines

## Design System
- Use a consistent color palette based on the brand colors
- Implement a cohesive typography system with no more than 3 font families
- Maintain consistent spacing using a predefined grid system
- Create reusable UI components for common elements

## Accessibility
- Ensure WCAG 2.1 AA compliance
- Provide sufficient color contrast
- Support keyboard navigation
- Include proper ARIA attributes
- Ensure screen reader compatibility

## Responsive Design
- Design for mobile-first approach
- Create distinct layouts for mobile, tablet, and desktop
- Ensure touch-friendly UI elements on mobile devices
- Implement proper viewport settings

## User Experience
- Minimize cognitive load with intuitive navigation
- Provide clear feedback for user actions
- Implement progressive disclosure for complex features
- Include helpful empty states
- Design clear call-to-action elements
- Provide error prevention and recovery mechanisms

## Performance
- Optimize image and asset loading
- Implement lazy loading for media content
- Minimize initial load time
- Add appropriate loading indicators for async operations

## Branding
- Apply consistent brand identity across all interfaces
- Maintain brand voice in all text content
- Include the logo in the appropriate locations""")
    
    logger.info("All test files regenerated successfully!")

if __name__ == "__main__":
    main() 