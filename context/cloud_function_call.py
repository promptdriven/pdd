import requests

def call_cloud_function(firebase_token):
    # Replace with your Cloud Function URL
    CLOUD_FUNCTION_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net/on_request_example"
    
    # Make a request to your Cloud Function with the Firebase token in the Authorization header
    headers = {"Authorization": f"Bearer {firebase_token}"}
    response = requests.get(CLOUD_FUNCTION_URL, headers=headers)
    
    return response.json()

firebase_token = "YOUR_FIREBASE_TOKEN_HERE"

# Call the Cloud Function
result = call_cloud_function(firebase_token)
print(f"Cloud Function Result: {result}")
