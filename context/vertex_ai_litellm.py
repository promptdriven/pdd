from litellm import completion
import json 
import os
os.environ["LITELLM_LOG"] = "DEBUG"
## GET CREDENTIALS from env var
file_path = os.environ.get("VERTEX_CREDENTIALS")

# Load the JSON file
with open(file_path, 'r') as file:
    vertex_credentials = json.load(file)

# Convert to JSON string
vertex_credentials_json = json.dumps(vertex_credentials)


response = completion(
  model="vertex_ai/gemini-2.5-pro-preview-05-06",
  messages=[{"content": "You are a good bot.","role": "system"}, {"content": "Hello, how are you?","role": "user"}], 
  vertex_credentials=vertex_credentials_json,
  vertex_project="meta-plateau-401521", 
  vertex_location="us-central1"
)

print(response)