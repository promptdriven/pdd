import base64
import json

# Assuming AzureKeyVaultService is in a module named 'service.azure_key_vault_service'
# You might need to adjust the import based on your project structure.
# from service.azure_key_vault_service import AzureKeyVaultService

# Placeholder for AzureKeyVaultService if you want to run this snippet standalone
# For actual use, ensure AzureKeyVaultService is correctly imported and configured.
# class AzureKeyVaultService:
#     def get_secret(self, secret_name: str) -> str:
#         print(f"Attempting to fetch secret: {secret_name}")
#         # In a real scenario, this would interact with Azure Key Vault.
#         # For this example, returning a dummy base64 encoded JSON string.
#         # Replace this with your actual Key Vault fetching logic.
#         if secret_name == "GCP-VERTEXAI-SERVICE-ACC":
#             dummy_service_account_json = """{
#   "type": "service_account",
#   "project_id": "your-gcp-project-id",
#   "private_key_id": "your-private-key-id",
#   "private_key": "-----BEGIN PRIVATE KEY-----\nYOUR_PRIVATE_KEY_MATERIAL\n-----END PRIVATE KEY-----\n",
#   "client_email": "your-service-account-email@your-gcp-project-id.iam.gserviceaccount.com",
#   "client_id": "your-client-id",
#   "auth_uri": "https://accounts.google.com/o/oauth2/auth",
#   "token_uri": "https://oauth2.googleapis.com/token",
#   "auth_provider_x509_cert_url": "https://www.googleapis.com/oauth2/v1/certs",
#   "client_x509_cert_url": "https://www.googleapis.com/robot/v1/metadata/x509/your-service-account-email%40your-gcp-project-id.iam.gserviceaccount.com"
# }"""
#             return base64.b64encode(dummy_service_account_json.encode("utf-8")).decode("utf-8")
#         return ""

# azure_key_vault_service = AzureKeyVaultService()

# Step 1: Fetch the base64 encoded service account JSON from Azure Key Vault
# The secret name "GCP-VERTEXAI-SERVICE-ACC" is used as identified in your codebase.
vertexai_service_account_b64 = ""

# azure_key_vault_service.get_secret(
#     "GCP-VERTEXAI-SERVICE-ACC"
# )

if vertexai_service_account_b64:
    # Step 2: Decode the base64 string and parse the JSON
    # The .decode("utf-8") is used twice: once for base64 decoding to a string,
    # and then implicitly by json.loads if the input is bytes (though b64decode returns bytes).
    # More explicitly, decode the bytes from b64decode to a string before json.loads.
    try:
        decoded_service_account_json_str = base64.b64decode(vertexai_service_account_b64).decode("utf-8")
        credentials_info = json.loads(decoded_service_account_json_str)
        
        print("Successfully fetched and decoded service account info:")
        print(json.dumps(credentials_info, indent=2))
        
        # This credentials_info can then be used with:
        # from google.oauth2 import service_account
        # credentials = service_account.Credentials.from_service_account_info(credentials_info)
        # And subsequently for ChatVertexAI initialization.

    except json.JSONDecodeError as e:
        print(f"Error decoding JSON: {e}")
    except Exception as e:
        print(f"An error occurred: {e}")
else:
    print("Failed to retrieve the service account secret from Key Vault.")

