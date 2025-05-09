import boto3
import os
from botocore.exceptions import ClientError
import logging
from dotenv import load_dotenv
from botocore.client import Config

# Load environment variables from .env file
load_dotenv()

# Configure logging
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')

# --- Configuration ---
# Read required configuration from environment variables
gcs_access_key_id = os.environ.get("GCS_HMAC_ACCESS_KEY_ID")
gcs_secret_access_key = os.environ.get("GCS_HMAC_SECRET_ACCESS_KEY")
bucket_name = os.environ.get("GCS_BUCKET_NAME")
gcs_endpoint_url = "https://storage.googleapis.com"

# Check if all required environment variables are set
if not all([gcs_access_key_id, gcs_secret_access_key, bucket_name]):
    logging.error("Error: Required environment variables are not set.")
    logging.error("Please set GCS_HMAC_ACCESS_KEY_ID, GCS_HMAC_SECRET_ACCESS_KEY, and GCS_BUCKET_NAME.")
    exit(1)

# File details
file_content = "This is a test file uploaded using GCS HMAC keys and boto3."
object_name = "test-hmac-upload.txt" # The desired name for the object in the bucket

# --- Create S3 Client for GCS ---
try:
    # uncomment this if using Boto3 >1.35
    # from botocore.config import Config

    # cfg = Config(
    #     signature_version='s3v4',
    #     request_checksum_calculation='when_required',
    #     response_checksum_validation='when_required',
    #     s3={'addressing_style': 'path'}   # keeps path-style like before
    # )

    s3_client = boto3.client(
        's3',
        endpoint_url='https://storage.googleapis.com',
        aws_access_key_id=gcs_access_key_id,
        aws_secret_access_key=gcs_secret_access_key,
        region_name='auto',              # any string is fine; 'auto' is conventional
        # config=cfg
    )
    
    logging.info("Successfully created S3 client configured for GCS.")
except Exception as e:
    logging.error(f"Failed to create S3 client: {e}")
    exit(1)

# --- Upload File ---
try:
    logging.info(f"Attempting to upload '{object_name}' to bucket '{bucket_name}'...")
    s3_client.put_object(
        Bucket=bucket_name,
        Key=object_name,
        Body=file_content.encode('utf-8') # Encode string content to bytes
    )
    logging.info(f"Successfully uploaded '{object_name}' to bucket '{bucket_name}'.")
    print(f"File '{object_name}' uploaded to GCS bucket '{bucket_name}'.")
    print(f"Verify here: https://console.cloud.google.com/storage/browser/{bucket_name}/{object_name}")

except ClientError as e:
    logging.error(f"ClientError during upload: {e}")
    error_code = e.response.get('Error', {}).get('Code')
    if error_code == 'NoSuchBucket':
        logging.error(f"The specified bucket '{bucket_name}' does not exist or you lack permissions.")
    elif error_code == 'InvalidAccessKeyId' or error_code == 'SignatureDoesNotMatch':
         logging.error("Authentication failed. Check your GCS HMAC keys.")
    else:
        logging.error("An unexpected error occurred during upload.")
except Exception as e:
    logging.error(f"An unexpected error occurred: {e}")
    exit(1) 