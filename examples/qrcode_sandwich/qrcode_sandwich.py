import torch
from PIL import Image
from diffusers import StableDiffusionControlNetImg2ImgPipeline, ControlNetModel, DDIMScheduler
from diffusers.utils import load_image
import qrcode
import random
import io

# --- 1. Installation Check (for user guidance) ---
# Ensure you have the necessary libraries installed.
# pip install diffusers transformers accelerate torch Pillow qrcode

# --- 2. Configuration ---
QR_CODE_URL = "https://PromptDriven.ai"
PROMPT = "A delicious stacked sandwich with embedded QR code textures in bread and fillings. Use the face of the sandwich and blend the qr code into the toppings of the sandwich. Have the sandwich use darker and lighter colors to make the QR code stand out."
NEGATIVE_PROMPT = "ugly, disfigured, low quality, blurry, nsfw, plain, simple, bad qr code, unreadable, distorted, abstract"
IMAGE_RESOLUTION = 512 # Recommended for best QR code detail and overall quality
GUIDANCE_SCALE = 7.0 # Higher values emphasize the prompt
CONTROLNET_CONDITIONING_SCALE = 1.5 # Higher values emphasize the ControlNet input (QR code)
STRENGTH = 0.9 # How much the diffusion process can change the initial image (if provided)
NUM_INFERENCE_STEPS = 20 # More steps can lead to better quality
SEED = random.randint(0, 1000000) # Use a random seed

# --- 3. Device Setup for macOS Compatibility ---
# Automatically detect and set the device (MPS for Apple Silicon, otherwise CPU)
device = "mps" if torch.backends.mps.is_available() else "cpu"
print(f"Using device: {device}")

# --- 4. QR Code Generation ---
def generate_qr_code_image(url: str, box_size: int = 10, border: int = 4) -> Image.Image:
    """Generates a QR code image for the given URL."""
    qr = qrcode.QRCode(
        version=1,
        error_correction=qrcode.constants.ERROR_CORRECT_H, # High correction for better scannability
        box_size=box_size,
        border=border,
    )
    qr.add_data(url)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white").convert("RGB")
    return img

print(f"Generating QR code for: {QR_CODE_URL}")
qr_image = generate_qr_code_image(QR_CODE_URL)
# Save QR code for verification (optional)
# qr_image.save("generated_qr_code.png")
# print("Generated QR code saved as generated_qr_code.png")

# --- 5. Image Resizing Utility (from example) ---
def resize_for_condition_image(input_image: Image, resolution: int):
    """Resizes an image to a multiple of 64, maintaining aspect ratio."""
    input_image = input_image.convert("RGB")
    W, H = input_image.size
    k = float(resolution) / min(H, W)
    H *= k
    W *= k
    H = int(round(H / 64.0)) * 64
    W = int(round(W / 64.0)) * 64
    img = input_image.resize((W, H), resample=Image.LANCZOS)
    return img

# --- 6. Load ControlNet and Pipeline ---
print("Loading ControlNet model...")
controlnet = ControlNetModel.from_pretrained(
    "DionTimmer/controlnet_qrcode-control_v1p_sd15",
    torch_dtype=torch.float16 if device == "mps" else torch.float32 # MPS often prefers float16 for performance
)

print("Loading Stable Diffusion pipeline...")
pipe = StableDiffusionControlNetImg2ImgPipeline.from_pretrained(
    "runwayml/stable-diffusion-v1-5",
    controlnet=controlnet,
    safety_checker=None, # Disable safety checker for this example
    torch_dtype=torch.float16 if device == "mps" else torch.float32
)

# Move pipeline to the detected device
pipe = pipe.to(device)

# Set scheduler
pipe.scheduler = DDIMScheduler.from_config(pipe.scheduler.config)

# --- 7. Prepare Images for Conditioning ---
# The ControlNet QR model is an img2img pipeline, meaning it expects an initial image.
# For a "photorealistic sandwich" without a specific starting image, we can use a
# simple placeholder or a very generic image that will be heavily transformed.
# A blank image or a simple texture can serve as a starting point.
# Let's create a plain white image as a starting point, which the model will transform.
init_image_placeholder = Image.new('RGB', (IMAGE_RESOLUTION, IMAGE_RESOLUTION), color = 'white')

# Resize the generated QR code and the initial image placeholder for conditioning
condition_image = resize_for_condition_image(qr_image, IMAGE_RESOLUTION)
init_image = resize_for_condition_image(init_image_placeholder, IMAGE_RESOLUTION)

# --- 8. Generate Image ---
print(f"Generating image with seed: {SEED}")
generator = torch.Generator(device=device).manual_seed(SEED)

output = pipe(
    prompt=PROMPT,
    negative_prompt=NEGATIVE_PROMPT,
    image=init_image, # The initial image to be transformed
    control_image=condition_image, # The QR code conditioning image
    width=IMAGE_RESOLUTION,
    height=IMAGE_RESOLUTION,
    guidance_scale=GUIDANCE_SCALE,
    controlnet_conditioning_scale=CONTROLNET_CONDITIONING_SCALE,
    generator=generator,
    strength=STRENGTH,
    num_inference_steps=NUM_INFERENCE_STEPS,
)

# --- 9. Save and Display Result ---
result_image = output.images[0]
output_filename = "sandwich_with_qr_code.png"
result_image.save(output_filename)
print(f"Generated image saved as {output_filename}")

# Optionally display the image
# result_image.show()
