# QRCode-Gen

`qrcode-gen` is a utility for generating QR codes enhanced with LLM-driven prompts. It builds on top of the **PDD** framework and uses the same model configuration (`llm_model.csv`) and environment variable system for flexibility and portability.

---

## Installation & Setup

### 1. Clone & Install Dependencies

    git clone https://github.com/gltanaka/pdd.git
    cd qrcode-gen
    pip install -r requirements.txt

### 2. Configure Models (`llm_model.csv`)

QRCode-Gen follows the same tiered model configuration as PDD:

- **User-specific:** `~/.pdd/llm_model.csv`  
- **Project-specific:** `<PROJECT_ROOT>/.pdd/llm_model.csv`  
- **Package default:** falls back to bundled config

Trim your `llm_model.csv` accordingly to the models you have. If you only have **Gemini 2.5 Flash**, for example:

    provider,model,input,output,coding_arena_elo,base_url,api_key,max_reasoning_tokens,structured_output,reasoning_type
    Google,gpt-4.1-nano,0.1,0.4,1249,,OPENAI_API_KEY,0,True,none
    Google,gemini/gemini-2.5-flash,0.15,0.6,1330,,GEMINI_API_KEY,0,True,effort

Note: **GPT 4.1 Nano** is required to exist as it is the default model. If you have another model to use, it will prioritize that one.

See the [main PDD README](../README.md) for a full explanation of how `llm_model.csv` works.

### 3. Setup Firecrawl and Add Environment Variables

QRCode-Gen uses Firecrawl to scrape the code from https://huggingface.co/DionTimmer/controlnet_qrcode-control_v1p_sd15. An API key is required to use Firecrawl.

Populate a `.env` file (or export in your shell config):

    GEMINI_API_KEY=your_key_here
    FIRECRAWL_API_KEY=your_key_here

---

## Usage

### Generate a QR Code

Once setup is complete, you can create a QR code by writing a `.prompt` file and running:

    pdd generate my_qrcode_{language}.prompt

### Example: QR Code Sandwich

    pdd generate qrcode_sandwich_python.prompt

Where `qrcode_sandwich_python.prompt` might look like:

    <note>
    This prompt is designed to guide code generation for a ControlNet-based image synthesis pipeline. It instructs the model to generate Python code that overlays a QR code pointing to "https://PromptDriven.ai" into a realistic sandwich image using ControlNet QR conditioning. Do not install `xformers`, as it is not compatible with macOS.
    </note>
    ...

The prompt will generate a script that can be run to produce a QR code overlaid onto an image.

The generated QR code will be saved in the path you’ve configured (`$PDD_GENERATE_OUTPUT_PATH`), or in the working directory if not set.

---