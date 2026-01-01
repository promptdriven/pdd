
# PDD Cloud
- [What is PDD Cloud?](#what-is-pdd-cloud)
- [PDD Cloud Automated Grounding](#automated-grounding)
- [Accessing the PDD Cloud Dashboard](#accessing-the-pdd-cloud-dashboard)
- [PDD-CLI Cloud Authentication](#pdd-cli-cloud-authentication-usually-one-time-only)
- [PDD-CLI Local Mode (non-cloud)](#pdd-cli-local-mode)

<a name="what-is-pdd-cloud"></a>
## What is PDD Cloud?

PDD Cloud maximizes ease-of-use and reliability of code generation using its proprietary [Automated Grounding](#automated-grounding)

Currently in invite-only Beta testing, PDD Cloud is not enabled for most users.  Your PDD Commands will default to local-only execution.

#### When in general release, PDD Cloud will offer:



#### 1. **The best available code generation**
- correctness, reproducibility, and reliability are all built-in
- built-in [Automated Grounding](#automated-grounding) - your code improves the more you use PDD


#### 2. **Hands-free setup and operation**
- no need to manage API keys locally
- built-in access to PDD-optimized selection of the most appropriate model for each task
- automatic updates, bug fixes, and other improvements


#### 3. **Automatic cost optimization**
- built-in automatic smart model selection and smart caching to minimize LLM API costs

#### 4. **Usage Analytics**
- track your team's usage and costs through the PDD Cloud dashboard

#### 5. **Collaboration**: 
- share prompts and generated code with team members
- access community contributions to **Automated Grounding** to further strengthen your project reliability, and reduce development time

<br><br>

<a name="automated-grounding"></a>
## PDD Cloud Automated Grounding
PDD Cloud includes Automated Grounding, which dramatically improves code output quality, and reduces your time spent creating overly-granular prompt details.   

PDD Cloud maintains the history of your prompts and output code.  This history of an output file captures everything you have ever specified about that code file.  Automatic Grounding selects the best portions of that history to inject into prompts during `pdd generate`.   The result is stable outputs over time.

Without Automated Grounding, you may experience issues such as these:
- function signatures change when you re-generate
- features decompose into different functions and objects each time you generate
- etc.

As a result, you will spend more time iterating on prompt details in order to control the LLM generation, along with time spent re-generating and re-testing.

But with PDD Cloud, Automated Grounding remembers the most relevant and salient characteristics described in the prompt/code history, and selects the best ones to guide the LLM in creating correct and stable outputs, as described.

For a more detailed treatment, see [Automated Grounding](docs/prompting_guide.md#automated-grounding) in the prompting guide.


---

<a name="accessing-the-pdd-cloud-dashboard"></a>
### Accessing the PDD Cloud Dashboard

Once in general public release, you will access the PDD Cloud dashboard here at: https://promptdriven.ai/

There you will first need to authenticate with your GitHub credentials.

In the dashbaord, you can
- View usage statistics
- Manage team access
- Configure default settings
- Control access to the community shared **my Recall** spaces
- Track costs

<br>

--- 
<a name="pdd-cli-cloud-authentication-usually-one-time-only"></a>
### PDD-CLI Cloud Authentication (usually one-time only)

When running in cloud mode, PDD uses GitHub Single Sign-On (SSO) for authentication. On first use, you'll be prompted to authenticate:

1. PDD will open your default browser to the GitHub login page
2. Log in with your GitHub account
3. Authorize PDD Cloud to access your GitHub profile
4. Once authenticated, you can return to your terminal to continue using PDD

The authentication token is securely stored locally and automatically refreshed as needed.

---

<a name="pdd-cli-local-mode"></a>
### PDD-CLI Local Mode

When PDD Cloud is publicly available, cloud execution will be default for all PDD commands; the --local flag is necessary to run in local mode.

When running in local mode with the `--local` flag, you'll need to set up API keys for the language models.  

As in the installation instructions,  it's typically most convenient to run `pdd setup` to set up these keys and associated environment variables.   

For those users who prefer to set up and manage their environment differently, without `pdd setup`, ensure your API keys are set as environment variables, in the shell(s) where you are running PDD-CLI commands.   Some examples, which vary depending on which LLM providers you choose to use:

```bash
# For OpenAI
export OPENAI_API_KEY=your_api_key_here

# For Anthropic
export ANTHROPIC_API_KEY=your_api_key_here

# For other supported providers (LiteLLM supports multiple LLM providers)
export PROVIDER_API_KEY=your_api_key_here
```
Add these to your `.bashrc`, `.zshrc`, or equivalent for persistence.

#### how PDD accesses these keys

PDD's local mode uses LiteLLM (version 1.75.5 or higher) for interacting with language models, providing:

- Support for multiple model providers (OpenAI, Anthropic, Google/Vertex AI, and more)
- Automatic model selection based on strength settings
- Response caching for improved performance
- Smart token usage tracking and cost estimation
- Interactive API key acquisition when keys are missing

For detailed information about configuring the models available for PDD use, see [Model Configuration](README-ADVANCED-CONFIGURATION.md#model-configuration) in the Advanced Configuration README.

### Important Note: 
When keys are missing from the shell environment, PDD commands will prompt for them interactively and securely store them in your local `.env` file.  


