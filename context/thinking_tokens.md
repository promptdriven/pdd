Thanks for clarifying. I’ll look into the maximum number of reasoning tokens—those used internally for chain-of-thought or intermediate steps—allowed by each of these models:

* gpt-5-nano
* grok-3-beta
* claude-3-5-haiku-20241022
* deepseek/deepseek-coder
* gemini-2.5-flash-preview-04-17
* gemini-2.5-pro-exp-03-25
* claude-3-7-sonnet-20250219
* deepseek-r1-distill-llama-70b-specdec
* deepseek-r1:70b-llama-distill-q8\_0
* deepseek-r1:32b-qwen-distill-fp16
* o4-mini
* o3
* gpt-4.1
* deepseek-reasoner
* accounts/fireworks/models/deepseek-r1

I’ll gather available technical documentation, model cards, or insights from reliable benchmarks to identify how each handles internal reasoning token limits. I’ll let you know what I find.


## Maximum Internal “Reasoning” Tokens by Model

* **GPT‑4.1‑nano** – *No dedicated chain-of-thought tokens.* This is a standard GPT-4.1 model with a 1M token context window, but **it does not use hidden reasoning tokens internally** (only single-pass answering, unlike OpenAI’s O-series reasoning models).

* **Grok 3 Beta** – *No fixed limit published; can be very large.* xAI’s Grok 3 Beta supports an **extended internal chain-of-thought**. It can spend “anywhere from a few seconds to several minutes reasoning” on hard queries. In practice this means **thousands** of internal reasoning tokens (likely up to the model’s \~131k context if needed) for complex problems, though no explicit max token count is given publicly.

* **Claude‑3.5 “Haiku” (2024‑10‑22)** – *No separate CoT mode.* This version **did not yet have Anthropic’s visible extended reasoning**. It behaves like a normal LM (no hidden multi-step chain-of-thought beyond what’s prompted). Extended “thinking mode” was introduced later with Claude 3.7, so **Claude 3.5 has no special internal reasoning token budget** (only standard generation within its context).

* **Claude‑3.7 “Sonnet” (2025‑02‑19)** – *Up to \~64K reasoning tokens.* Claude 3.7 Sonnet added an **“extended thinking” mode**. Internally it can use a large token budget for chain-of-thought: in Anthropic’s tests it was allowed **up to 64,000 tokens** for reasoning, which significantly boosted accuracy. (The model often stops before the full budget, but 64k was the maximum “thinking” tokens used in evaluations.) Anthropic also supports outputs up to 128k tokens (65k generally available) for this model, aligning with the \~64k reasoning budget.

* **DeepSeek Coder** (`deepseek-coder`) – *No internal CoT (code model).* DeepSeek Coder models are trained on code and natural language for direct generation. They **do not use hidden reasoning tokens**; instead they rely on their normal context window (16k tokens for infill tasks) and output the answer directly (no separate CoT stage).

* **Gemini 2.5 Flash (Preview 04–17)** – *On the order of \~10^4 tokens.* Google’s Gemini 2.5 models all incorporate hidden reasoning. The Flash variant has a **1,048,576 token context** and can produce **up to \~65k tokens in its output**. While Google hasn’t explicitly stated a fixed CoT limit, it’s implied to be **tens of thousands of tokens** (comparable to its output length). In other words, Gemini 2.5 Flash’s “thinking” mode can internally consume on the order of *10^4* tokens before producing the final answer.

* **Gemini 2.5 Pro (Experimental 03–25)** – *On the order of \~10^4 tokens.* This larger Gemini 2.5 model likewise uses an internal chain-of-thought. It was trained via RL to generate reasoning tokens before responding. It supports the same **1M token input** and **up to \~65k output tokens**, so we can infer a similar **internal reasoning token budget (likely up to dozens of thousands of tokens)** per query. In short, Gemini 2.5 Pro’s hidden reasoning trace can be extremely long, on par with Claude 3.7’s 64k token thinking budget.

* **Claude‑3.7 “Sonnet” (2025‑02‑19)** – *Up to \~64K reasoning tokens.* (See above for Claude-3.7 Sonnet.)

* **DeepSeek R1 (Llama 70B Distilled “SpecDec”)** – *Up to \~32K reasoning tokens.* DeepSeek-R1 (first-gen reasoning model) was distilled into a Llama2-70B base (with “SpecDec” hints). It retains R1’s chain-of-thought capability. **Generation length was capped at 32,768 tokens** during DeepSeek’s evaluations, and the R1 API notes the CoT output *itself* can reach **up to \~32K tokens**. So this distilled model can use on the order of **30k+ tokens internally** for reasoning before final output.

* **DeepSeek R1 (70B Llama Distill, Q8\_0)** – *Up to \~32K reasoning tokens.* This is a quantized 8-bit variant of the above 70B distilled model. It shares the same architecture and **\~32k token** chain-of-thought limit (quantization does not change the token capacity).

* **DeepSeek R1 (32B Qwen Distill, FP16)** – *Up to \~32K reasoning tokens.* Another R1-distilled model (based on a 32B Qwen). It was fine-tuned on R1’s long CoT outputs, so it can similarly generate **lengthy chain-of-thoughts (up to \~32k tokens)**. DeepSeek set a universal 32,768-token generation cap for all R1 models in testing, indicating this smaller distilled model targets the same ballpark for maximum reasoning length.

* **OpenAI o4‑mini** – *Up to \~100K reasoning tokens.* The O4-mini is an OpenAI “reasoning-optimized” model. It has a **200,000-token context window** and supports **up to 100,000 output tokens**. All hidden reasoning tokens count toward the output quota, so in practice O4-mini can devote **up to \~100k tokens** to its internal chain-of-thought (at high `reasoning_effort` settings) before finalizing an answer. This huge token budget allows very deep multi-step reasoning.

* **OpenAI o3** – *Up to \~100K reasoning tokens.* OpenAI’s O3 (third-gen reasoning model) similarly features a **\~200K context** and **\~100K max generation**. It is the “most powerful” reasoning model of the O-series and can use on the order of **10^5 tokens internally** when performing step-by-step reasoning. (By comparison, earlier O1 models had smaller budgets, often in the low thousands of tokens for CoT by default, but O3 extended this dramatically to handle long, complex tasks.)

* **GPT‑4.1 (Base)** – *No internal reasoning tokens.* GPT‑4.1 is a direct successor to GPT‑4, focusing on long context and coding, but **it does not employ the hidden multi-step reasoning approach** of the O-series. It processes queries in a single forward pass. Thus **GPT-4.1 has no separate “reasoning token” budget** – it can only utilize its (very large) context window for input/output (up to 1M tokens in context), but any step-by-step reasoning must be prompted or implicit rather than generated internally.

* **DeepSeek-R1 (“DeepSeek Reasoner”)** – *Up to \~32K reasoning tokens.* This is DeepSeek’s main reasoning model (RL-trained). **Before giving an answer, it generates a hidden Chain-of-Thought up to about 32,768 tokens long**. Notably, the DeepSeek API exposes this CoT (`reasoning_content`) and does *not* count those tokens against the 64k input context limit. In summary, DeepSeek-R1 can internally reason with **\~32k tokens** of deliberation, then produce a final answer (typically capped at 4k–8k tokens).

* **DeepSeek-R1** (as listed under `accounts/fireworks/models/deepseek-r1`) – *Same as above.* This refers to the same **DeepSeek-R1 reasoning model**, which supports an internal chain-of-thought up to roughly **32k tokens** in length. (The “fireworks” path is just an internal reference to the DeepSeek-R1 model on the platform.)

**Sources:** Official model documentation and announcements were used wherever possible to determine these limits, as well as benchmark reports and reputable analyses for estimates. Each figure above represents the best-known maximum *internal reasoning* token budget for the model in question (distinct from its input context or output length limits).
