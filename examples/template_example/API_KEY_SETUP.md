# API Key Setup for PDD

This guide shows common ways to provide LLM provider credentials while running
the template example.

## Required Environment Variables

Set the variables required by the model provider you plan to use:

- `ANTHROPIC_API_KEY`
- `OPENAI_API_KEY`
- `GEMINI_API_KEY`
- `GOOGLE_API_KEY`
- `VERTEX_AI_PROJECT`
- `VERTEX_AI_LOCATION`
- `GOOGLE_APPLICATION_CREDENTIALS`

Optional provider keys include `GROQ_API_KEY`, `TOGETHER_API_KEY`,
`DEEPSEEK_API_KEY`, `CEREBRAS_API_KEY`, `XAI_API_KEY`, and
`FIREWORKS_API_KEY`.

## Usage

Export keys in your shell before running the workflow:

```bash
export OPENAI_API_KEY="your-key"
make USE_FORCE=yes sync_all
```

For a single command, pass the key inline:

```bash
OPENAI_API_KEY="your-key" make USE_FORCE=yes sync_all
```

You can also use the example Makefile's `COMMAND_PREFIX` hook:

```bash
make COMMAND_PREFIX="env OPENAI_API_KEY=your-key" USE_FORCE=yes sync_all
```
