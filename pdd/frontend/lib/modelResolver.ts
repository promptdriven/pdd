import { ModelInfo } from '../api';

/**
 * Full model catalog from data/llm_model.csv.
 * Used for the strength slider so all cloud models are selectable
 * regardless of the user's local llm_model.csv configuration.
 */
export const ALL_MODELS: ModelInfo[] = [
  { model: 'openai/mlx-community/Qwen3-30B-A3B-4bit', provider: 'OpenAI', input_cost: 0, output_cost: 0, elo: 1040, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'none', structured_output: false },
  { model: 'lm_studio/openai-gpt-oss-120b-mlx-6', provider: 'lm_studio', input_cost: 0.0001, output_cost: 0, elo: 1082, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'gpt-5-nano', provider: 'OpenAI', input_cost: 0.05, output_cost: 0.4, elo: 1249, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'none', structured_output: true },
  { model: 'anthropic/claude-haiku-4-5-20251001', provider: 'Anthropic', input_cost: 1.0, output_cost: 5.0, elo: 1270, context_limit: 200000, max_thinking_tokens: 128000, reasoning_type: 'budget', structured_output: true },
  { model: 'gpt-5.1-codex-mini', provider: 'OpenAI', input_cost: 0.25, output_cost: 2.0, elo: 1325, context_limit: 200000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'groq/moonshotai/kimi-k2-instruct-0905', provider: 'OpenAI', input_cost: 1.0, output_cost: 3.0, elo: 1330, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'none', structured_output: true },
  { model: 'fireworks_ai/accounts/fireworks/models/qwen3-coder-480b-a35b-instruct', provider: 'Fireworks', input_cost: 0.45, output_cost: 1.80, elo: 1363, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'none', structured_output: false },
  { model: 'anthropic/claude-sonnet-4-5-20250929', provider: 'Anthropic', input_cost: 3.0, output_cost: 15.0, elo: 1370, context_limit: 200000, max_thinking_tokens: 128000, reasoning_type: 'budget', structured_output: true },
  { model: 'vertex_ai/claude-sonnet-4-5', provider: 'Google', input_cost: 3.0, output_cost: 15.0, elo: 1370, context_limit: 200000, max_thinking_tokens: 128000, reasoning_type: 'budget', structured_output: true },
  { model: 'vertex_ai/gemini-3-flash-preview', provider: 'Google', input_cost: 0.50, output_cost: 3.0, elo: 1430, context_limit: 1000000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'vertex_ai/deepseek-ai/deepseek-v3.2-maas', provider: 'Google', input_cost: 0.28, output_cost: 0.42, elo: 1450, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'vertex_ai/claude-opus-4-5', provider: 'Google', input_cost: 5.0, output_cost: 25.0, elo: 1465, context_limit: 200000, max_thinking_tokens: 128000, reasoning_type: 'budget', structured_output: true },
  { model: 'anthropic/claude-opus-4-5-20251101', provider: 'Anthropic', input_cost: 5.0, output_cost: 25.0, elo: 1474, context_limit: 200000, max_thinking_tokens: 128000, reasoning_type: 'budget', structured_output: true },
  { model: 'gpt-5.1-codex', provider: 'OpenAI', input_cost: 1.25, output_cost: 10.0, elo: 1478, context_limit: 200000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'gpt-5.1-codex-max', provider: 'OpenAI', input_cost: 1.25, output_cost: 10.0, elo: 1480, context_limit: 200000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'fireworks_ai/accounts/fireworks/models/glm-4p7', provider: 'Fireworks', input_cost: 0.60, output_cost: 2.20, elo: 1481, context_limit: 128000, max_thinking_tokens: 0, reasoning_type: 'none', structured_output: false },
  { model: 'gpt-5.2', provider: 'OpenAI', input_cost: 1.75, output_cost: 14.0, elo: 1486, context_limit: 200000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'gemini/gemini-3-pro-preview', provider: 'Google', input_cost: 1.25, output_cost: 10.0, elo: 1487, context_limit: 1000000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
  { model: 'vertex_ai/gemini-3-pro-preview', provider: 'Google', input_cost: 1.25, output_cost: 10.0, elo: 1487, context_limit: 1000000, max_thinking_tokens: 0, reasoning_type: 'effort', structured_output: true },
];

/**
 * Resolve which model to use based on the strength slider value.
 * Models are sorted by ELO (ascending) and evenly distributed across [0, 1].
 * Every model is reachable at a distinct slider position.
 *
 * strength 0 → weakest/cheapest model
 * strength 1 → strongest/highest ELO model
 */
export function resolveModelForStrength(models: ModelInfo[], strength: number): ModelInfo | null {
  if (models.length === 0) return null;
  if (models.length === 1) return models[0];

  // Sort by ELO ascending (weakest first, strongest last)
  const sorted = [...models].sort((a, b) => a.elo - b.elo);

  // Map strength [0, 1] to index [0, N-1]
  const index = Math.round(strength * (sorted.length - 1));
  return sorted[Math.min(index, sorted.length - 1)];
}
