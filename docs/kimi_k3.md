# Kimi K3

PDD supports Kimi K3 through Moonshot's direct China API:

```bash
pdd setup
# Choose "Add a provider", then "Moonshot AI", and save MOONSHOT_API_KEY.

PDD_MODEL_DEFAULT=moonshot/kimi-k3 pdd --local --time 1.0 generate prompt.prompt
```

The catalog pins K3 to `https://api.moonshot.cn/v1`. This is a per-model
endpoint; existing Moonshot models keep their existing LiteLLM endpoint.

K3 always reasons. PDD maps its generic `--time` scale to K3's supported
efforts as follows:

| PDD effort | K3 effort |
| --- | --- |
| low | low |
| medium | high |
| high | max |

Set `PDD_REASONING_EFFORT` to `low`, `high`, or `max` for an explicit
override. Other values fail before a provider request is made. K3 fixes
`temperature=1.0`, `top_p=0.95`, `n=1`, and both penalty values to zero, so
PDD intentionally omits those sampling fields instead of overriding them.

## Pricing normalization

Moonshot publishes K3 pricing in RMB: ¥2 per million cached input tokens, ¥20
per million uncached input tokens, and ¥100 per million output tokens. PDD's
current model catalog stores only USD input/output rates and has no cached
input tier. The K3 row therefore uses the uncached input price as a
conservative estimate and converts it, along with output, at the U.S. Federal
Reserve H.10 rate for 2026-07-17 (6.7760 CNY per USD):

- uncached input: `$2.951594` per million tokens
- output: `$14.757969` per million tokens

Sources: [Moonshot K3 pricing](https://platform.kimi.com/docs/pricing/chat-k3)
and the dated [Federal Reserve H.10 release for July 20,
2026](https://www.federalreserve.gov/releases/h10/20260720/).
The cached-input discount is not represented in cost estimates until the
catalog gains tiered input-pricing support.
