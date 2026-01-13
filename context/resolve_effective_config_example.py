# Example usage of resolve_effective_config
# This function is used after construct_paths to resolve strength, temperature, and time
# with proper priority: CLI > pddrc > defaults

from pdd.config_resolution import resolve_effective_config

# After calling construct_paths which returns resolved_config as the first element:
# resolved_config, input_strings, output_file_paths, detected_language = construct_paths(...)

# Call resolve_effective_config with:
#   - ctx: The click.Context object
#   - resolved_config: The config dict returned by construct_paths
#   - param_overrides: Optional dict of command-specific overrides

# Example without param_overrides (uses CLI and pddrc values):
effective_config = resolve_effective_config(ctx, resolved_config)
strength = effective_config["strength"]
temperature = effective_config["temperature"]
time = effective_config["time"]

# Example with param_overrides (when command accepts strength/temperature parameters):
effective_config = resolve_effective_config(
    ctx=ctx,
    resolved_config=resolved_config,
    param_overrides={"strength": strength_param, "temperature": temperature_param}
)
eff_strength = effective_config["strength"]
eff_temperature = effective_config["temperature"]
eff_time = effective_config["time"]
