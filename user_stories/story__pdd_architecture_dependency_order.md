<!-- pdd-story-prompts: prompts/architecture_sync_python.prompt, prompts/sync_order_python.prompt, prompts/architecture_registry_python.prompt, prompts/metadata_sync_python.prompt -->
<!-- pdd-story-dev-units: architecture_sync_python.prompt, sync_order_python.prompt, architecture_registry_python.prompt, metadata_sync_python.prompt -->

# User Story: Architecture order drives safe sync

## Story

As a PDD maintainer changing related prompts, I want architecture metadata to determine a stable dependency-aware generation order, so that sync and regeneration do not update dependent units before their sources are known.
