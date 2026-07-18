"""Command registration module with deferred handler imports."""
import click


_COMMANDS = {
    "generate": ("pdd.commands.generate", "generate"),
    "test": ("pdd.commands.generate", "test"),
    "example": ("pdd.commands.generate", "example"),
    "fix": ("pdd.commands.fix", "fix"),
    "split": ("pdd.commands.modify", "split"),
    "change": ("pdd.commands.modify", "change"),
    "update": ("pdd.commands.modify", "update"),
    "sync": ("pdd.commands.maintenance", "sync"),
    "sync-architecture": ("pdd.commands.maintenance", "sync_architecture"),
    "checkup": ("pdd.commands.checkup", "checkup"),
    "contracts": ("pdd.commands.contracts", "contracts_cli"),
    "auto-deps": ("pdd.commands.maintenance", "auto_deps"),
    "setup": ("pdd.commands.maintenance", "setup"),
    "detect": ("pdd.commands.analysis", "detect_change"),
    "conflicts": ("pdd.commands.analysis", "conflicts"),
    "bug": ("pdd.commands.analysis", "bug"),
    "crash": ("pdd.commands.analysis", "crash"),
    "trace": ("pdd.commands.analysis", "trace"),
    "preprocess": ("pdd.commands.misc", "preprocess"),
    "extracts": ("pdd.commands.extracts", "extracts"),
    "report-core": ("pdd.commands.report", "report_core"),
    "replay": ("pdd.commands.replay", "replay"),
    "context": ("pdd.commands.context", "context"),
    "install_completion": ("pdd.commands.utility", "install_completion_cmd"),
    "verify": ("pdd.commands.utility", "verify"),
    "which": ("pdd.commands.which", "which"),
    "reconcile": ("pdd.commands.reconcile", "reconcile"),
    "install-hooks": ("pdd.commands.reconcile", "install_hooks"),
    "certify": ("pdd.commands.sync_core", "certify"),
    "recover": ("pdd.commands.sync_core", "recover"),
    "baseline": ("pdd.commands.sync_core", "baseline"),
    "validate": ("pdd.commands.sync_core", "validate"),
    "templates": ("pdd.commands.templates", "templates_group"),
    "connect": ("pdd.commands.connect", "connect"),
    "auth": ("pdd.commands.auth", "auth_group"),
    "sessions": ("pdd.commands.sessions", "sessions"),
    "firecrawl-cache": ("pdd.commands.firecrawl", "firecrawl_cache_group"),
    "story": ("pdd.commands.story", "story"),
}

def register_commands(cli: click.Group) -> None:
    """Register subcommands without importing their implementation modules."""
    cli._lazy_commands = dict(_COMMANDS)  # type: ignore[attr-defined]
