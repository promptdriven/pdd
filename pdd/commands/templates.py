"""
Templates command group.
"""
import io
import click
from rich import box
from rich.console import Console
from rich.table import Table
from rich.text import Text
from rich.markup import escape
from typing import Optional, List, Tuple, Any

from .. import template_registry
from ..core.errors import handle_error, custom_theme


def _echo_rich(*renderables):
    """Render Rich objects to plain text and output via click.echo (CliRunner-compatible)."""
    buf = io.StringIO()
    c = Console(file=buf, highlight=False, force_terminal=False, theme=custom_theme)
    for r in renderables:
        c.print(r)
    click.echo(buf.getvalue(), nl=False)

@click.group(name="templates")
def templates_group():
    """Manage packaged and project templates."""
    pass


@templates_group.command("list")
@click.option("--json", "as_json", is_flag=True, help="Output as JSON")
@click.option("--filter", "filter_tag", type=str, default=None, help="Filter by tag")
def templates_list(as_json: bool, filter_tag: Optional[str]):
    try:
        items = template_registry.list_templates(filter_tag)
        if as_json:
            import json as _json
            click.echo(_json.dumps(items, indent=2))
        else:
            if not items:
                _echo_rich("[info]No templates found.[/info]")
                return
            _echo_rich("[info]Available Templates:[/info]")
            for it in items:
                # Print the template name on its own line to avoid Rich wrapping
                name_line = Text(f"- {it['name']}", style="bold", no_wrap=True)
                _echo_rich(name_line)
                # Print details on the next line(s) with a small indent; wrapping is fine here
                version = it.get("version", "")
                description = it.get("description", "")
                tags = ", ".join(it.get("tags", []))
                details_parts = []
                if version:
                    details_parts.append(f"({version})")
                if description:
                    details_parts.append(description)
                if tags:
                    details_parts.append(f"[{tags}]")
                if details_parts:
                    _echo_rich("  " + " — ".join(details_parts))
    except Exception as e:
        handle_error(e, "templates list", False)


@templates_group.command("show")
@click.argument("name", type=str)
def templates_show(name: str):
    try:
        data = template_registry.show_template(name)
        summary = data.get("summary", {})

        def _render_key_value_table(title: Optional[str], items: List[Tuple[str, Any]], *, highlight_path: bool = False):
            """Render a 2-column Rich table for key/value pairs."""

            table = Table(show_header=False, box=box.SIMPLE, expand=True)
            table.add_column("Field", style="info", no_wrap=True)
            table.add_column("Value", overflow="fold")

            added_rows = False
            for label, value in items:
                if value in (None, "", [], {}):
                    continue
                if isinstance(value, (list, tuple)):
                    value_str = ", ".join(str(v) for v in value)
                else:
                    value_str = str(value)

                if highlight_path and label.lower() == "path":
                    value_markup = f"[path]{escape(value_str)}[/path]"
                else:
                    value_markup = escape(value_str)

                table.add_row(label, value_markup)
                added_rows = True

            if added_rows:
                if title:
                    _echo_rich(f"[info]{title}[/info]")
                _echo_rich(table)

        summary_items = [
            ("Name", summary.get("name")),
            ("Description", summary.get("description")),
            ("Version", summary.get("version")),
            ("Tags", summary.get("tags", [])),
            ("Language", summary.get("language")),
            ("Output", summary.get("output")),
            ("Path", summary.get("path")),
        ]
        _render_key_value_table("Template Summary:", summary_items, highlight_path=True)

        if data.get("variables"):
            _echo_rich("\n[info]Variables:[/info]")
            variables_table = Table(box=box.SIMPLE_HEAD, show_lines=False, expand=True)
            variables_table.add_column("Name", style="bold", no_wrap=True)
            variables_table.add_column("Required", style="info", no_wrap=True)
            variables_table.add_column("Type", no_wrap=True)
            variables_table.add_column("Description", overflow="fold")
            variables_table.add_column("Default/Examples", overflow="fold")

            for var_name, var_meta in data["variables"].items():
                required = var_meta.get("required")
                if required is True:
                    required_str = "Yes"
                elif required is False:
                    required_str = "No"
                else:
                    required_str = "-"

                var_type = escape(str(var_meta.get("type", "-")))
                description = escape(str(var_meta.get("description", "")))

                default_parts: List[str] = []
                default_value = var_meta.get("default")
                if default_value not in (None, ""):
                    default_parts.append(f"default: {default_value}")

                examples_value = var_meta.get("examples")
                if examples_value:
                    if isinstance(examples_value, (list, tuple)):
                        examples_str = ", ".join(str(example) for example in examples_value)
                    else:
                        examples_str = str(examples_value)
                    default_parts.append(f"examples: {examples_str}")

                example_paths_value = var_meta.get("example_paths")
                if example_paths_value:
                    if isinstance(example_paths_value, (list, tuple)):
                        example_paths_str = ", ".join(str(example) for example in example_paths_value)
                    else:
                        example_paths_str = str(example_paths_value)
                    default_parts.append(f"paths: {example_paths_str}")

                default_examples = "\n".join(default_parts) if default_parts else "-"

                variables_table.add_row(
                    escape(str(var_name)),
                    required_str,
                    var_type,
                    description,
                    escape(default_examples),
                )

            _echo_rich(variables_table)

        if data.get("usage"):
            _echo_rich("\n[info]Usage:[/info]")
            usage = data["usage"]
            if isinstance(usage, dict):
                for group_name, entries in usage.items():
                    _echo_rich(f"[bold]{escape(str(group_name))}[/bold]")
                    usage_table = Table(box=box.SIMPLE, show_lines=False, expand=True)
                    usage_table.add_column("Name", style="bold", no_wrap=True)
                    usage_table.add_column("Command", overflow="fold")

                    if isinstance(entries, (list, tuple)):
                        iterable_entries = entries
                    else:
                        iterable_entries = [entries]

                    for entry in iterable_entries:
                        if isinstance(entry, dict):
                            name_value = escape(str(entry.get("name", "")))
                            command_value = escape(str(entry.get("command", "")))
                        else:
                            name_value = "-"
                            command_value = escape(str(entry))
                        usage_table.add_row(name_value, f"[command]{command_value}[/command]")

                    if usage_table.row_count:
                        _echo_rich(usage_table)
            else:
                _echo_rich(usage)

        if data.get("discover"):
            _echo_rich("\n[info]Discover:[/info]")
            discover = data["discover"]
            if isinstance(discover, dict):
                discover_items = [(str(key), value) for key, value in discover.items()]
                _render_key_value_table(None, discover_items)
            else:
                _echo_rich(discover)
        if data.get("output_schema"):
            _echo_rich("\n[info]Output Schema:[/info]")
            try:
                import json as _json
                _echo_rich(_json.dumps(data["output_schema"], indent=2))
            except Exception:
                _echo_rich(str(data["output_schema"]))
        if data.get("notes"):
            _echo_rich("\n[info]Notes:[/info]")
            _echo_rich(data["notes"])  # plain text
    except Exception as e:
        handle_error(e, "templates show", False)


@templates_group.command("copy")
@click.argument("name", type=str)
@click.option("--to", "dest_dir", type=click.Path(file_okay=False), required=True)
def templates_copy(name: str, dest_dir: str):
    try:
        dest = template_registry.copy_template(name, dest_dir)
        _echo_rich(f"[success]Copied to:[/success] {dest}")
    except Exception as e:
        handle_error(e, "templates copy", False)
