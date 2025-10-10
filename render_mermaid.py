#!/usr/bin/env python3
"""
Render architecture.json as an interactive HTML Mermaid diagram.

Usage:
    python render_mermaid.py architecture.json "App Name" [output.html]

Features:
    - Direct browser rendering (no external tools)
    - Beautiful modern UI with statistics
    - Color-coded module categories
    - Interactive Mermaid diagram
    - Self-contained HTML (works offline)
"""

import json
import sys
from pathlib import Path


def generate_mermaid_code(architecture, app_name="System"):
    """Generate Mermaid flowchart code from architecture JSON."""
    lines = ["flowchart TB", f'    PRD["{app_name}"]', ""]
    
    # Categorize modules by tags
    frontend = [m for m in architecture if any(t in m.get('tags', []) for t in ['frontend', 'react', 'nextjs', 'ui', 'page', 'component'])]
    backend = [m for m in architecture if any(t in m.get('tags', []) for t in ['backend', 'api', 'database', 'sqlalchemy', 'fastapi'])]
    shared = [m for m in architecture if m not in frontend and m not in backend]
    
    # Generate subgraphs
    for group_name, modules in [("Frontend", frontend), ("Backend", backend), ("Shared", shared)]:
        if modules:
            lines.append(f"    subgraph {group_name}")
            for m in modules:
                name = Path(m['filename']).stem
                pri = m.get('priority', 0)
                lines.append(f'        {name}["{name} ({pri})"]')
            lines.append("    end\n")
    
    # PRD connections
    if frontend:
        lines.append("    PRD --> Frontend")
    if backend:
        lines.append("    PRD --> Backend")
    lines.append("")
    
    # Dependencies
    for m in architecture:
        src = Path(m['filename']).stem
        for dep in m.get('dependencies', []):
            dst = Path(dep).stem
            lines.append(f'    {src} -->|uses| {dst}')
    
    # Styles
    lines.extend(["", "    classDef frontend fill:#FFF3E0,stroke:#F57C00,stroke-width:2px",
                  "    classDef backend fill:#E3F2FD,stroke:#1976D2,stroke-width:2px",
                  "    classDef shared fill:#E8F5E9,stroke:#388E3C,stroke-width:2px",
                  "    classDef system fill:#E0E0E0,stroke:#616161,stroke-width:3px", ""])
    
    # Apply classes
    if frontend:
        lines.append(f"    class {','.join([Path(m['filename']).stem for m in frontend])} frontend")
    if backend:
        lines.append(f"    class {','.join([Path(m['filename']).stem for m in backend])} backend")
    if shared:
        lines.append(f"    class {','.join([Path(m['filename']).stem for m in shared])} shared")
    lines.append("    class PRD system")
    
    return "\n".join(lines)


def generate_html(mermaid_code, architecture, app_name):
    """Generate minimal black and white HTML with Mermaid diagram."""
    
    table_rows = []
    for m in sorted(architecture, key=lambda x: x.get('priority', 999)):
        deps = ', '.join(m.get('dependencies', [])) or '-'
        table_rows.append(f"""
            <tr>
                <td>{m.get('priority', '-')}</td>
                <td><strong>{m['filename']}</strong></td>
                <td>{', '.join(m.get('tags', []))}</td>
                <td>{deps}</td>
            </tr>""")
    
    return f"""<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>{app_name}</title>
<script type="module">
import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs';
mermaid.initialize({{startOnLoad:true,theme:'default'}});
</script>
<style>
*{{margin:0;padding:0;box-sizing:border-box}}
body{{font-family:system-ui,sans-serif;background:#fff;color:#000;padding:2rem;max-width:1400px;margin:0 auto}}
h1{{font-size:2rem;font-weight:600;margin-bottom:2rem;padding-bottom:1rem;border-bottom:2px solid #000}}
.diagram{{border:1px solid #000;padding:2rem;margin:2rem 0;overflow-x:auto}}
.mermaid{{display:flex;justify-content:center}}
h2{{font-size:1.5rem;font-weight:600;margin:2rem 0 1rem;border-bottom:1px solid #000;padding-bottom:0.5rem}}
table{{width:100%;border-collapse:collapse;border:1px solid #000;margin:1rem 0}}
th{{padding:0.75rem;text-align:left;font-weight:600;background:#f5f5f5;border:1px solid #000}}
td{{padding:0.75rem;border:1px solid #ddd}}
tbody tr:hover{{background:#f9f9f9}}
</style></head><body>
<h1>{app_name}</h1>
<div class="diagram"><pre class="mermaid">{mermaid_code}</pre></div>
<h2>Modules</h2>
<table><thead><tr><th>Priority</th><th>Module</th><th>Tags</th><th>Dependencies</th></tr></thead>
<tbody>{''.join(table_rows)}</tbody></table>
</body></html>"""


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python render_mermaid.py <architecture.json> [app_name] [output.html]")
        sys.exit(1)
    
    arch_file = sys.argv[1]
    app_name = sys.argv[2] if len(sys.argv) > 2 else "System Architecture"
    output_file = sys.argv[3] if len(sys.argv) > 3 else f"{Path(arch_file).stem}_diagram.html"
    
    with open(arch_file) as f:
        architecture = json.load(f)
    
    mermaid_code = generate_mermaid_code(architecture, app_name)
    html = generate_html(mermaid_code, architecture, app_name)
    
    with open(output_file, 'w') as f:
        f.write(html)
    
    print(f"✅ Generated: {output_file}")
    print(f"📊 Modules: {len(architecture)}")
    print(f"🌐 Open {output_file} in your browser!")

