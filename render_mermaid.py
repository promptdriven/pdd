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
    """Generate self-contained HTML with Mermaid diagram."""
    
    stats = {
        'total': len(architecture),
        'frontend': len([m for m in architecture if any(t in m.get('tags', []) for t in ['frontend', 'react', 'nextjs', 'ui'])]),
        'backend': len([m for m in architecture if any(t in m.get('tags', []) for t in ['backend', 'api', 'database'])]),
        'deps': sum(len(m.get('dependencies', [])) for m in architecture)
    }
    
    table_rows = []
    for m in sorted(architecture, key=lambda x: x.get('priority', 999)):
        table_rows.append(f"""
            <tr>
                <td><strong>{m['filename']}</strong></td>
                <td style="text-align:center;">{m.get('priority', 'N/A')}</td>
                <td>{m.get('description', '')}</td>
                <td><code>{', '.join(m.get('dependencies', [])) or 'None'}</code></td>
            </tr>""")
    
    return f"""<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>{app_name} - Architecture</title>
<script type="module">
import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs';
mermaid.initialize({{startOnLoad:true,theme:'default'}});
</script>
<style>
*{{margin:0;padding:0;box-sizing:border-box}}
body{{font-family:system-ui,sans-serif;background:linear-gradient(135deg,#667eea 0%,#764ba2 100%);min-height:100vh;padding:2rem}}
.container{{max-width:1400px;margin:0 auto;background:white;border-radius:16px;box-shadow:0 20px 60px rgba(0,0,0,0.3);overflow:hidden}}
.header{{background:linear-gradient(135deg,#667eea 0%,#764ba2 100%);color:white;padding:3rem 2rem;text-align:center}}
h1{{font-size:2.5rem;font-weight:700}}
.content{{padding:2rem}}
.stats{{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:1rem;margin:1.5rem 0}}
.stat{{background:linear-gradient(135deg,#667eea 0%,#764ba2 100%);color:white;padding:1.5rem;border-radius:8px;text-align:center}}
.stat-num{{font-size:2.5rem;font-weight:700;display:block}}
.stat-label{{font-size:0.9rem;opacity:0.9}}
.diagram{{background:#f9fafb;border-radius:12px;padding:2rem;margin:2rem 0;overflow-x:auto}}
.mermaid{{background:white;padding:2rem;border-radius:8px}}
h2{{font-size:1.75rem;margin:2rem 0 1rem;color:#111827;border-bottom:3px solid #667eea;padding-bottom:0.5rem}}
table{{width:100%;border-collapse:collapse;margin:1.5rem 0;box-shadow:0 1px 3px rgba(0,0,0,0.1);border-radius:8px;overflow:hidden}}
thead{{background:#667eea;color:white}}
th{{padding:1rem;text-align:left;font-weight:600}}
td{{padding:1rem;border-bottom:1px solid #e5e7eb}}
tbody tr:hover{{background:#f9fafb}}
code{{background:#f3f4f6;padding:0.2rem 0.4rem;border-radius:4px;font-size:0.9em}}
.legend{{display:flex;gap:1.5rem;flex-wrap:wrap;padding:1.5rem;background:#f9fafb;border-radius:8px;margin:1.5rem 0}}
.legend-item{{display:flex;align-items:center;gap:0.5rem}}
.legend-box{{width:24px;height:24px;border-radius:4px;border:2px solid}}
.fe{{background:#FFF3E0;border-color:#F57C00}}
.be{{background:#E3F2FD;border-color:#1976D2}}
.sh{{background:#E8F5E9;border-color:#388E3C}}
.sys{{background:#E0E0E0;border-color:#616161}}
</style></head><body>
<div class="container">
<div class="header"><h1>🏗️ {app_name}</h1><p>Architecture Visualization</p></div>
<div class="content">
<h2>📊 Statistics</h2>
<div class="stats">
<div class="stat"><span class="stat-num">{stats['total']}</span><span class="stat-label">TOTAL MODULES</span></div>
<div class="stat"><span class="stat-num">{stats['backend']}</span><span class="stat-label">BACKEND</span></div>
<div class="stat"><span class="stat-num">{stats['frontend']}</span><span class="stat-label">FRONTEND</span></div>
<div class="stat"><span class="stat-num">{stats['deps']}</span><span class="stat-label">DEPENDENCIES</span></div>
</div>
<h2>🎨 Legend</h2>
<div class="legend">
<div class="legend-item"><div class="legend-box fe"></div><span><strong>Frontend</strong> - React, Next.js, UI</span></div>
<div class="legend-item"><div class="legend-box be"></div><span><strong>Backend</strong> - APIs, Database, Services</span></div>
<div class="legend-item"><div class="legend-box sh"></div><span><strong>Shared</strong> - Utils, Common</span></div>
<div class="legend-item"><div class="legend-box sys"></div><span><strong>System</strong> - Application Root</span></div>
</div>
<h2>🗺️ Architecture Diagram</h2>
<div class="diagram"><pre class="mermaid">{mermaid_code}</pre></div>
<h2>📋 Module Details</h2>
<table><thead><tr><th>Module</th><th>Priority</th><th>Description</th><th>Dependencies</th></tr></thead>
<tbody>{''.join(table_rows)}</tbody></table>
<div style="text-align:center;padding:2rem;color:#6b7280;border-top:1px solid #e5e7eb">
<p>Generated by PDD Architecture Visualization Pipeline</p>
</div></div></div></body></html>"""


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

