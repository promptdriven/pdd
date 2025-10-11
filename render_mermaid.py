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
    
    # Categorize modules by tags (frontend takes priority over backend)
    frontend = [m for m in architecture if any(t in m.get('tags', []) for t in ['frontend', 'react', 'nextjs', 'ui', 'page', 'component'])]
    backend = [m for m in architecture if m not in frontend and any(t in m.get('tags', []) for t in ['backend', 'api', 'database', 'sqlalchemy', 'fastapi'])]
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
    """Generate interactive HTML with hover tooltips."""
    
    # Create module data as JSON for tooltips
    module_data = {}
    for m in architecture:
        module_id = Path(m['filename']).stem
        module_data[module_id] = {
            'filename': m['filename'],
            'priority': m.get('priority', 'N/A'),
            'description': m.get('description', 'No description'),
            'dependencies': m.get('dependencies', []),
            'tags': m.get('tags', []),
            'filepath': m.get('filepath', '')
        }
    
    import json
    module_json = json.dumps(module_data)
    
    return f"""<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>{app_name}</title>
<script type="module">
import mermaid from 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs';
mermaid.initialize({{startOnLoad:true,theme:'default'}});

window.addEventListener('load', () => {{
    const moduleData = {module_json};
    
    // Add hover listeners to all nodes
    setTimeout(() => {{
        const nodes = document.querySelectorAll('.node');
        nodes.forEach(node => {{
            const text = node.querySelector('.nodeLabel');
            if (!text) return;
            
            const nodeText = text.textContent.trim();
            const moduleId = nodeText.split(' ')[0];
            const data = moduleData[moduleId];
            
            if (data) {{
                node.style.cursor = 'pointer';
                
                node.addEventListener('mouseenter', (e) => {{
                    showTooltip(e, data);
                }});
                
                node.addEventListener('mouseleave', () => {{
                    hideTooltip();
                }});
            }}
        }});
    }}, 500);
}});

function showTooltip(e, data) {{
    hideTooltip();
    
    const tooltip = document.createElement('div');
    tooltip.id = 'module-tooltip';
    tooltip.innerHTML = `
        <div style="font-weight:600;margin-bottom:8px;font-size:1.1em;">${{data.filename}}</div>
        <div style="margin-bottom:6px;"><strong>Priority:</strong> ${{data.priority}}</div>
        <div style="margin-bottom:6px;"><strong>Path:</strong> ${{data.filepath}}</div>
        <div style="margin-bottom:6px;"><strong>Tags:</strong> ${{data.tags.join(', ')}}</div>
        <div style="margin-bottom:6px;"><strong>Dependencies:</strong> ${{data.dependencies.length > 0 ? data.dependencies.join(', ') : 'None'}}</div>
        <div style="margin-top:8px;padding-top:8px;border-top:1px solid #ddd;font-size:0.9em;color:#444;">${{data.description}}</div>
    `;
    
    document.body.appendChild(tooltip);
    
    const rect = e.target.closest('.node').getBoundingClientRect();
    tooltip.style.left = rect.right + 10 + 'px';
    tooltip.style.top = rect.top + window.scrollY + 'px';
}}

function hideTooltip() {{
    const existing = document.getElementById('module-tooltip');
    if (existing) existing.remove();
}}
</script>
<style>
*{{margin:0;padding:0;box-sizing:border-box}}
body{{font-family:system-ui,sans-serif;background:#fff;color:#000;padding:2rem;max-width:1400px;margin:0 auto}}
h1{{font-size:2rem;font-weight:600;margin-bottom:2rem;padding-bottom:1rem;border-bottom:2px solid #000}}
.diagram{{border:1px solid #000;padding:2rem;margin:2rem 0;overflow-x:auto;position:relative}}
.mermaid{{display:flex;justify-content:center}}
#module-tooltip{{
    position:absolute;
    background:#fff;
    border:2px solid #000;
    padding:1rem;
    max-width:400px;
    z-index:1000;
    box-shadow:4px 4px 0 rgba(0,0,0,0.1);
    font-size:0.9rem;
    line-height:1.5;
}}
.node{{transition:opacity 0.2s}}
.node:hover{{opacity:0.8}}
</style></head><body>
<h1>{app_name}</h1>
<div class="diagram"><pre class="mermaid">{mermaid_code}</pre></div>
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

