# PDD Interactive Showcase Example

🚀 **Welcome to PDD's Interactive Showcase!** This example demonstrates how PDD (Prompt-Driven Development) can generate a complete interactive web application from simple configuration files.

## 🎯 What You'll Get

After running this example, you'll have:
- A beautiful, interactive HTML showcase of PDD capabilities
- Real-time cost calculator for PDD usage
- Interactive command playground
- Workflow visualization tools
- Responsive design that works on all devices

## 📋 Prerequisites

- Python 3.7+ installed on your system
- An OpenAI, Anthropic, or Gemini API key
- Basic familiarity with command line

## 🚀 Quick Start Guide

### Step 1: Clone the Repository

```bash
# Clone the PDD repository
git clone https://github.com/promptdriven/pdd.git
cd pdd/examples/pdd-showcase-interactive
```

### Step 2: Install PDD

**Quick Installation:**
```bash
pip install pdd-cli
```

**For detailed setup instructions and API key configuration, see the [main PDD README](../../README.md)**

**Configure your API key:**
```bash
# Run the interactive setup
pdd setup
```

### Step 3: Generate the Interactive Showcase

```bash
# Generate the complete interactive showcase
pdd sync index
```

**Expected output:**
```
✅ Generated index.html
✅ Integrated CSS styling
✅ Added JavaScript interactions
✅ Extracted content from documentation
```

### Step 4: View Your Interactive Showcase

**Option A: Open directly in browser**
```bash
open index.html  # macOS
# or
start index.html  # Windows
# or
xdg-open index.html  # Linux
```

**Option B: Use a local server (recommended)**
```bash
# Start a local server
python3 -m http.server 8080

# Then open http://localhost:8080 in your browser
```

## 🎉 What Gets Generated

After running `pdd sync index`, you'll see these new files:

```
pdd-showcase-interactive/
├── index.html          # 🆕 Complete interactive showcase
├── .pdd/              # 🆕 PDD metadata directory
│   ├── sync_log.json
│   └── generated_files.json
└── [existing source files...]
```

### Interactive Features:
- **Welcome Section**: "Welcome! This is PDD - The Next Big Thing"
- **Cost Calculator**: Real-time estimation of PDD usage costs
- **Command Playground**: Try PDD commands with live examples
- **Workflow Visualizer**: See how PDD processes work
- **Feature Gallery**: Interactive demonstrations of capabilities
- **Responsive Design**: Perfect on desktop, tablet, and mobile

## 🛠️ Troubleshooting

### Common Issues:

**❌ "API key not found" error**
```bash
# Solution: Run the setup again
pdd setup
# Make sure to enter a valid API key when prompted
```

**❌ "pdd command not found"**
```bash
# Solution: Install PDD
pip install pdd-cli
# or
pip3 install pdd-cli
```

**❌ Generation fails or produces empty files**
- Check your internet connection
- Verify your API key has sufficient credits
- Try running `pdd sync index` again

**❌ HTML file doesn't display correctly**
- Use a local server instead of opening the file directly
- Check browser console for any JavaScript errors

### Getting Help:
- 📖 [Main PDD Documentation](../../README.md)
- 🐛 [Report Issues](https://github.com/promptdriven/pdd/issues)
- 💬 [Community Discussions](https://github.com/promptdriven/pdd/discussions)

## 🏗️ Understanding the Architecture

This example showcases PDD's **Architecture-Driven Development** approach:

### Key Files (Source - You Push These):
- `architecture.json` - Orchestrates the entire generation process
- `PRD.md` - Defines what to build
- `tech_stack.md` - Specifies technologies to use
- `prompts/` - Specialized prompts for different components

### How It Works:
1. **Architecture Coordination**: `architecture.json` defines how different prompts work together
2. **Specialized Generation**: Each prompt handles a specific aspect (HTML, CSS, JS, content)
3. **Content Integration**: Automatically pulls data from main README and documentation
4. **Coordinated Output**: All components work together seamlessly

**Want to learn more?** Check out the [PDD Architecture Guide](../../docs/architecture.md)

## 🎯 Next Steps

### Customize This Example:
1. **Modify the content**: Edit `PRD.md` to change what gets built
2. **Update styling**: Modify `prompts/css_generator.md` for different designs
3. **Add features**: Extend `prompts/js_generator.md` for new interactions
4. **Change structure**: Update `architecture.json` to modify the workflow

### Explore More Examples:
- [Basic PDD Example](../basic-example/)
- [API Integration Example](../api-example/)
- [Multi-Page Application](../multi-page-app/)

### Join the Community:
- ⭐ [Star the repository](https://github.com/promptdriven/pdd)
- 🤝 [Contribute to PDD](../../CONTRIBUTING.md)
- 📢 [Share your creations](https://github.com/promptdriven/pdd/discussions)

## 📁 File Descriptions

| File | Purpose | Required |
|------|---------|----------|
| `PRD.md` | Product requirements and feature specifications | ✅ |
| `tech_stack.md` | Technology stack and implementation details | ✅ |
| `architecture.json` | PDD workflow orchestration and coordination | ✅ |
| `prompts/` | Specialized prompts for each component | ✅ |
| `README.md` | Documentation and usage instructions | ✅ |
| `index.html` | Generated interactive showcase (DO NOT PUSH) | ❌ |
| `.pdd/` | PDD metadata and cache (DO NOT PUSH) | ❌ |

## 🎉 Success Indicators

After running `pdd sync index`, you should see:
- ✅ `index.html` file created
- ✅ Interactive web page with PDD branding
- ✅ Working cost calculator and feature demos
- ✅ Responsive design across devices
- ✅ Professional, modern appearance

---

**🎊 Congratulations!** You've successfully generated an interactive showcase using PDD's architecture-driven development. This demonstrates how PDD can create complex, coordinated applications from simple configuration files.

*Happy coding with PDD! 🚀*