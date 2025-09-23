# HTML Structure Generation Prompt

## Objective

Generate a complete, self-contained HTML5 document that serves as an interactive showcase for Prompt-Driven Development (PDD). This single file should demonstrate PDD's capabilities, philosophy, and benefits through an engaging web experience.

## Core Requirements

### Document Structure
- Create a complete HTML5 document with proper DOCTYPE and semantic structure
- Include all necessary meta tags for SEO, accessibility, and responsive design
- Embed all CSS styles within a `<style>` tag in the `<head>`
- Embed all JavaScript within a `<script>` tag before the closing `</body>`
- Ensure the document is completely self-contained with no external dependencies

### Content Sections

Create the following main sections in order:

1. **Hero Section**
   - Prominent headline: "Welcome! This is PDD - The Next Big Thing"
   - Compelling subtitle about revolutionizing software development
   - Brief explanation of the maintenance burden problem (80-90% costs)
   - Call-to-action buttons for key sections
   - Visual element representing the PDD workflow

2. **Problem Statement**
   - Highlight the traditional development maintenance burden
   - Visual representation of legacy code accumulation
   - Statistics from the whitepaper about development costs
   - Pain points of interactive AI patching

3. **PDD Solution**
   - Core concept: "Prompts as Source of Truth"
   - Regenerative development explanation
   - Batch vs Interactive efficiency comparison
   - Synchronization and feedback loop benefits

4. **Core Principles** (Interactive)
   - 6 fundamental principles with expandable details:
     1. Prompts as the Source of Truth
     2. Regenerative Development
     3. Intent Preservation
     4. Modularity
     5. Synchronization
     6. Batch-Oriented Workflow
   - Each principle should have a clickable card with detailed explanation

5. **Benefits Showcase**
   - Cost savings with interactive calculator
   - Developer efficiency improvements
   - Code quality enhancements
   - Collaboration benefits
   - LLM usage optimization

6. **PDD Commands Demo**
   - Interactive command explorer
   - Key commands: `pdd sync`, `pdd generate`, `pdd test`, `pdd fix`, `pdd verify`
   - Simulated terminal interface
   - Syntax highlighting for examples

7. **Workflow Visualization**
   - Interactive flowchart of PDD development cycle
   - Clickable workflow steps
   - Progress animations
   - Detailed explanations for each step

8. **Case Studies & Benchmarks**
   - Performance comparisons from whitepaper
   - Success metrics and statistics
   - Cost-effectiveness demonstrations
   - Real-world application examples

9. **Getting Started**
   - Installation instructions for different platforms
   - Quick start guide
   - Links to documentation and examples
   - Community and support information

### Interactive Features

Include placeholders and structure for:

1. **Cost Calculator**
   - Form inputs for project parameters
   - Real-time calculation display
   - Visual charts showing savings
   - Comparison tables

2. **Command Playground**
   - Simulated terminal interface
   - Interactive command examples
   - Syntax highlighting
   - Output simulation

3. **Workflow Simulator**
   - Step-by-step process walkthrough
   - Interactive decision points
   - Progress indicators
   - Animated transitions

4. **Animated Diagrams**
   - SVG-based flowcharts
   - Interactive hover states
   - Progressive disclosure
   - Smooth animations

### Technical Specifications

#### HTML5 Semantic Structure
```html
<!DOCTYPE html>
<html lang="en">
<head>
  <!-- Meta tags, title, and embedded CSS -->
</head>
<body>
  <header>
    <nav><!-- Navigation --></nav>
  </header>
  
  <main>
    <section id="hero"><!-- Hero section --></section>
    <section id="problem"><!-- Problem statement --></section>
    <section id="solution"><!-- PDD solution --></section>
    <section id="principles"><!-- Core principles --></section>
    <section id="benefits"><!-- Benefits showcase --></section>
    <section id="commands"><!-- Commands demo --></section>
    <section id="workflow"><!-- Workflow visualization --></section>
    <section id="case-studies"><!-- Case studies --></section>
    <section id="getting-started"><!-- Getting started --></section>
  </main>
  
  <footer>
    <!-- Footer content -->
  </footer>
  
  <!-- Embedded JavaScript -->
</body>
</html>
```

#### Accessibility Requirements
- Proper heading hierarchy (h1, h2, h3, etc.)
- ARIA labels and roles for interactive elements
- Alt text for all images and visual elements
- Keyboard navigation support
- Screen reader compatibility
- High contrast mode support
- Focus management for interactive elements

#### SEO Optimization
- Title: "PDD - Prompt-Driven Development | The Next Big Thing in Software Development"
- Meta description highlighting PDD's benefits
- Structured data markup for software application
- Open Graph tags for social sharing
- Canonical URL and language declarations

#### Responsive Design Structure
- Mobile-first approach with progressive enhancement
- Flexible grid system using CSS Grid and Flexbox
- Responsive images and media
- Touch-friendly interactive elements
- Optimized typography scaling

### Content Integration

Extract and integrate key information from:

#### From README.md:
- Installation instructions and prerequisites
- Command descriptions and usage examples
- Supported programming languages
- Configuration and setup details
- Troubleshooting information
- Version and update information

#### From Whitepaper:
- Core philosophy and principles
- Maintenance burden statistics (80-90% costs)
- Comparison with traditional approaches
- Benefits and advantages
- Workflow descriptions
- Case studies and benchmarks
- Performance metrics

### Design System Integration

Use the following design tokens:

#### Colors
- Primary: #1e40af (Deep Blue)
- Secondary: #10b981 (Emerald Green)
- Accent: #f59e0b (Amber)
- Neutral scale: #f9fafb to #111827

#### Typography
- Font family: system-ui, -apple-system, sans-serif
- Scale: 0.75rem to 2.25rem
- Line heights: 1.2 to 1.8

#### Spacing
- Scale: 0.25rem, 0.5rem, 1rem, 2rem, 4rem, 8rem
- Consistent margins and padding

### Performance Considerations

- Optimize for file size under 500KB
- Minimize DOM complexity
- Use efficient CSS selectors
- Implement lazy loading for heavy content
- Optimize images and assets
- Ensure smooth 60fps animations

### Browser Compatibility

- Target modern browsers (Chrome 90+, Firefox 88+, Safari 14+, Edge 90+)
- Progressive enhancement for older browsers
- Feature detection for advanced capabilities
- Graceful degradation of interactive features

## Expected Output

A complete, production-ready HTML file that:

1. **Demonstrates PDD Excellence**: Shows the quality and attention to detail that PDD enables
2. **Educates Visitors**: Clearly explains PDD concepts and benefits
3. **Engages Users**: Provides interactive elements that enhance understanding
4. **Performs Well**: Loads quickly and runs smoothly on all devices
5. **Accessible**: Works for all users regardless of abilities or assistive technologies
6. **Self-Contained**: Requires no external resources or dependencies

The final HTML file should serve as both a marketing tool for PDD and a demonstration of what PDD can accomplish - a perfect meta-example of the technology creating its own showcase.

## Success Criteria

- [ ] Complete HTML5 document with semantic structure
- [ ] All content sections implemented with proper hierarchy
- [ ] Interactive features have proper HTML structure
- [ ] Accessibility compliance (WCAG 2.1 AA)
- [ ] SEO optimization with proper meta tags
- [ ] Responsive design structure
- [ ] Performance-optimized markup
- [ ] Self-contained with embedded assets
- [ ] Professional, modern appearance
- [ ] Clear, compelling messaging about PDD

This HTML structure will serve as the foundation for the complete PDD Interactive Showcase, demonstrating how PDD can create sophisticated, professional web applications through its architecture-driven approach.