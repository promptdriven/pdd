# CSS Styles Generation Prompt

## Objective

Generate comprehensive CSS styles for the PDD Interactive Showcase that creates a modern, professional, and highly interactive web experience. The styles should be embedded within the HTML document and provide a complete design system with responsive layouts, smooth animations, and accessibility features.

## Design Philosophy

### Visual Identity
- **Modern & Professional**: Clean, sophisticated design that reflects PDD's innovation
- **Trustworthy**: Deep blues and stable grays to convey reliability
- **Innovative**: Emerald greens and amber accents to suggest growth and energy
- **Accessible**: High contrast, clear typography, and inclusive design

### User Experience Principles
- **Progressive Disclosure**: Information revealed as needed
- **Smooth Interactions**: 60fps animations with hardware acceleration
- **Responsive Design**: Mobile-first approach with seamless scaling
- **Performance**: Optimized for fast loading and smooth scrolling

## Design System

### Color Palette
```css
:root {
  /* Primary Colors */
  --color-primary: #1e40af;        /* Deep Blue - Trust & Professionalism */
  --color-primary-light: #3b82f6;  /* Lighter Blue */
  --color-primary-dark: #1e3a8a;   /* Darker Blue */
  
  /* Secondary Colors */
  --color-secondary: #10b981;      /* Emerald Green - Growth & Innovation */
  --color-secondary-light: #34d399; /* Lighter Green */
  --color-secondary-dark: #059669;  /* Darker Green */
  
  /* Accent Colors */
  --color-accent: #f59e0b;         /* Amber - Energy & Attention */
  --color-accent-light: #fbbf24;   /* Lighter Amber */
  --color-accent-dark: #d97706;    /* Darker Amber */
  
  /* Neutral Colors */
  --color-neutral-50: #f9fafb;
  --color-neutral-100: #f3f4f6;
  --color-neutral-200: #e5e7eb;
  --color-neutral-300: #d1d5db;
  --color-neutral-400: #9ca3af;
  --color-neutral-500: #6b7280;
  --color-neutral-600: #4b5563;
  --color-neutral-700: #374151;
  --color-neutral-800: #1f2937;
  --color-neutral-900: #111827;
  
  /* Semantic Colors */
  --color-success: #10b981;
  --color-warning: #f59e0b;
  --color-error: #ef4444;
  --color-info: #3b82f6;
}
```

### Typography System
```css
:root {
  /* Font Families */
  --font-primary: system-ui, -apple-system, 'Segoe UI', Roboto, sans-serif;
  --font-mono: 'SF Mono', Monaco, 'Cascadia Code', 'Roboto Mono', monospace;
  
  /* Font Sizes */
  --text-xs: 0.75rem;      /* 12px */
  --text-sm: 0.875rem;     /* 14px */
  --text-base: 1rem;       /* 16px */
  --text-lg: 1.125rem;     /* 18px */
  --text-xl: 1.25rem;      /* 20px */
  --text-2xl: 1.5rem;      /* 24px */
  --text-3xl: 1.875rem;    /* 30px */
  --text-4xl: 2.25rem;     /* 36px */
  --text-5xl: 3rem;        /* 48px */
  --text-6xl: 3.75rem;     /* 60px */
  
  /* Line Heights */
  --leading-tight: 1.25;
  --leading-normal: 1.5;
  --leading-relaxed: 1.75;
  
  /* Font Weights */
  --font-light: 300;
  --font-normal: 400;
  --font-medium: 500;
  --font-semibold: 600;
  --font-bold: 700;
}
```

### Spacing System
```css
:root {
  /* Spacing Scale */
  --space-1: 0.25rem;   /* 4px */
  --space-2: 0.5rem;    /* 8px */
  --space-3: 0.75rem;   /* 12px */
  --space-4: 1rem;      /* 16px */
  --space-5: 1.25rem;   /* 20px */
  --space-6: 1.5rem;    /* 24px */
  --space-8: 2rem;      /* 32px */
  --space-10: 2.5rem;   /* 40px */
  --space-12: 3rem;     /* 48px */
  --space-16: 4rem;     /* 64px */
  --space-20: 5rem;     /* 80px */
  --space-24: 6rem;     /* 96px */
  --space-32: 8rem;     /* 128px */
}
```

### Breakpoints
```css
:root {
  --breakpoint-sm: 640px;
  --breakpoint-md: 768px;
  --breakpoint-lg: 1024px;
  --breakpoint-xl: 1280px;
  --breakpoint-2xl: 1536px;
}
```

## Layout System

### Base Styles
```css
/* Reset and Base Styles */
*, *::before, *::after {
  box-sizing: border-box;
  margin: 0;
  padding: 0;
}

html {
  scroll-behavior: smooth;
  font-size: 16px;
}

body {
  font-family: var(--font-primary);
  font-size: var(--text-base);
  line-height: var(--leading-normal);
  color: var(--color-neutral-900);
  background-color: var(--color-neutral-50);
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
}
```

### Container System
```css
.container {
  width: 100%;
  max-width: 1280px;
  margin: 0 auto;
  padding: 0 var(--space-4);
}

@media (min-width: 640px) {
  .container { padding: 0 var(--space-6); }
}

@media (min-width: 1024px) {
  .container { padding: 0 var(--space-8); }
}
```

### Grid System
```css
.grid {
  display: grid;
  gap: var(--space-6);
}

.grid-cols-1 { grid-template-columns: repeat(1, 1fr); }
.grid-cols-2 { grid-template-columns: repeat(2, 1fr); }
.grid-cols-3 { grid-template-columns: repeat(3, 1fr); }
.grid-cols-4 { grid-template-columns: repeat(4, 1fr); }

@media (min-width: 768px) {
  .md\:grid-cols-2 { grid-template-columns: repeat(2, 1fr); }
  .md\:grid-cols-3 { grid-template-columns: repeat(3, 1fr); }
}

@media (min-width: 1024px) {
  .lg\:grid-cols-3 { grid-template-columns: repeat(3, 1fr); }
  .lg\:grid-cols-4 { grid-template-columns: repeat(4, 1fr); }
}
```

## Component Styles

### Navigation Header
```css
header {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  z-index: 1000;
  background: rgba(255, 255, 255, 0.95);
  backdrop-filter: blur(10px);
  border-bottom: 1px solid var(--color-neutral-200);
  transition: all 0.3s ease;
}

nav {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--space-4) 0;
}

.nav-links {
  display: flex;
  gap: var(--space-6);
  list-style: none;
}

.nav-link {
  color: var(--color-neutral-700);
  text-decoration: none;
  font-weight: var(--font-medium);
  transition: color 0.2s ease;
}

.nav-link:hover {
  color: var(--color-primary);
}
```

### Hero Section
```css
#hero {
  min-height: 100vh;
  display: flex;
  align-items: center;
  background: linear-gradient(135deg, var(--color-primary) 0%, var(--color-secondary) 100%);
  color: white;
  text-align: center;
  position: relative;
  overflow: hidden;
}

.hero-content {
  position: relative;
  z-index: 2;
}

.hero-title {
  font-size: var(--text-5xl);
  font-weight: var(--font-bold);
  margin-bottom: var(--space-6);
  line-height: var(--leading-tight);
}

@media (min-width: 768px) {
  .hero-title {
    font-size: var(--text-6xl);
  }
}

.hero-subtitle {
  font-size: var(--text-xl);
  margin-bottom: var(--space-8);
  opacity: 0.9;
  max-width: 600px;
  margin-left: auto;
  margin-right: auto;
}
```

### Interactive Cards
```css
.card {
  background: white;
  border-radius: 12px;
  padding: var(--space-6);
  box-shadow: 0 4px 6px rgba(0, 0, 0, 0.05);
  border: 1px solid var(--color-neutral-200);
  transition: all 0.3s ease;
  cursor: pointer;
}

.card:hover {
  transform: translateY(-4px);
  box-shadow: 0 12px 24px rgba(0, 0, 0, 0.1);
  border-color: var(--color-primary);
}

.card-title {
  font-size: var(--text-lg);
  font-weight: var(--font-semibold);
  color: var(--color-neutral-900);
  margin-bottom: var(--space-3);
}

.card-description {
  color: var(--color-neutral-600);
  line-height: var(--leading-relaxed);
}
```

### Buttons
```css
.btn {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  padding: var(--space-3) var(--space-6);
  border-radius: 8px;
  font-weight: var(--font-medium);
  text-decoration: none;
  border: none;
  cursor: pointer;
  transition: all 0.2s ease;
  font-size: var(--text-base);
}

.btn-primary {
  background: var(--color-primary);
  color: white;
}

.btn-primary:hover {
  background: var(--color-primary-dark);
  transform: translateY(-1px);
}

.btn-secondary {
  background: var(--color-secondary);
  color: white;
}

.btn-secondary:hover {
  background: var(--color-secondary-dark);
  transform: translateY(-1px);
}

.btn-outline {
  background: transparent;
  color: var(--color-primary);
  border: 2px solid var(--color-primary);
}

.btn-outline:hover {
  background: var(--color-primary);
  color: white;
}
```

### Cost Calculator
```css
.calculator {
  background: white;
  border-radius: 16px;
  padding: var(--space-8);
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.1);
}

.calculator-input {
  width: 100%;
  padding: var(--space-3);
  border: 2px solid var(--color-neutral-200);
  border-radius: 8px;
  font-size: var(--text-base);
  transition: border-color 0.2s ease;
}

.calculator-input:focus {
  outline: none;
  border-color: var(--color-primary);
  box-shadow: 0 0 0 3px rgba(30, 64, 175, 0.1);
}

.calculator-result {
  background: linear-gradient(135deg, var(--color-secondary), var(--color-secondary-light));
  color: white;
  padding: var(--space-6);
  border-radius: 12px;
  text-align: center;
}

.savings-amount {
  font-size: var(--text-3xl);
  font-weight: var(--font-bold);
  margin-bottom: var(--space-2);
}
```

### Command Playground
```css
.terminal {
  background: var(--color-neutral-900);
  color: var(--color-neutral-100);
  border-radius: 12px;
  padding: var(--space-6);
  font-family: var(--font-mono);
  font-size: var(--text-sm);
  overflow-x: auto;
}

.terminal-header {
  display: flex;
  align-items: center;
  margin-bottom: var(--space-4);
  padding-bottom: var(--space-3);
  border-bottom: 1px solid var(--color-neutral-700);
}

.terminal-dots {
  display: flex;
  gap: var(--space-2);
}

.terminal-dot {
  width: 12px;
  height: 12px;
  border-radius: 50%;
}

.terminal-dot:nth-child(1) { background: #ff5f57; }
.terminal-dot:nth-child(2) { background: #ffbd2e; }
.terminal-dot:nth-child(3) { background: #28ca42; }

.command-line {
  display: flex;
  align-items: center;
  margin-bottom: var(--space-2);
}

.command-prompt {
  color: var(--color-secondary);
  margin-right: var(--space-2);
}

.command-text {
  color: var(--color-neutral-100);
}

.syntax-highlight .keyword { color: #ff79c6; }
.syntax-highlight .string { color: #f1fa8c; }
.syntax-highlight .comment { color: #6272a4; }
```

### Workflow Visualization
```css
.workflow-container {
  position: relative;
  padding: var(--space-8);
}

.workflow-step {
  display: flex;
  align-items: center;
  padding: var(--space-4);
  background: white;
  border-radius: 12px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
  margin-bottom: var(--space-4);
  cursor: pointer;
  transition: all 0.3s ease;
}

.workflow-step:hover {
  transform: translateX(8px);
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.15);
}

.workflow-step.active {
  background: linear-gradient(135deg, var(--color-primary), var(--color-primary-light));
  color: white;
}

.step-number {
  width: 40px;
  height: 40px;
  border-radius: 50%;
  background: var(--color-primary);
  color: white;
  display: flex;
  align-items: center;
  justify-content: center;
  font-weight: var(--font-bold);
  margin-right: var(--space-4);
}

.step-content h3 {
  font-size: var(--text-lg);
  font-weight: var(--font-semibold);
  margin-bottom: var(--space-1);
}

.step-content p {
  color: var(--color-neutral-600);
  font-size: var(--text-sm);
}
```

## Animation System

### Keyframes
```css
@keyframes fadeInUp {
  from {
    opacity: 0;
    transform: translateY(30px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

@keyframes slideInLeft {
  from {
    opacity: 0;
    transform: translateX(-30px);
  }
  to {
    opacity: 1;
    transform: translateX(0);
  }
}

@keyframes pulse {
  0%, 100% {
    transform: scale(1);
  }
  50% {
    transform: scale(1.05);
  }
}

@keyframes typing {
  from { width: 0; }
  to { width: 100%; }
}

@keyframes blink {
  50% { border-color: transparent; }
}
```

### Animation Classes
```css
.animate-fade-in-up {
  animation: fadeInUp 0.6s ease-out;
}

.animate-slide-in-left {
  animation: slideInLeft 0.6s ease-out;
}

.animate-pulse {
  animation: pulse 2s infinite;
}

.animate-on-scroll {
  opacity: 0;
  transform: translateY(30px);
  transition: all 0.6s ease-out;
}

.animate-on-scroll.visible {
  opacity: 1;
  transform: translateY(0);
}
```

## Responsive Design

### Mobile Styles
```css
@media (max-width: 767px) {
  .hero-title {
    font-size: var(--text-4xl);
  }
  
  .container {
    padding: 0 var(--space-4);
  }
  
  .grid {
    grid-template-columns: 1fr;
  }
  
  .nav-links {
    display: none;
  }
  
  .mobile-menu-toggle {
    display: block;
  }
}
```

### Tablet Styles
```css
@media (min-width: 768px) and (max-width: 1023px) {
  .grid-cols-2 {
    grid-template-columns: repeat(2, 1fr);
  }
  
  .hero-title {
    font-size: var(--text-5xl);
  }
}
```

### Desktop Styles
```css
@media (min-width: 1024px) {
  .grid-cols-3 {
    grid-template-columns: repeat(3, 1fr);
  }
  
  .hero-title {
    font-size: var(--text-6xl);
  }
  
  .container {
    padding: 0 var(--space-8);
  }
}
```

## Accessibility Features

### Focus States
```css
.focus-visible:focus {
  outline: 2px solid var(--color-primary);
  outline-offset: 2px;
}

.btn:focus-visible {
  box-shadow: 0 0 0 3px rgba(30, 64, 175, 0.3);
}
```

### High Contrast Mode
```css
@media (prefers-contrast: high) {
  :root {
    --color-primary: #000080;
    --color-secondary: #008000;
    --color-neutral-600: #000000;
  }
}
```

### Reduced Motion
```css
@media (prefers-reduced-motion: reduce) {
  * {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
  }
  
  html {
    scroll-behavior: auto;
  }
}
```

## Dark Mode Support
```css
@media (prefers-color-scheme: dark) {
  :root {
    --color-neutral-50: #111827;
    --color-neutral-100: #1f2937;
    --color-neutral-900: #f9fafb;
  }
  
  body {
    background-color: var(--color-neutral-100);
    color: var(--color-neutral-50);
  }
  
  .card {
    background: var(--color-neutral-800);
    border-color: var(--color-neutral-700);
  }
}
```

## Performance Optimizations

### Hardware Acceleration
```css
.gpu-accelerated {
  transform: translateZ(0);
  will-change: transform;
}

.smooth-scroll {
  -webkit-overflow-scrolling: touch;
}
```

### Critical CSS
```css
/* Above-the-fold critical styles */
.critical {
  /* Essential styles for initial render */
}
```

## Success Criteria

- [ ] Complete design system with consistent tokens
- [ ] Responsive design that works on all screen sizes
- [ ] Smooth 60fps animations and transitions
- [ ] Accessibility compliance (WCAG 2.1 AA)
- [ ] High contrast and dark mode support
- [ ] Performance-optimized CSS (< 100KB)
- [ ] Modern, professional visual design
- [ ] Interactive elements with proper feedback
- [ ] Cross-browser compatibility
- [ ] Print-friendly styles

This comprehensive CSS system will create a visually stunning, highly functional, and accessible showcase that demonstrates the quality and attention to detail that PDD enables in web development.