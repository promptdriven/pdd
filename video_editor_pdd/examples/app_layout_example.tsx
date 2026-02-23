/**
 * Verification program for the RootLayout component (app/layout.tsx).
 *
 * Validates the module structure, exports, and source-level requirements
 * from the prompt specification. Since the layout imports globals.css (which
 * can't be parsed by Node), we verify by reading the source file AND by
 * requiring the module with a CSS mock registered first.
 *
 * Runs headlessly with `npx tsx`.
 */

import * as fs from 'fs';
import * as path from 'path';
import Module from 'module';
import React from 'react';
import { renderToStaticMarkup } from 'react-dom/server';

// ============================================================================
// 0. Register a no-op CSS loader so `import './globals.css'` doesn't crash
// ============================================================================

// Make React available globally so JSX works in the layout (Next.js auto-injects
// React but tsx with "jsx": "preserve" does not)
(globalThis as any).React = React;

const originalResolveFilename = (Module as any)._resolveFilename;
(Module as any)._resolveFilename = function (request: string, parent: any, ...rest: any[]) {
  if (request.endsWith('.css')) {
    // Return a path to a virtual empty module; we'll intercept in _load too
    return request;
  }
  return originalResolveFilename.call(this, request, parent, ...rest);
};

const originalLoad = (Module as any)._load;
(Module as any)._load = function (request: string, parent: any, ...rest: any[]) {
  if (request.endsWith('.css')) {
    return {}; // no-op
  }
  return originalLoad.call(this, request, parent, ...rest);
};

// ============================================================================
// 1. Source-level requirement verification
// ============================================================================

console.log('=== RootLayout Module Verification ===\n');
console.log('=== Source-Level Requirements ===\n');

const sourcePath = path.resolve(__dirname, '..', 'app', 'layout.tsx');
const source = fs.readFileSync(sourcePath, 'utf-8');

// Req 4: imports globals.css
const importsGlobalsCss = source.includes("import './globals.css'");
console.log('Req 4 - Imports ./globals.css:', importsGlobalsCss ? 'PASS' : 'FAIL');

// Req 6: No 'use client' directive — server component
const hasNoUseClient = !source.includes("'use client'") && !source.includes('"use client"');
console.log('Req 6 - No "use client" (server component):', hasNoUseClient ? 'PASS' : 'FAIL');

// No useState or useEffect
const hasNoClientState = !source.includes('useState') && !source.includes('useEffect');
console.log('Req 6 - No useState/useEffect:', hasNoClientState ? 'PASS' : 'FAIL');

// Instruction: import type { Metadata } from 'next'
const importsMetadataType = source.includes("import type { Metadata } from 'next'");
console.log('Inst - import type { Metadata } from "next":', importsMetadataType ? 'PASS' : 'FAIL');

// Req 7: export default function RootLayout
const hasDefaultExportFn = source.includes('export default function RootLayout');
console.log('Req 7 - export default function RootLayout:', hasDefaultExportFn ? 'PASS' : 'FAIL');

// Req 7: children: React.ReactNode
const hasChildrenType = source.includes('children: React.ReactNode');
console.log('Req 7 - children: React.ReactNode:', hasChildrenType ? 'PASS' : 'FAIL');

// Metadata export in source
const hasMetadataExport = source.includes('export const metadata: Metadata');
console.log('Req 1 - export const metadata: Metadata:', hasMetadataExport ? 'PASS' : 'FAIL');

// ============================================================================
// 2. Module export verification (with CSS mock in place)
// ============================================================================

console.log('\n=== Module Export Verification ===\n');

const LayoutModule = require('../app/layout');

const defaultExport = LayoutModule.default;
const metadataExport = LayoutModule.metadata;

const hasDefaultFn = typeof defaultExport === 'function';
const hasMetadataObj = metadataExport && typeof metadataExport === 'object';

console.log('Default export (RootLayout):', hasDefaultFn ? 'PASS' : 'FAIL');
console.log('Named export (metadata):', hasMetadataObj ? 'PASS' : 'FAIL');

// ============================================================================
// 3. Metadata verification
// ============================================================================

console.log('\n=== Metadata Verification ===\n');

const titleCorrect = metadataExport?.title === 'Video Pipeline Editor';
const descriptionCorrect = metadataExport?.description === 'AI-powered video production pipeline';

console.log('Req 1 - metadata.title is "Video Pipeline Editor":', titleCorrect ? 'PASS' : 'FAIL');
console.log('Req 1 - metadata.description is "AI-powered video production pipeline":', descriptionCorrect ? 'PASS' : 'FAIL');

// ============================================================================
// 4. Render verification — exercise the actual exported component
// ============================================================================

console.log('\n=== Render Verification ===\n');

const RootLayout = defaultExport;
const html = renderToStaticMarkup(
  React.createElement(RootLayout, null,
    React.createElement('div', { id: 'test-child' }, 'Hello')
  )
);

const hasHtmlLangEn = html.includes('lang="en"');
const hasDarkClass = html.includes('class="dark"');
const hasBgPanel = html.includes('bg-panel');
const hasTextSlate200 = html.includes('text-slate-200');
const hasAntialiased = html.includes('antialiased');
const hasMainHScreen = html.includes('h-screen');
const hasOverflowHidden = html.includes('overflow-hidden');
const childrenRendered = html.includes('test-child') && html.includes('Hello');

console.log('Req 2 - <html lang="en" className="dark">:', hasHtmlLangEn && hasDarkClass ? 'PASS' : 'FAIL');
console.log('Req 3 - <body> has bg-panel:', hasBgPanel ? 'PASS' : 'FAIL');
console.log('Req 3 - <body> has text-slate-200:', hasTextSlate200 ? 'PASS' : 'FAIL');
console.log('Req 3 - <body> has antialiased:', hasAntialiased ? 'PASS' : 'FAIL');
console.log('Req 5 - <main> has h-screen:', hasMainHScreen ? 'PASS' : 'FAIL');
console.log('Req 5 - <main> has overflow-hidden:', hasOverflowHidden ? 'PASS' : 'FAIL');
console.log('Req 5 - Children rendered inside <main>:', childrenRendered ? 'PASS' : 'FAIL');

// ============================================================================
// 5. Summary
// ============================================================================

console.log('\n=== Verification Summary ===\n');

const checks = [
  importsGlobalsCss,
  hasNoUseClient,
  hasNoClientState,
  importsMetadataType,
  hasDefaultExportFn,
  hasChildrenType,
  hasMetadataExport,
  hasDefaultFn,
  hasMetadataObj,
  titleCorrect,
  descriptionCorrect,
  hasHtmlLangEn && hasDarkClass,
  hasBgPanel,
  hasTextSlate200,
  hasAntialiased,
  hasMainHScreen,
  hasOverflowHidden,
  childrenRendered,
];

const passed = checks.filter(Boolean).length;
const total = checks.length;

console.log(`Results: ${passed}/${total} checks passed`);

if (passed === total) {
  console.log('Status: ALL CHECKS PASSED');
  console.log('\nRootLayout component fully satisfies the prompt specification.');
} else {
  console.log('Status: SOME CHECKS FAILED');
  const failed = total - passed;
  console.log(`${failed} check(s) did not pass. Review output above.`);
  process.exit(1);
}
