// Generated from prompts/cli/product.prompt.md.
// Thin compatibility facade over Layer-1 core product modules (`src/core/product/*`, ZERO legacy workflow imports).
export { computeProductWaves, parseProductDocuments, parseProductWorldWriters } from './core/product/documents.mjs';
export { auditProductPlan } from './core/product/plan-audit.mjs';
export { resolveProductRepository } from './core/product/github-state.mjs';
export { readProduct, recordedRuntimeLines, sourceFingerprint, storyEvidence } from './core/product/progress.mjs';
export { productNext, productStart, productStatus, runProduct } from './core/product/product-cli.mjs';
