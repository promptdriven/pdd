/**
 * PDD Directive definitions for autocomplete and guidance sidebar
 */

export interface PDDDirective {
  tag: string;
  description: string;
  syntax: string;
  example: string;
  hasClosingTag: boolean;
  category: 'include' | 'meta' | 'grounding' | 'dynamic';
}

export const PDD_DIRECTIVES: PDDDirective[] = [
  {
    tag: 'include',
    description: 'Include file content (text or image) at this position',
    syntax: '<include>path/to/file</include>',
    example: '<include>context/preamble.prompt</include>',
    hasClosingTag: true,
    category: 'include',
  },
  {
    tag: 'include-many',
    description: 'Include multiple files (comma-separated)',
    syntax: '<include-many>path1, path2, ...</include-many>',
    example: '<include-many>src/api.ts, src/types.ts</include-many>',
    hasClosingTag: true,
    category: 'include',
  },
  {
    tag: 'pdd',
    description: 'Human-only comment (removed during preprocessing)',
    syntax: '<pdd>comment text</pdd>',
    example: '<pdd>TODO: Add more examples here</pdd>',
    hasClosingTag: true,
    category: 'meta',
  },
  {
    tag: 'shell',
    description: 'Run shell command and inline stdout (non-deterministic)',
    syntax: '<shell>command</shell>',
    example: '<shell>git config --get user.name</shell>',
    hasClosingTag: true,
    category: 'dynamic',
  },
  {
    tag: 'web',
    description: 'Fetch URL content as markdown (non-deterministic)',
    syntax: '<web>URL</web>',
    example: '<web>https://docs.example.com/api</web>',
    hasClosingTag: true,
    category: 'dynamic',
  },
  {
    tag: 'pin',
    description: 'Force a specific grounding example (PDD Cloud)',
    syntax: '<pin>module_name</pin>',
    example: '<pin>user_service</pin>',
    hasClosingTag: true,
    category: 'grounding',
  },
  {
    tag: 'exclude',
    description: 'Block a grounding example from being retrieved (PDD Cloud)',
    syntax: '<exclude>module_name</exclude>',
    example: '<exclude>legacy_handler</exclude>',
    hasClosingTag: true,
    category: 'grounding',
  },
];

// Best practices for the guidance sidebar
export const BEST_PRACTICES = [
  {
    title: 'Prompt-to-Code Ratio',
    content: 'Aim for 10-30% of expected code size. Too vague (<10%) or too detailed (>50%) reduces effectiveness.',
  },
  {
    title: 'Prompt Structure',
    content: 'Include: Role/scope (1-2 sentences), Requirements (5-10 items), Dependencies via <include>.',
  },
  {
    title: 'What to Avoid',
    content: 'Don\'t include: Coding style (use preamble), implementation patterns, every edge case (use tests).',
  },
  {
    title: 'Shared Preamble',
    content: 'Use <include>context/preamble.prompt</include> for consistent coding style across all prompts.',
  },
];

// Category labels for display
export const CATEGORY_LABELS: Record<PDDDirective['category'], string> = {
  include: 'Context Includes',
  grounding: 'Grounding (Cloud)',
  dynamic: 'Dynamic Content',
  meta: 'Comments',
};
