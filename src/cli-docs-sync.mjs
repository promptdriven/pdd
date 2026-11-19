// Generated from prompts/cli/cli-docs-sync.prompt.md.

export const CLI_DOCS_START_MARKER = '<!-- pdd:generated:cli-commands:start -->';
export const CLI_DOCS_END_MARKER = '<!-- pdd:generated:cli-commands:end -->';
export const CLI_DOCS_NOTICE = '<!-- Auto-generated from the command catalog; update via sync, not by hand. -->';
export const CLI_DOCS_GROUP_ORDER = Object.freeze([
  'Core PDD workflow',
  'Cloud accounts',
  'Workflows & product',
  'Autopilot',
  'Metrics, shell & help',
]);

const CONTROL_CHARS = /[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/g;
const INVALID_FORM_CHARS = /[\r\n`]/;
const RENDERED_ROW = /^\| `([^`\n]+)` \|/;

const GROUP_RULES = [
  { group: 'Cloud accounts', exact: ['accounts'], prefixes: ['accounts.'] },
  { group: 'Workflows & product', exact: ['graph'], prefixes: ['product.', 'workflow.', 'dependencies.'] },
  { group: 'Autopilot', exact: ['autopilot'], prefixes: ['autopilot.'] },
  { group: 'Metrics, shell & help', exact: ['metrics', 'completion', 'help', 'version'], prefixes: ['metrics.', 'version.'] },
];

/** Create an Error tagged with a canonical cli-docs-sync error code. */
function codedError(code, message) {
  const err = new Error(message);
  err.code = code;
  return err;
}

function isRecord(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

/** Infer the canonical CLI reference group title from a route id. */
function inferGroupForRouteId(id) {
  for (const rule of GROUP_RULES) {
    if (rule.exact.includes(id) || rule.prefixes.some(prefix => id.startsWith(prefix))) {
      return rule.group;
    }
  }
  return 'Core PDD workflow';
}

function escapePipe(text) {
  return text.replaceAll('|', '\\|');
}

/** Normalize a command description into a single table-safe Markdown cell. */
function cleanDescription(description) {
  const collapsed = description
    .replace(CONTROL_CHARS, '')
    .replace(/[\r\n\t ]+/g, ' ')
    .trim();
  return collapsed ? escapePipe(collapsed) : '-';
}

/** Validate route definitions and group their unique command forms in canonical order. */
function collectGroupedForms(routes) {
  if (!Array.isArray(routes)) {
    throw codedError('invalid-route', 'routes must be an array.');
  }

  const byGroup = new Map();
  const customGroups = [];
  const seenForms = new Set();
  const orderedForms = [];

  for (const route of routes) {
    if (!isRecord(route) || typeof route.id !== 'string' || !route.id.trim()) {
      throw codedError('invalid-route', 'Each route must be an object with a nonblank string id.');
    }
    if (route.group !== undefined && route.group !== null && typeof route.group !== 'string') {
      throw codedError('invalid-route', `Route "${route.id}" has a non-string group.`);
    }
    if (!Array.isArray(route.forms)) {
      throw codedError('invalid-route', `Route "${route.id}" must include a forms array.`);
    }

    const explicitGroup = typeof route.group === 'string' ? route.group.trim() : '';
    const groupTitle = explicitGroup || inferGroupForRouteId(route.id.trim());

    for (const entry of route.forms) {
      if (!isRecord(entry) || typeof entry.form !== 'string' || typeof entry.description !== 'string') {
        throw codedError('invalid-route', `Route "${route.id}" contains an invalid form entry.`);
      }
      const trimmedForm = entry.form.trim();
      if (!trimmedForm || INVALID_FORM_CHARS.test(entry.form)) {
        throw codedError('invalid-route', `Route "${route.id}" contains an empty, multi-line, or backtick form.`);
      }
      if (seenForms.has(trimmedForm)) {
        throw codedError('invalid-route', `Duplicate command form "${trimmedForm}".`);
      }

      seenForms.add(trimmedForm);
      orderedForms.push(trimmedForm);
      if (!byGroup.has(groupTitle)) {
        byGroup.set(groupTitle, []);
        if (!CLI_DOCS_GROUP_ORDER.includes(groupTitle)) {
          customGroups.push(groupTitle);
        }
      }
      byGroup.get(groupTitle).push({
        form: trimmedForm,
        description: entry.description,
      });
    }
  }

  const groups = [
    ...CLI_DOCS_GROUP_ORDER.filter(title => (byGroup.get(title)?.length ?? 0) > 0),
    ...customGroups.filter(title => (byGroup.get(title)?.length ?? 0) > 0),
  ];

  return { groups, byGroup, orderedForms, formCount: orderedForms.length };
}

/** Split a document into line spans while preserving exact byte offsets and line endings. */
function scanDocumentLines(document) {
  const lines = [];
  let start = 0;
  while (start <= document.length) {
    const nl = document.indexOf('\n', start);
    if (nl === -1) {
      const raw = document.slice(start);
      const textWithoutCr = raw.endsWith('\r') ? raw.slice(0, -1) : raw;
      lines.push({ startOffset: start, lineEndOffset: document.length, textWithoutCr });
      break;
    }
    const raw = document.slice(start, nl);
    const textWithoutCr = raw.endsWith('\r') ? raw.slice(0, -1) : raw;
    lines.push({ startOffset: start, lineEndOffset: nl + 1, textWithoutCr });
    start = nl + 1;
  }
  return lines;
}

function isConflictMarkerLine(textWithoutCr) {
  return (
    textWithoutCr.startsWith('<<<<<<< ')
    || textWithoutCr.startsWith('||||||| ')
    || textWithoutCr === '======='
    || textWithoutCr.startsWith('>>>>>>> ')
  );
}

/** Validate marker lines and locate Git conflict markers relative to the generated block. */
function inspectMarkedDocument(document) {
  if (typeof document !== 'string') {
    throw codedError('missing-markers', 'Document must be a string containing generated command markers.');
  }

  const lines = scanDocumentLines(document);
  const startIndices = [];
  const endIndices = [];

  for (let i = 0; i < lines.length; i++) {
    const trimmedRight = lines[i].textWithoutCr.replace(/[ \t]+$/, '');
    if (trimmedRight === CLI_DOCS_START_MARKER) startIndices.push(i);
    if (trimmedRight === CLI_DOCS_END_MARKER) endIndices.push(i);
  }

  if (startIndices.length === 0 || endIndices.length === 0) {
    throw codedError('missing-markers', 'Document is missing the CLI command start or end marker.');
  }
  if (startIndices.length > 1 || endIndices.length > 1) {
    throw codedError('duplicate-markers', 'Document contains duplicate CLI command markers.');
  }

  const startIdx = startIndices[0];
  const endIdx = endIndices[0];
  if (endIdx < startIdx) {
    throw codedError('misordered-markers', 'CLI command end marker appears before the start marker.');
  }

  for (let i = 0; i < lines.length; i++) {
    if (i > startIdx && i < endIdx) continue;
    if (isConflictMarkerLine(lines[i].textWithoutCr)) {
      throw codedError('prose-conflict', 'Document contains Git conflict markers outside the generated CLI command block.');
    }
  }

  const insideLines = lines.slice(startIdx + 1, endIdx);
  const insideConflict = insideLines.some(line => isConflictMarkerLine(line.textWithoutCr));
  const eol = document.includes('\r\n') ? '\r\n' : '\n';
  const prefix = document.slice(0, lines[startIdx].lineEndOffset);
  const suffix = document.slice(lines[endIdx].startOffset);

  return { eol, prefix, suffix, insideLines, insideConflict };
}

function spliceRenderedBlock(prefix, markdown, eol, suffix) {
  const body = eol === '\r\n' ? markdown.replaceAll('\n', '\r\n') : markdown;
  return `${prefix}${body}${eol}${suffix}`;
}

function extractRenderedForms(insideLines) {
  const seen = new Set();
  const forms = [];
  for (const line of insideLines) {
    const match = RENDERED_ROW.exec(line.textWithoutCr);
    if (!match) continue;
    const form = match[1].replaceAll('\\|', '|');
    if (seen.has(form)) continue;
    seen.add(form);
    forms.push(form);
  }
  return forms;
}

/** Render grouped tables along with catalog-ordered forms for internal callers. */
function renderCommandTablesInternal(routes) {
  const { groups, byGroup, orderedForms, formCount } = collectGroupedForms(routes);
  const lines = [CLI_DOCS_NOTICE];

  if (formCount > 0) {
    for (const group of groups) {
      lines.push('', `### ${group}`, '', '| Command | What it does |', '| --- | --- |');
      for (const entry of byGroup.get(group)) {
        lines.push(`| \`${escapePipe(entry.form)}\` | ${cleanDescription(entry.description)} |`);
      }
    }
    lines.push('');
  }

  return {
    markdown: lines.join('\n'),
    formCount,
    groups,
    orderedForms,
  };
}

/** Render grouped one-row-per-command Markdown tables from catalog routes. */
export function renderCommandTables(input) {
  if (!isRecord(input)) {
    throw codedError('invalid-route', 'Input must be an object with routes.');
  }
  const { markdown, formCount, groups } = renderCommandTablesInternal(input.routes);
  return { markdown, formCount, groups };
}

/** Splice regenerated CLI command tables between the document markers. */
export function syncCliDocs(input) {
  if (!isRecord(input)) {
    throw codedError('invalid-route', 'Input must be an object with document and routes.');
  }
  const { document, routes, allowInsideConflicts = false } = input;
  const rendered = renderCommandTablesInternal(routes);
  const inspected = inspectMarkedDocument(document);

  if (inspected.insideConflict && allowInsideConflicts !== true) {
    throw codedError('generated-conflict', 'Generated CLI command block contains Git conflict markers; opt in with allowInsideConflicts to regenerate.');
  }

  const nextDocument = spliceRenderedBlock(inspected.prefix, rendered.markdown, inspected.eol, inspected.suffix);
  return {
    document: nextDocument,
    changed: nextDocument !== document,
    resolvedConflicts: inspected.insideConflict,
    formCount: rendered.formCount,
    groups: rendered.groups,
  };
}

/** Check whether a document's generated CLI command tables match the command catalog. */
export function checkCliDocs(input) {
  if (!isRecord(input)) {
    throw codedError('invalid-route', 'Input must be an object with document and routes.');
  }
  const { document, routes } = input;
  const rendered = renderCommandTablesInternal(routes);
  const inspected = inspectMarkedDocument(document);

  if (inspected.insideConflict) {
    return {
      ok: false,
      status: 'conflict',
      missingForms: [],
      extraForms: [],
      formCount: rendered.formCount,
    };
  }

  const expectedDocument = spliceRenderedBlock(inspected.prefix, rendered.markdown, inspected.eol, inspected.suffix);
  if (expectedDocument === document) {
    return {
      ok: true,
      status: 'current',
      missingForms: [],
      extraForms: [],
      formCount: rendered.formCount,
    };
  }

  const existingForms = extractRenderedForms(inspected.insideLines);
  const existingSet = new Set(existingForms);
  const catalogSet = new Set(rendered.orderedForms);
  const missingForms = rendered.orderedForms.filter(form => !existingSet.has(form));
  const extraForms = existingForms.filter(form => !catalogSet.has(form));

  return {
    ok: false,
    status: 'stale',
    missingForms,
    extraForms,
    formCount: rendered.formCount,
  };
}
