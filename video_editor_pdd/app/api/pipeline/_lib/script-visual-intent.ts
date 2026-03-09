export type ScriptSectionVisualIntent = {
  heading: string;
  normalizedHeading: string;
  veoMarkers: string[];
};

const collapseWhitespace = (value: string): string => value.replace(/\s+/g, " ").trim();

export function normalizeSectionIntentKey(value: string): string {
  return collapseWhitespace(
    value
      .toLowerCase()
      .replace(/[_-]+/g, " ")
      .replace(/([a-z])([0-9])/g, "$1 $2")
      .replace(/([0-9])([a-z])/g, "$1 $2")
      .replace(/[^a-z0-9\s]/g, " ")
  );
}

export function parseScriptSectionVisualIntent(
  content: string
): ScriptSectionVisualIntent[] {
  const sections: ScriptSectionVisualIntent[] = [];
  const lines = content.split(/\r?\n/);
  let current: ScriptSectionVisualIntent | null = null;

  lines.forEach((line) => {
    const trimmed = line.trim();

    if (/^##\s+/.test(trimmed)) {
      if (current) {
        sections.push(current);
      }

      const heading = trimmed.replace(/^##\s+/, "").trim();
      current = {
        heading,
        normalizedHeading: normalizeSectionIntentKey(heading),
        veoMarkers: [],
      };
      return;
    }

    if (!current) {
      return;
    }

    const veoMatches = Array.from(trimmed.matchAll(/\[veo:\s*([^\]]*?)\]/gi));
    veoMatches.forEach((match) => {
      current?.veoMarkers.push((match[1] ?? "").trim());
    });
  });

  if (current) {
    sections.push(current);
  }

  return sections.filter((section) => section.heading.length > 0);
}

const buildSectionCandidates = (target: { id: string; label: string }): string[] => {
  const variants = [
    target.label,
    target.id,
    target.label.replace(/^part\s+\d+\s*:\s*/i, ""),
    target.id.replace(/^part[_-]?(\d+)[_-]?/i, "part $1 "),
  ]
    .map(normalizeSectionIntentKey)
    .filter(Boolean);

  return Array.from(new Set(variants));
};

const tokenOverlapScore = (left: string, right: string): number => {
  const leftTokens = left.split(" ").filter(Boolean);
  const rightTokens = right.split(" ").filter(Boolean);

  if (leftTokens.length === 0 || rightTokens.length === 0) {
    return 0;
  }

  const rightSet = new Set(rightTokens);
  const overlap = leftTokens.filter((token) => rightSet.has(token)).length;
  return overlap / Math.max(leftTokens.length, rightTokens.length);
};

export function findMatchingScriptSectionVisualIntent(
  sections: ScriptSectionVisualIntent[],
  target: { id: string; label: string }
): ScriptSectionVisualIntent | null {
  const candidates = buildSectionCandidates(target);
  let bestSection: ScriptSectionVisualIntent | null = null;
  let bestScore = 0;

  sections.forEach((section) => {
    candidates.forEach((candidate) => {
      const condensedHeading = section.normalizedHeading.replace(/\s+/g, "");
      const condensedCandidate = candidate.replace(/\s+/g, "");

      let score = 0;
      if (section.normalizedHeading === candidate) {
        score = 100;
      } else if (condensedHeading === condensedCandidate) {
        score = 95;
      } else if (
        section.normalizedHeading.includes(candidate) ||
        candidate.includes(section.normalizedHeading)
      ) {
        score = 80;
      } else {
        score = Math.round(tokenOverlapScore(section.normalizedHeading, candidate) * 70);
      }

      if (score > bestScore) {
        bestScore = score;
        bestSection = section;
      }
    });
  });

  return bestScore >= 60 ? bestSection : null;
}

export function resolveSectionHasVeoIntent(
  content: string,
  target: { id: string; label: string }
): boolean | null {
  const matchingSection = findMatchingScriptSectionVisualIntent(
    parseScriptSectionVisualIntent(content),
    target
  );

  if (!matchingSection) {
    return null;
  }

  return matchingSection.veoMarkers.length > 0;
}

export function resolveSectionVeoPromptFromScript(
  content: string,
  target: { id: string; label: string }
): string | null {
  const matchingSection = findMatchingScriptSectionVisualIntent(
    parseScriptSectionVisualIntent(content),
    target
  );

  return matchingSection?.veoMarkers.find((marker) => marker.length > 0) ?? null;
}
