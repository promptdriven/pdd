import type { Section } from "./types";
import {
  groupScriptSectionsByProjectSection,
  normalizeNarrativeHeading,
  parseTimedNarrativeHeadings,
} from "./narration-manifest";

type SectionSummary = Pick<Section, "id" | "label"> & {
  scriptHeadings?: string[];
};

type GeneratedBlock = {
  tags: string[];
  speech: string;
  trailingPause: string | null;
};

const TTS_TAG_RE = /^\[(TONE|PACE|EMOTION|INSTRUCT):[^\]]+\]$/i;
const PAUSE_TAG_RE = /^\[PAUSE:[^\]]+\]$/i;
const NARRATOR_RE = /^\*{0,2}NARRATOR:\*{0,2}\s*$/i;
const BASE_INSTRUCTION =
  "Speak with a confident, authoritative tone like a knowledgeable educator";

const cleanText = (value: string): string =>
  value.replace(/\s+/g, " ").trim();

const titleFromId = (sectionId: string): string =>
  sectionId
    .split(/[_-]+/)
    .filter(Boolean)
    .map((part) => part[0]?.toUpperCase() + part.slice(1))
    .join(" ");

const extractTagValue = (
  tags: readonly string[],
  name: "TONE" | "PACE" | "EMOTION" | "INSTRUCT",
): string | null => {
  const match = tags
    .map((tag) => tag.match(new RegExp(`^\\[${name}:\\s*([^\\]]+)\\]$`, "i")))
    .find(Boolean);
  return match?.[1]?.replace(/\s+/g, " ").trim() ?? null;
};

const buildInstructionText = (tags: readonly string[]): string => {
  const explicit = extractTagValue(tags, "INSTRUCT");
  if (explicit) {
    return explicit;
  }

  const tone = extractTagValue(tags, "TONE");
  const pace = extractTagValue(tags, "PACE");
  const emotion = extractTagValue(tags, "EMOTION");
  const parts: string[] = [];

  if (tone) {
    parts.push(`with a ${tone.toLowerCase()} tone`);
  }

  if (pace && pace.toLowerCase() !== "moderate") {
    parts.push(`at a ${pace.toLowerCase()} pace`);
  }

  if (emotion) {
    parts.push(`with ${emotion.toLowerCase()} emotion`);
  }

  return parts.length > 0
    ? `${BASE_INSTRUCTION}, ${parts.join(", ")}.`
    : `${BASE_INSTRUCTION}.`;
};

const ensureInstructionTag = (tags: readonly string[]): string[] => {
  const filteredTags = tags.filter(Boolean);
  if (extractTagValue(filteredTags, "INSTRUCT")) {
    return [...filteredTags];
  }
  return [...filteredTags, `[INSTRUCT: ${buildInstructionText(filteredTags)}]`];
};

const extractNarrationParagraphs = (body: string): string[] => {
  const paragraphs: string[] = [];
  let currentLines: string[] = [];
  let narratorStarted = false;

  const flush = () => {
    const paragraph = cleanText(currentLines.join(" "));
    if (paragraph) {
      paragraphs.push(paragraph);
    }
    currentLines = [];
  };

  for (const line of body.split(/\r?\n/)) {
    const trimmed = line.trim();

    if (NARRATOR_RE.test(trimmed)) {
      flush();
      narratorStarted = true;
      continue;
    }

    if (!narratorStarted) {
      continue;
    }

    if (!trimmed) {
      flush();
      continue;
    }

    if (/^##\s+/.test(trimmed) || /^---+$/.test(trimmed)) {
      flush();
      continue;
    }

    if (/^#{3,}\s+/.test(trimmed)) {
      flush();
      continue;
    }

    if (/^\*{0,2}\[VISUAL:/i.test(trimmed)) {
      flush();
      continue;
    }

    currentLines.push(trimmed.replace(/^\*{0,2}NARRATOR:\*{0,2}\s*/i, ""));
  }

  flush();
  return paragraphs;
};

const parseGeneratedBlocks = (rawTtsScript: string): GeneratedBlock[] => {
  const blocks: GeneratedBlock[] = [];
  let currentTags: string[] = [];
  let currentSpeech: string[] = [];
  let trailingPause: string | null = null;

  const flush = () => {
    const speech = cleanText(currentSpeech.join(" "));
    if (!speech && currentTags.length === 0) {
      trailingPause = null;
      return;
    }

    blocks.push({
      tags: currentTags.filter((tag) => TTS_TAG_RE.test(tag)),
      speech,
      trailingPause,
    });
    currentTags = [];
    currentSpeech = [];
    trailingPause = null;
  };

  for (const line of rawTtsScript.split(/\r?\n/)) {
    const trimmed = line.trim();

    if (!trimmed || /^---+$/.test(trimmed) || /^#(?!#)/.test(trimmed) || /^#{2,3}\s+/.test(trimmed)) {
      if (!trimmed || /^---+$/.test(trimmed) || /^#{2,3}\s+/.test(trimmed)) {
        flush();
      }
      continue;
    }

    if (NARRATOR_RE.test(trimmed)) {
      flush();
      continue;
    }

    if (PAUSE_TAG_RE.test(trimmed)) {
      if (currentSpeech.length > 0 || currentTags.length > 0) {
        trailingPause = trimmed;
        flush();
      } else if (blocks.length > 0) {
        blocks[blocks.length - 1].trailingPause = trimmed;
      }
      continue;
    }

    if (TTS_TAG_RE.test(trimmed)) {
      if (currentSpeech.length > 0) {
        flush();
      }
      currentTags.push(trimmed);
      continue;
    }

    const narrationLine = trimmed.replace(/^\*{0,2}NARRATOR:\*{0,2}\s*/i, "");
    currentSpeech.push(narrationLine);
  }

  flush();
  return blocks;
};

const shouldRenderSubheading = (
  sectionHeading: string,
  canonicalHeading: string,
  sectionIndex: number,
): boolean =>
  sectionIndex > 0 &&
  normalizeNarrativeHeading(sectionHeading) !==
    normalizeNarrativeHeading(canonicalHeading);

export function buildCanonicalTtsScript(
  mainScript: string,
  rawTtsScript: string,
  sections: ReadonlyArray<SectionSummary>,
): string {
  const extractedSections = parseTimedNarrativeHeadings(mainScript);
  const effectiveSections =
    sections.length > 0
      ? sections
      : extractedSections.map((section) => ({
          id: section.heading
            .toLowerCase()
            .replace(/[^a-z0-9]+/g, "_")
            .replace(/^_+|_+$/g, ""),
          label: section.heading,
        }));
  const groupedSections = groupScriptSectionsByProjectSection(
    extractedSections,
    effectiveSections,
  );
  const generatedBlocks = parseGeneratedBlocks(rawTtsScript);
  let blockIndex = 0;

  const sectionBlocks = effectiveSections.map((section, sectionIndex) => {
    const heading = section.label || titleFromId(section.id);
    const lines = [`## ${heading}`, ""];
    const scriptSections = groupedSections.get(section.id) ?? [];

    if (scriptSections.length === 0) {
      const generated = generatedBlocks[blockIndex];
      if (generated) {
        blockIndex += 1;
        lines.push(...ensureInstructionTag(generated.tags.length ? generated.tags : [
          "[TONE: explanatory]",
          "[PACE: moderate]",
          "[EMOTION: calm]",
        ]));
        lines.push(generated.speech);
        if (generated.trailingPause) {
          lines.push(generated.trailingPause);
        }
        lines.push("");
      }
    }

    scriptSections.forEach((scriptSection, scriptSectionIndex) => {
      if (shouldRenderSubheading(scriptSection.heading, heading, scriptSectionIndex)) {
        lines.push(`### ${scriptSection.heading}`);
        lines.push("");
      }

      scriptSection.narration.forEach((paragraph, paragraphIndex) => {
        const generated = generatedBlocks[blockIndex];
        if (generated) {
          blockIndex += 1;
        }

        const tags =
          generated?.tags.length
            ? ensureInstructionTag(generated.tags)
            : ensureInstructionTag([
                "[TONE: explanatory]",
                "[PACE: moderate]",
                "[EMOTION: calm]",
              ]);
        const speech = generated?.speech || paragraph;
        const pause =
          generated?.trailingPause ??
          (paragraphIndex < scriptSection.narration.length - 1 ? "[PAUSE: 1.0s]" : null);

        lines.push(...tags);
        lines.push(speech);
        if (pause) {
          lines.push(pause);
        }
        lines.push("");
      });
    });

    if (sectionIndex === effectiveSections.length - 1) {
      while (blockIndex < generatedBlocks.length) {
        const generated = generatedBlocks[blockIndex];
        blockIndex += 1;
        lines.push(
          ...ensureInstructionTag(
            generated.tags.length ? generated.tags : ["[TONE: explanatory]"],
          ),
        );
        lines.push(generated.speech);
        if (generated.trailingPause) {
          lines.push(generated.trailingPause);
        }
        lines.push("");
      }
    }

    return lines.join("\n").trimEnd();
  });

  return sectionBlocks.length > 0
    ? `${sectionBlocks.join("\n\n---\n\n")}\n`
    : rawTtsScript.trim()
      ? `${rawTtsScript.trim()}\n`
      : "";
}
