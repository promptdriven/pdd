// example_usage.ts
// Comprehensive usage example for lib/project.ts
// Demonstrates loading, saving, validating, and querying project configuration.
//
// NOTE: This module is marked 'server-only' and must run in a Node.js
// server context (e.g., Next.js API routes or server components).

import fs from 'fs';
import os from 'os';
import path from 'path';

import {
  loadProject,
  saveProject,
  validateProjectConfig,
  getSection,
  projectConfigSchema,
  sectionSchema,
  ttsConfigSchema,
} from '../lib/project';

import type { ProjectConfig, Section } from '../lib/types';

// ============================================================================
// Example 1: Validate raw/untrusted data against the schema
// ============================================================================

/**
 * validateProjectConfig(data: unknown): ProjectConfig
 *
 * A thin wrapper around projectConfigSchema.parse(). Validates arbitrary
 * data against the full ProjectConfig Zod schema.
 *
 * @param data - Any unknown value (e.g., parsed JSON from an API request body).
 *
 * @returns A fully typed and validated ProjectConfig object.
 *
 * @throws ZodError with field-level details if validation fails.
 *         Each issue includes the path to the invalid field, the expected type,
 *         and the received value.
 */

// Simulating data received from an API request
const rawRequestBody: unknown = {
  name: 'Demo Video Project',
  outputResolution: '1920x1080',
  tts: {
    voice: 'en-US-Neural2-F',
    rate: 1.0, // Will be coerced via z.coerce.number()
    model: 'google-tts-v2',
  },
  sections: [
    {
      id: 'intro',
      label: 'Introduction',
      videoFile: 'output/sections/intro.mp4',
      specDir: 'specs/intro',
      remotionDir: 'remotion/intro',
      compositionId: 'IntroComposition',
      durationSeconds: 12.5,
      offsetSeconds: 0,
    },
    {
      id: 'main',
      label: 'Main Content',
      videoFile: 'output/sections/main.mp4',
      specDir: 'specs/main',
      remotionDir: 'remotion/main',
      compositionId: 'MainComposition',
      // durationSeconds omitted — will default to 0 via z.coerce.number().default(0)
      // offsetSeconds omitted — will default to 0
    },
  ],
  audioSync: {
    sectionGroups: {
      narration: ['intro', 'main'],
      music: ['intro'],
    },
  },
  veo: {
    model: 'veo-2.0-generate-001',
    aspectRatio: '16:9',
    referenceImages: {
      logo: 'assets/logo.png',
      background: 'assets/bg-gradient.png',
    },
  },
  render: {
    maxParallelRenders: 3,
    outputDir: 'output/final',
    fps: 30,
    width: 1920,
    height: 1080,
  },
};

const validated: ProjectConfig = validateProjectConfig(rawRequestBody);
console.log('Validation passed!');
console.log(`Project name: ${validated.name}`);
// Note: the 'main' section will have durationSeconds=0 and offsetSeconds=0
// because of the Zod .default(0) on those fields.
console.log(
  `Main section duration: ${validated.sections[1].durationSeconds}s (defaulted)`
);

// Demonstrate validation failure with invalid data
try {
  validateProjectConfig({
    name: 123, // wrong type — should be string
    outputResolution: '4K', // not in enum ['1920x1080', '1280x720']
  });
} catch (err) {
  // ZodError with detailed field-level issues:
  // - path: ['name'], expected: string, received: number
  // - path: ['outputResolution'], invalid enum value
  // - path: ['tts'], required
  // - path: ['sections'], required
  // etc.
  console.log('\nExpected validation error caught (invalid name type + bad resolution)');
}

// ============================================================================
// Example 2: Save a project config atomically
// ============================================================================

/**
 * saveProject(config: ProjectConfig, dir?: string): void
 *
 * Validates the config with Zod, then writes it atomically to project.json.
 * The atomic write strategy:
 *   1. Serialize to JSON with 2-space indentation (human-readable).
 *   2. Write to project.tmp.json in the target directory.
 *   3. Rename project.tmp.json → project.json via fs.renameSync.
 *
 * This prevents partial/corrupt writes if the process crashes mid-write.
 *
 * @param config - A ProjectConfig object. Will be re-validated before writing.
 * @param dir    - Optional directory path. Defaults to process.cwd().
 *
 * @throws ZodError if the config does not pass schema validation.
 * @throws Error if the filesystem write or rename fails.
 */

const projectConfig: ProjectConfig = {
  name: 'Product Launch Video',
  outputResolution: '1920x1080',
  tts: {
    voice: 'en-US-Neural2-F',
    rate: 1.0,
    model: 'google-tts-v2',
  },
  sections: [
    {
      id: 'intro',
      label: 'Introduction',
      videoFile: 'output/sections/intro.mp4',
      specDir: 'specs/intro',
      remotionDir: 'remotion/intro',
      compositionId: 'IntroComposition',
      durationSeconds: 12.5,
      offsetSeconds: 0,
    },
    {
      id: 'main',
      label: 'Main Content',
      videoFile: 'output/sections/main.mp4',
      specDir: 'specs/main',
      remotionDir: 'remotion/main',
      compositionId: 'MainComposition',
      durationSeconds: 45.0,
      offsetSeconds: 12.5,
    },
    {
      id: 'outro',
      label: 'Outro',
      videoFile: 'output/sections/outro.mp4',
      specDir: 'specs/outro',
      remotionDir: 'remotion/outro',
      compositionId: 'OutroComposition',
      durationSeconds: 8.0,
      offsetSeconds: 57.5,
    },
  ],
  audioSync: {
    sectionGroups: {
      narration: ['intro', 'main', 'outro'],
      music: ['intro', 'outro'],
    },
  },
  veo: {
    model: 'veo-2.0-generate-001',
    aspectRatio: '16:9',
    referenceImages: {
      logo: 'assets/logo.png',
    },
  },
  render: {
    maxParallelRenders: 3,
    outputDir: 'output/final',
    fps: 30,
    width: 1920,
    height: 1080,
  },
};

// Use a temp directory so the example is self-contained and doesn't pollute cwd
const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'pdd-example-'));

// Save to the temp directory
saveProject(projectConfig, tmpDir);
console.log(`\nProject saved successfully to ${path.join(tmpDir, 'project.json')}`);

// Save to another subdirectory to demonstrate the dir parameter
const subDir = path.join(tmpDir, 'subproject');
fs.mkdirSync(subDir);
saveProject(projectConfig, subDir);
console.log(`Project saved to ${path.join(subDir, 'project.json')}`);

// ============================================================================
// Example 3: Load an existing project.json from disk
// ============================================================================

/**
 * loadProject(dir?: string): ProjectConfig
 *
 * Reads `project.json` from the given directory (defaults to process.cwd()).
 * Parses the JSON and validates it against the full Zod schema.
 *
 * @param dir - Optional directory path containing project.json.
 *              Defaults to process.cwd() if omitted.
 *
 * @returns A fully validated ProjectConfig object with all fields typed.
 *
 * @throws Error if project.json does not exist at the resolved path.
 * @throws ZodError if the JSON content does not match the ProjectConfig schema.
 *         The error message includes the file path for easier debugging.
 */

// Load from the temp directory where we just saved
const config: ProjectConfig = loadProject(tmpDir);

console.log(`\nLoaded project: "${config.name}"`);
console.log(`Resolution: ${config.outputResolution}`);
console.log(`Sections: ${config.sections.length}`);
console.log(`TTS voice: ${config.tts.voice}`);
console.log(`Veo model: ${config.veo.model}`);
console.log(`Render FPS: ${config.render.fps}`);

// Demonstrate load error for missing file
try {
  loadProject('/nonexistent/path');
} catch (err) {
  console.log(`\nExpected load error caught (file not found)`);
}

// ============================================================================
// Example 4: Look up a section by ID
// ============================================================================

/**
 * getSection(id: string, config: ProjectConfig): Section | undefined
 *
 * Finds and returns a section from config.sections by its unique ID.
 *
 * @param id     - The section ID to search for (e.g., 'intro', 'main').
 * @param config - The ProjectConfig containing the sections array.
 *
 * @returns The matching Section object, or undefined if no section has that ID.
 */

const introSection: Section | undefined = getSection('intro', config);
if (introSection) {
  console.log(`\nFound section: "${introSection.label}"`);
  console.log(`  Video file: ${introSection.videoFile}`);
  console.log(`  Duration: ${introSection.durationSeconds}s`);
  console.log(`  Offset: ${introSection.offsetSeconds}s`);
  console.log(`  Composition: ${introSection.compositionId}`);
  console.log(`  Spec dir: ${introSection.specDir}`);
  console.log(`  Remotion dir: ${introSection.remotionDir}`);
} else {
  console.log('Section "intro" not found');
}

// Handling a missing section
const missing = getSection('nonexistent', config);
console.log(`\nSection "nonexistent" found: ${missing !== undefined}`); // false

// ============================================================================
// Example 5: Using exported Zod schemas for partial validation in API routes
// ============================================================================

/**
 * The individual Zod schemas (projectConfigSchema, sectionSchema, ttsConfigSchema, etc.)
 * are named exports, so they can be imported in API routes for partial validation
 * or for building derivative schemas.
 */

// Validate just a TTS config (e.g., from a PATCH /api/config/tts endpoint)
const ttsPayload = { voice: 'en-US-Neural2-D', rate: '1.2', model: 'google-tts-v2' };
const validatedTts = ttsConfigSchema.parse(ttsPayload);
console.log(`\nTTS rate (coerced from string): ${validatedTts.rate}`); // 1.2 (number)

// Validate a single section
const sectionPayload = {
  id: 'credits',
  label: 'Credits',
  videoFile: 'output/sections/credits.mp4',
  specDir: 'specs/credits',
  remotionDir: 'remotion/credits',
  compositionId: 'CreditsComposition',
  // durationSeconds and offsetSeconds omitted — defaults to 0
};
const validatedSection = sectionSchema.parse(sectionPayload);
console.log(
  `Section "${validatedSection.label}" duration: ${validatedSection.durationSeconds}s`
); // 0

// Use projectConfigSchema.partial() for PATCH-style updates
const partialSchema = projectConfigSchema.partial();
const partialUpdate = partialSchema.parse({ name: 'Updated Project Name' });
console.log(`Partial update name: ${partialUpdate.name}`);

// ============================================================================
// Example 6: Typical API route pattern — load, modify, save
// ============================================================================

/**
 * Common pattern in Next.js API routes: load the project, make changes,
 * and save it back atomically.
 */
function addSectionToProject(newSection: Section, dir?: string): ProjectConfig {
  // 1. Load current state
  const cfg = loadProject(dir);

  // 2. Check for duplicate IDs
  if (cfg.sections.some((s) => s.id === newSection.id)) {
    throw new Error(`Section with id "${newSection.id}" already exists`);
  }

  // 3. Validate the new section independently
  const validatedSec = sectionSchema.parse(newSection);

  // 4. Add section and recalculate offset
  const lastSection = cfg.sections[cfg.sections.length - 1];
  validatedSec.offsetSeconds = lastSection
    ? lastSection.offsetSeconds + lastSection.durationSeconds
    : 0;

  cfg.sections.push(validatedSec);

  // 5. Save atomically — saveProject re-validates the entire config
  saveProject(cfg, dir);

  return cfg;
}

// Run addSectionToProject against our temp directory
const updated = addSectionToProject(
  {
    id: 'credits',
    label: 'Credits',
    videoFile: 'output/sections/credits.mp4',
    specDir: 'specs/credits',
    remotionDir: 'remotion/credits',
    compositionId: 'CreditsComposition',
    durationSeconds: 5.0,
    offsetSeconds: 0, // will be recalculated
  },
  tmpDir
);
console.log(`\nProject now has ${updated.sections.length} sections`);

// Clean up temp files
fs.rmSync(tmpDir, { recursive: true, force: true });

console.log('\n✅ All examples completed successfully');
