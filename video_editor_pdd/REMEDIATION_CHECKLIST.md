# Architecture Remediation Checklist

## Issue 1: Types.ts Missing 9+ Exports (CRITICAL - Blocks Compilation)

### Current State
- `types_TypeScript.prompt` Requirements section lists only 17 exports
- Architecture uses at least 26 types
- Missing types cause "Cannot find module" errors in 6+ modules

### Affected Modules
- `api_pipeline_veo_route.ts` → imports `VeoClip`
- `api_pipeline_specs_route.ts` → imports `SpecSection`
- `api_pipeline_compositions_route.ts` → imports `CompositionEntry`, `CompositionSection`
- `api_pipeline_render_route.ts` → imports `SectionRenderStatus`, `FullVideoInfo`
- `api_pipeline_audit_route.ts` → imports `AuditSectionResult`, `AuditVerdict`
- `components/stages/Stage4TtsRendering.tsx` → imports `TtsSegment`
- `components/stages/Stage5AudioSync.tsx` → imports `WordTimestamp`

### Required Fix

**File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/prompts/types_TypeScript.prompt`

**Action**: Update the Requirements section to include all 26 type definitions:

```diff
Requirements
1. Export the `PipelineStage` union type covering all 10 pipeline stages...
2. Export `StageStatus` union...
3. Export `JobStatus` union...
4. Export `Job` interface...
5. Export `FixType` union...
6. Export `AnnotationAnalysis` interface...
7. Export `Annotation` interface...
8. Export `Section` interface...
9. Export `TtsConfig` interface...
10. Export `VeoConfig` interface...
11. Export `RenderConfig` interface...
12. Export `AudioSyncConfig` interface...
13. Export `ProjectConfig` interface...
14. Export `RenderProgress` interface...
15. Export `ClaudeFixResult` interface...
16. Export `AnnotationCaptureData` interface...
17. Export `SseSend` type alias...
+ 18. Export `StageStatusEntry` interface: `{ status: StageStatus; lastJobId: string | null; error: string | null }`
+ 19. Export `TtsSegment` interface: `{ segmentId: string; status: 'done' | 'error' | 'pending'; duration: number; text: string }`
+ 20. Export `WordTimestamp` interface: `{ word: string; start: number; end: number; segmentId: string }`
+ 21. Export `VeoClip` interface: `{ clipId: string; section: string; aspectRatio: '16:9' | '9:16'; status: 'pending' | 'done' | 'error'; frameChainDeps: string[] }`
+ 22. Export `AssetStagingEntry` interface: `{ expectedPath: string; presentPath: string | null; status: 'present' | 'missing' }`
+ 23. Export `SpecSection` interface: `{ sectionId: string; files: SpecFile[] }`
+ 24. Export `SpecFile` interface: `{ path: string; visualType: string; status: 'done' | 'error' | 'pending' }`
+ 25. Export `CompositionEntry` interface: `{ id: string; type: string; status: 'done' | 'error' | 'pending' }`
+ 26. Export `CompositionSection` interface: `{ sectionId: string; components: CompositionEntry[]; wrappers: CompositionEntry[] }`
+ 27. Export `SectionRenderStatus` interface: `{ sectionId: string; status: StageStatus; duration: number; progress: number; jobId: string | null }`
+ 28. Export `FullVideoInfo` interface: `{ path: string; duration: number; fileSize: number; exists: boolean }`
+ 29. Export `AuditSectionResult` interface: `{ sectionId: string; passCount: number; failCount: number; status: StageStatus; verdicts: AuditVerdict[] }`
+ 30. Export `AuditVerdict` interface: `{ specId: string; passed: boolean; message: string }`
+ 31. Export `CreateAnnotationInput` interface: `{ sectionId: string; timestamp: number; text: string; drawingDataUrl: string | null; compositeDataUrl: string | null; videoFile: string }`
```

### Verification Checklist
- [ ] Update requirements section with all 31 type definitions
- [ ] Add JSDoc comment for each new type explaining purpose
- [ ] Ensure all types are exported as named exports
- [ ] Verify no new imports added (types.ts should have zero local dependencies)
- [ ] Cross-reference with architecture.json description line 3-4 to ensure complete coverage

### Testing
```bash
# After updating the prompt and regenerating types.ts:
npm run build
# Should compile without "Cannot find module" errors for any type imports
```

---

## Issue 2: TTS Script Endpoint Ambiguity (MEDIUM - Blocks Stage 3 Editor)

### Current State
- `api_project_script_route_TypeScript.prompt` only mentions `narrative/main_script.md`
- `Stage3TtsScriptGen.tsx` expects to fetch/save `tts_script.md` via the same API
- Stage 3 prompt line 5: "Loads content from `GET /api/project/script?file=tts`"
- But route prompt doesn't mention `?file` parameter support

### Affected Modules
- `app/api/project/script/route.ts` (needs update)
- `components/stages/Stage3TtsScriptGen.tsx` (auto-save will fail)

### Required Fix (OPTION A - RECOMMENDED)

**File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/prompts/api_project_script_route_TypeScript.prompt`

**Action**: Update to support both `main_script.md` and `tts_script.md`:

```diff
Requirements
1. `GET /api/project/script` — reads `narrative/main_script.md` by default.
   - Optional query param `?file=main` (default) or `?file=tts`
   - If `?file=main`: returns `narrative/main_script.md`
   - If `?file=tts`: returns `narrative/tts_script.md`
   - Returns `{ content: string }` with status 200
   - Returns HTTP 404 with `{ error: 'Script file not found' }` if file doesn't exist

2. `PUT /api/project/script` — writes to script file.
   - Optional query param `?file=main` (default) or `?file=tts`
   - Accepts `{ content: string }` body
   - If `?file=main`: writes to `narrative/main_script.md`
   - If `?file=tts`: writes to `narrative/tts_script.md`
   - Writes atomically (write to `.tmp` then rename)
   - Returns `{ ok: true }` with status 200
   - Returns HTTP 400 if `content` is missing or not a string

3. No authentication required.

4. Ensure the `narrative/` directory is created if it does not exist before writing.

Instructions
- Use `path.join(process.cwd(), 'narrative', filename)` where filename = 'main_script.md' | 'tts_script.md'
- Parse query param: `const file = request.nextUrl.searchParams.get('file') || 'main'`
- Map file param to filename: `file === 'tts' ? 'tts_script.md' : 'main_script.md'`
- REST: same as before (atomic write, 404 on missing, fs.mkdirSync recursive)
```

### Alternative: Option B (Separate Endpoint)

If you prefer to keep script.ts for main_script.md only, create a new endpoint:

**New prompt**: `api_pipeline_tts_script_file_route_TypeScript.prompt`
**Endpoints**:
- `GET /api/pipeline/tts-script/file` → returns tts_script.md content
- `PUT /api/pipeline/tts-script/file` → writes tts_script.md

Then update Stage3TtsScriptGen to call `/api/pipeline/tts-script/file` instead.

### Recommendation
**Use Option A** — it's minimal, backward-compatible, and keeps related endpoints together.

### Verification Checklist
- [ ] Update api_project_script_route_TypeScript.prompt with ?file param support
- [ ] Regenerate api_project_script_route.ts with updated prompt
- [ ] Update Stage3TtsScriptGen.tsx inline editor to pass ?file=tts in fetch calls:
  ```typescript
  const response = await fetch('/api/project/script?file=tts');
  // ... save also passes ?file=tts
  ```
- [ ] Test Stage 3 inline editor auto-save works

### Testing
```bash
# After fix:
curl 'http://localhost:3000/api/project/script?file=main'
# Should return narrative/main_script.md

curl 'http://localhost:3000/api/project/script?file=tts'
# Should return narrative/tts_script.md
```

---

## Issue 3: Remotion Project Bootstrap Unspecified (HIGH - Blocks Rendering)

### Current State
- No scaffold prompts for Remotion project structure
- `generate_section_compositions.py` references `remotion/src/remotion/Root.tsx` but doesn't create it
- No specification for `remotion/package.json`, `remotion/tsconfig.json`, `remotion/src/Video.tsx`
- Implementation must infer structure from incomplete specs

### Affected Modules
- `lib/render.ts` → calls `renderSection(compositionId)` (assumes Remotion project exists)
- `api_pipeline_compositions_route.ts` → depends on Remotion scaffold
- `scripts/generate_section_compositions.py` → writes to remotion/src/remotion/ (parent dirs may not exist)

### Required Fix

Create 2-3 new prompt modules:

#### New File 1: `remotion_root_tsx_TypeScriptReact.prompt`

**Purpose**: Root Composition container that registers all section compositions

**Content**:
```
You are implementing remotion/src/Root.tsx for a video production pipeline editor.
This file is the top-level Remotion composition that registers all generated section
compositions and the main video sequence.

Requirements
1. Export a Composition named 'MainVideo' with sequence covering all sections
2. All section compositions (generated by generate_section_compositions.py) are imported
   and registered as <Composition> elements in Remotion's composition registry
3. Accept props typed as ProjectConfig
4. Section timings are calculated from section.offsetSeconds + section.durationSeconds
5. Component hierarchy:
   - MainVideo (top-level) → Sequence (full duration) → per-section Sequences

Instructions
- Use @remotion/core: Composition, Sequence, AbsoluteFill
- Dynamically import section compositions from ./remotion/{sectionId}/
- Register each with Composition() API
- Read section list from project.json (passed as prop or loaded locally)

Deliverable
- remotion/src/Root.tsx — Composition registry with all sections
```

#### New File 2: `remotion_package_json_JSON.prompt`

**Purpose**: Remotion subproject package.json

**Content**:
```
You are creating remotion/package.json for the embedded Remotion project.

Requirements
1. dependencies: @remotion/core, @remotion/renderer, react, react-dom, tailwindcss
2. devDependencies: typescript, @types/react, @types/node, @remotion/eslint-config
3. scripts: dev (remotion preview), build (remotion render), test
4. Extends parent project's Node.js version (>=20)

Deliverable
- remotion/package.json
```

#### New File 3: `remotion_tsconfig_json_JSON.prompt`

**Purpose**: TypeScript configuration for Remotion

**Content**:
```
TypeScript config for Remotion subproject.
- Extends parent tsconfig.json or sets strict: true, lib: [ES2021, dom]
- target: ES2021
- module: ES2020
- jsx: react-jsx
- moduleResolution: bundler
```

### Alternative: Enhance `generate_section_compositions_Python.prompt`

Instead of new prompts, enhance the Python script to:
1. Create `remotion/src/Root.tsx` if it doesn't exist (with composition import stubs)
2. Create `remotion/package.json` if it doesn't exist
3. Create `remotion/tsconfig.json` if it doesn't exist

Add to `generate_section_compositions.py`:

```python
def bootstrap_remotion_if_needed(remotion_dir: str):
    """Create minimal Remotion project structure if missing."""
    # Create Root.tsx with composition imports
    # Create package.json with Remotion deps
    # Create tsconfig.json
```

### Recommendation
**Create new prompts (Option 1)** — cleaner separation of concerns, easier to maintain.

### Verification Checklist
- [ ] Create remotion_root_tsx_TypeScriptReact.prompt
- [ ] Create remotion_package_json_JSON.prompt
- [ ] Create remotion_tsconfig_json_JSON.prompt
- [ ] Regenerate all three files before running composition generation
- [ ] Verify remotion/ directory structure:
  ```
  remotion/
  ├── package.json
  ├── tsconfig.json
  ├── remotion.config.ts
  └── src/
      ├── Root.tsx (generated)
      ├── Video.tsx
      └── remotion/
          ├── section-1/
          │   └── index.tsx (generated by script)
          ├── section-2/
          │   └── index.tsx
          └── ...
  ```

### Testing
```bash
# After bootstrap:
cd remotion
npm install
npm run dev
# Should render MainVideo with all section compositions
```

---

## Issue 4: Python Requirements.txt Missing (LOW - Operational Gap)

### Current State
- Three Python scripts have dependencies listed in prompts but no central requirements.txt
- Deployment documentation unclear on how to set up Python environment

### Affected Scripts
- `scripts/render_tts.py` → uses `transformers`, `pydub`, `torch`
- `scripts/sync_audio_pipeline.py` → uses `pydub`, `faster-whisper`, `ffmpeg-python`
- `scripts/generate_section_compositions.py` → minimal external deps (just stdlib)

### Required Fix

**New File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/scripts/requirements.txt`

**Content**:
```
# Python dependencies for video editor pipeline scripts
# Install with: pip install -r scripts/requirements.txt

# TTS synthesis (render_tts.py)
transformers>=4.40.0
torch>=2.0.0
pydub>=0.25.0

# Audio sync and word-level timestamps (sync_audio_pipeline.py)
faster-whisper>=0.10.0
ffmpeg-python>=0.2.1
pydub>=0.25.0  # already listed above

# Optional: better CLI parsing
click>=8.0.0
```

### Alternative: Create pyproject.toml

For better modern Python packaging:

**New File**: `/Users/gregtanaka/Documents/pdd_cloud/pdd/video_editor_pdd/scripts/pyproject.toml`

```toml
[project]
name = "video-editor-scripts"
version = "0.1.0"
description = "Python scripts for video production pipeline"
dependencies = [
    "transformers>=4.40.0",
    "torch>=2.0.0",
    "pydub>=0.25.0",
    "faster-whisper>=0.10.0",
    "ffmpeg-python>=0.2.1",
    "click>=8.0.0",
]
```

### Recommendation
**Use requirements.txt** — simpler, Python standard, matches Node.js pattern.

### Verification Checklist
- [ ] Create /scripts/requirements.txt
- [ ] Test installation: `pip install -r scripts/requirements.txt`
- [ ] Update project README with Python setup instructions
- [ ] Add to .gitignore if using venv: `/scripts/.venv/`

### Testing
```bash
python -m venv /tmp/test-venv
source /tmp/test-venv/bin/activate
pip install -r scripts/requirements.txt
python scripts/render_tts.py --help
# Should show CLI help without import errors
```

---

## Summary & Quick Start

### Priority Order
1. **Fix types.ts** (30 min) - BLOCKS COMPILATION
2. **Fix TTS script endpoint** (15 min) - BLOCKS STAGE 3
3. **Add Remotion bootstrap** (60 min) - BLOCKS RENDERING
4. **Add requirements.txt** (10 min) - OPERATIONAL

### Total Estimated Remediation Time: ~2 hours

### Implementation Order
```bash
# 1. Update types.ts prompt
# 2. Update api_project_script_route prompt
# 3. Create remotion bootstrap prompts (3 new files)
# 4. Create scripts/requirements.txt
# 5. Regenerate all affected prompt files
# 6. Test: npm run build && npm run dev
```

---
