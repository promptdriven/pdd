import fs from 'fs';
import path from 'path';

export interface ProjectSectionFixture {
  id: string;
  label: string;
  compositionId: string;
  durationSeconds?: number;
}

interface ProjectFixture {
  name: string;
  outputResolution: {
    width: number;
    height: number;
  };
  tts: {
    speaker: string;
    speakingRate: number;
    sampleRate: number;
  };
  veo: {
    model: string;
    defaultAspectRatio: string;
    references?: Array<{ id: string; label: string }>;
  };
  render: {
    maxParallelRenders: number;
  };
  sections: ProjectSectionFixture[];
}

type RenderStatus = 'missing' | 'rendering' | 'done' | 'error';
type AuditStatus = 'pending' | 'running' | 'done' | 'error';

const PROJECT_JSON_PATH = path.join(__dirname, '..', '..', '..', 'project.json');

export function loadActiveProjectFixture(): ProjectFixture {
  return JSON.parse(fs.readFileSync(PROJECT_JSON_PATH, 'utf8')) as ProjectFixture;
}

export function getProjectSections(): ProjectSectionFixture[] {
  return loadActiveProjectFixture().sections;
}

export function buildMockRenderStatus(options?: {
  firstSectionStatus?: RenderStatus;
  remainingStatus?: RenderStatus;
  fullVideoExists?: boolean;
}) {
  const project = loadActiveProjectFixture();
  const sections = project.sections.map((section, index) => {
    const status =
      index === 0
        ? options?.firstSectionStatus ?? 'done'
        : options?.remainingStatus ?? 'missing';
    const progress = status === 'done' ? 100 : status === 'rendering' ? 50 : 0;

    return {
      id: section.id,
      durationSeconds: section.durationSeconds ?? 0,
      status,
      progress,
    };
  });

  return {
    sections,
    fullVideo: {
      exists: options?.fullVideoExists ?? true,
      sizeBytes: options?.fullVideoExists === false ? undefined : 1024 * 1024,
      durationSeconds: options?.fullVideoExists === false
        ? undefined
        : project.sections.reduce(
            (total, section) => total + (section.durationSeconds ?? 0),
            0,
          ),
    },
  };
}

export function buildMockAuditResults(options?: { status?: AuditStatus }) {
  const project = loadActiveProjectFixture();
  return {
    sections: project.sections.map((section, index) => ({
      sectionId: section.id,
      sectionLabel: section.label,
      passCount: 1,
      failCount: index === 0 ? 1 : 0,
      status: options?.status ?? 'done',
      specs: [
        {
          specName: 'text_readable',
          verdict: 'PASS',
          summary: 'Looks good',
          specPath: `/specs/${section.id}/text_readable.yaml`,
        },
        {
          specName: 'framing',
          verdict: index === 0 ? 'FAIL' : 'PASS',
          summary: index === 0 ? 'Needs adjustment' : 'Framing is stable',
          finding: index === 0 ? 'Subject drifts off-center' : undefined,
          specPath: `/specs/${section.id}/framing.yaml`,
        },
      ],
    })),
  };
}
