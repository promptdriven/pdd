import fs from "fs";
import os from "os";
import path from "path";

import {
  applyVeoPromptFixForAnnotation,
  extractSuggestedVeoPrompt,
} from "@/lib/veo-prompt-fix";

describe("veo prompt fix helpers", () => {
  it("extracts an explicit prompt rewrite from suggested fixes", () => {
    const prompt = extractSuggestedVeoPrompt({
      text: "I want birds in the sky",
      analysis: {
        severity: "major",
        fixType: "veo",
        technicalAssessment: "Birds require regenerated footage",
        suggestedFixes: [
          'Update the Veo prompt to: "A calm ocean wave at sunset with birds in the sky"',
        ],
        confidence: 0.9,
      },
    });

    expect(prompt).toBe("A calm ocean wave at sunset with birds in the sky");
  });

  it("rewrites the targeted Veo spec marker and JSON prompt before regeneration", () => {
    const projectDir = fs.mkdtempSync(path.join(os.tmpdir(), "veo-prompt-fix-"));
    const specDir = path.join(projectDir, "specs", "veo_section");
    fs.mkdirSync(specDir, { recursive: true });

    fs.writeFileSync(
      path.join(specDir, "02_ocean_wave_sunset.md"),
      [
        "[veo:]",
        "",
        "# Ocean",
        "",
        "**Timestamp:** 0:03 - 0:06",
        "",
        "## Data Points",
        "```json",
        "{",
        '  "veoPrompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",',
        '  "clipSource": "veo/ocean_wave_sunset.mp4"',
        "}",
        "```",
      ].join("\n")
    );

    fs.writeFileSync(
      path.join(specDir, "04_forest_canopy_aerial.md"),
      [
        "[veo:]",
        "",
        "# Forest",
        "",
        "**Timestamp:** 0:09 - 0:12",
        "",
        "## Data Points",
        "```json",
        "{",
        '  "veoPrompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",',
        '  "clipSource": "veo/forest_canopy_aerial.mp4"',
        "}",
        "```",
      ].join("\n")
    );

    const patch = applyVeoPromptFixForAnnotation(
      projectDir,
      {
        id: "veo_section",
        label: "Veo Section",
        specDir: "veo_section",
        compositionId: "VeoSection",
        durationSeconds: 11,
        offsetSeconds: 0,
        compositions: [
          { id: "ocean_wave_sunset", startSeconds: 1, durationSeconds: 1.5 },
          { id: "forest_canopy_aerial", startSeconds: 4, durationSeconds: 1.5 },
        ],
      },
      {
        text: "I want birds in the sky",
        timestamp: 1.3,
        analysis: {
          severity: "major",
          fixType: "veo",
          technicalAssessment: "Birds require regenerated footage",
          suggestedFixes: [
            'Update the Veo prompt to: "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion, birds flying in the sky on the right side of frame"',
          ],
          confidence: 0.9,
        },
      }
    );

    expect(patch).toEqual(
      expect.objectContaining({
        clipId: "ocean_wave_sunset",
        prompt:
          "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion, birds flying in the sky on the right side of frame",
      })
    );

    const updatedOceanSpec = fs.readFileSync(
      path.join(specDir, "02_ocean_wave_sunset.md"),
      "utf-8"
    );
    expect(updatedOceanSpec).toContain(
      "[veo: A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion, birds flying in the sky on the right side of frame]"
    );
    expect(updatedOceanSpec).toContain(
      '"veoPrompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion, birds flying in the sky on the right side of frame"'
    );

    const untouchedForestSpec = fs.readFileSync(
      path.join(specDir, "04_forest_canopy_aerial.md"),
      "utf-8"
    );
    expect(untouchedForestSpec).not.toContain("birds flying in the sky");
  });
});
