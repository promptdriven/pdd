import fs from "fs";
import os from "os";
import path from "path";

import { applyRemotionSpecFixForAnnotation } from "@/lib/remotion-spec-fix";

describe("remotion spec fix helpers", () => {
  it("writes an annotation revision block into the targeted spec file", () => {
    const tempDir = fs.mkdtempSync(path.join(os.tmpdir(), "remotion-spec-fix-"));
    const specDir = path.join(tempDir, "specs", "animation_section");
    fs.mkdirSync(specDir, { recursive: true });

    const titleCardPath = path.join(specDir, "01_title_card.md");
    const squarePath = path.join(specDir, "03_square.md");

    fs.writeFileSync(
      titleCardPath,
      `# Title Card\n\n**Timestamp:** 0:00 - 0:02\n`,
      "utf-8"
    );
    fs.writeFileSync(
      squarePath,
      `# Square Visual\n\n**Timestamp:** 0:02 - 0:04\n`,
      "utf-8"
    );

    const patch = applyRemotionSpecFixForAnnotation(
      tempDir,
      {
        id: "animation_section",
        label: "Animation Section",
        specDir: "animation_section",
        durationSeconds: 4,
        offsetSeconds: 0,
        compositionId: "AnimationSection",
        compositions: ["01_title_card", "03_square"],
      },
      {
        id: "ann-remotion-1",
        timestamp: 2.6,
        text: "Make this square yellow",
        analysis: {
          severity: "major",
          fixType: "remotion",
          technicalAssessment: "The centered square should be yellow instead of green.",
          suggestedFixes: [
            "Change the square fill to #EAB308 in the spec and component.",
          ],
          confidence: 0.9,
        },
      }
    );

    expect(patch).toEqual({
      specPath: squarePath,
      note: "Make this square yellow",
    });

    const updatedSquareSpec = fs.readFileSync(squarePath, "utf-8");
    expect(updatedSquareSpec).toContain("<!-- ANNOTATION_UPDATE_START: ann-remotion-1 -->");
    expect(updatedSquareSpec).toContain("## Annotation Update");
    expect(updatedSquareSpec).toContain("Requested change: Make this square yellow");
    expect(updatedSquareSpec).toContain("Technical assessment: The centered square should be yellow instead of green.");
    expect(updatedSquareSpec).toContain("Change the square fill to #EAB308 in the spec and component.");

    const unchangedTitleCardSpec = fs.readFileSync(titleCardPath, "utf-8");
    expect(unchangedTitleCardSpec).not.toContain("ANNOTATION_UPDATE_START");
  });
});
