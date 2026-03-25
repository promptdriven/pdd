import {
  evaluateDeterministicTextAudit,
  type AuditImageEvidence,
} from "../lib/audit-evidence";

describe("evaluateDeterministicTextAudit", () => {
  const auditHints = {
    criticalElements: ["Summary line", "Equivalent diagram", "Prompt label"],
    decorativeElements: [],
    layoutKeywords: [],
    transitionWindows: [],
  };

  const strongEvidence: AuditImageEvidence = {
    normalizedText:
      "summary line equivalent diagram prompt label bridge text all clearly visible",
    textTokenCount: 10,
    contrastScore: 22,
    ocrText:
      "Summary line Equivalent diagram Prompt label bridge text all clearly visible",
  };

  it("upgrades clipped-or-missing text failures to pass when OCR confirms the full critical labels", () => {
    const result = evaluateDeterministicTextAudit(
      {
        severity: "major",
        fixType: "remotion",
        technicalAssessment:
          "The summary line and equivalent diagram text are missing from the frame, and the prompt label is clipped.",
        suggestedFixes: ["Restore the missing labels.", "Prevent the prompt label from clipping."],
        confidence: 0.71,
      },
      auditHints,
      strongEvidence
    );

    expect(result?.verdict).toBe("pass");
    expect(result?.summary).toMatch(/clipped-or-missing text failure/i);
  });

  it("upgrades major missing-text verdicts to pass when OCR strongly confirms multiple critical elements and no non-text issue remains", () => {
    const result = evaluateDeterministicTextAudit(
      {
        severity: "major",
        fixType: "remotion",
        technicalAssessment:
          "The summary line, equivalent diagram, and prompt label are missing from the frame.",
        suggestedFixes: ["Restore the missing labels."],
        confidence: 0.71,
      },
      auditHints,
      strongEvidence
    );

    expect(result?.verdict).toBe("pass");
    expect(result?.summary).toMatch(/multiple critical text/i);
  });

  it("upgrades minor missing-text verdicts to pass when OCR strongly confirms the claimed labels", () => {
    const result = evaluateDeterministicTextAudit(
      {
        severity: "minor",
        fixType: "remotion",
        technicalAssessment:
          "The prompt label is not visible enough in the sampled frame.",
        suggestedFixes: ["Increase the label opacity."],
        confidence: 0.62,
      },
      auditHints,
      strongEvidence
    );

    expect(result?.verdict).toBe("pass");
  });

  it("returns null when OCR evidence is too weak to override Claude", () => {
    const result = evaluateDeterministicTextAudit(
      {
        severity: "major",
        fixType: "remotion",
        technicalAssessment: "The prompt label is missing.",
        suggestedFixes: ["Restore the label."],
        confidence: 0.87,
      },
      auditHints,
      {
        normalizedText: "noise",
        textTokenCount: 1,
        contrastScore: 4,
        ocrText: "noise",
      }
    );

    expect(result).toBeNull();
  });

  it("keeps layout-sensitive text complaints at warn when OCR cannot disprove the positioning issue", () => {
    const result = evaluateDeterministicTextAudit(
      {
        severity: "major",
        fixType: "remotion",
        technicalAssessment:
          "The summary line is missing and the prompt label is misaligned under the diagram.",
        suggestedFixes: ["Restore the missing summary line.", "Move the prompt label into position."],
        confidence: 0.8,
      },
      auditHints,
      strongEvidence
    );

    expect(result?.verdict).toBe("warn");
  });
});
