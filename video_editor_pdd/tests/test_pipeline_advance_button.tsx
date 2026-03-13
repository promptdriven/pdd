import fs from "fs";
import path from "path";

const SOURCE_PATH = path.join(
  __dirname,
  "..",
  "components",
  "PipelineAdvanceButton.tsx"
);
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

describe("PipelineAdvanceButton", () => {
  it("exists at the expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("defaults the label to Continue →", () => {
    expect(sourceCode).toMatch(/label\s*=\s*['"]Continue →['"]/);
  });

  it("uses the shared emerald styling", () => {
    expect(sourceCode).toContain("bg-emerald-600");
    expect(sourceCode).toContain("hover:bg-emerald-700");
    expect(sourceCode).toContain("text-white");
  });

  it("uses the shared disabled styling", () => {
    expect(sourceCode).toContain("disabled:bg-slate-700");
    expect(sourceCode).toContain("disabled:text-slate-500");
    expect(sourceCode).toContain("disabled:cursor-not-allowed");
  });

  it("renders a button element wired to onClick and disabled", () => {
    expect(sourceCode).toMatch(/<button/);
    expect(sourceCode).toMatch(/onClick=\{onClick\}/);
    expect(sourceCode).toMatch(/disabled=\{disabled\}/);
  });
});
