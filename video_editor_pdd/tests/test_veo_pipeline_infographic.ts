import fs from "fs";
import path from "path";

describe("Veo pipeline infographic arrows", () => {
  const pipelineArrowPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection06VeoPipelineInfographic/PipelineArrow.tsx"
  );

  it("draws the visible arrow segment directly instead of relying on SVG clipPath masking", () => {
    const source = fs.readFileSync(pipelineArrowPath, "utf8");

    expect(source).toContain("const visibleLineEndX = Math.min");
    expect(source).toContain("x2={visibleLineEndX}");
    expect(source).not.toContain("clipPath");
    expect(source).not.toContain("<defs>");
  });
});
