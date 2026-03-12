import fs from "fs";
import path from "path";

describe("resolution-aware Veo overlays", () => {
  const waveOverlayPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/VeoSection03WaveDataOverlay.tsx"
  );
  const gradientOverlayPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/GradientOverlay.tsx"
  );
  const sineWavePathPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/SineWavePath.tsx"
  );
  const accentDotsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/AccentDots.tsx"
  );
  const statCalloutPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/StatCallout.tsx"
  );
  const pipelineInfographicPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection06VeoPipelineInfographic/VeoSection06VeoPipelineInfographic.tsx"
  );
  const pipelineArrowPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection06VeoPipelineInfographic/PipelineArrow.tsx"
  );
  const pipelineNodePath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection06VeoPipelineInfographic/PipelineNode.tsx"
  );

  it("derives the wave data overlay layout from the active video config", () => {
    const source = fs.readFileSync(waveOverlayPath, "utf8");

    expect(source).toMatch(/useVideoConfig/);
    expect(source).toMatch(/const\s*\{\s*width,\s*height\s*\}\s*=\s*useVideoConfig\(\)/);
    expect(source).not.toMatch(/width:\s*CANVAS\.width/);
    expect(source).not.toMatch(/height:\s*CANVAS\.height/);
  });

  it("avoids hardcoded 1920x1080 sizing in the wave data overlay children", () => {
    const gradientSource = fs.readFileSync(gradientOverlayPath, "utf8");
    const sineWaveSource = fs.readFileSync(sineWavePathPath, "utf8");
    const dotsSource = fs.readFileSync(accentDotsPath, "utf8");
    const calloutSource = fs.readFileSync(statCalloutPath, "utf8");

    expect(gradientSource).not.toMatch(/width:\s*CANVAS\.width/);
    expect(gradientSource).not.toMatch(/height:\s*CANVAS\.height/);
    expect(sineWaveSource).not.toMatch(/width=\{CANVAS\.width\}/);
    expect(sineWaveSource).not.toMatch(/height=\{CANVAS\.height\}/);
    expect(dotsSource).not.toMatch(/DOTS\.positions/);
    expect(calloutSource).not.toMatch(/left:\s*STAT_X/);
  });

  it("derives the pipeline infographic layout from the active video config", () => {
    const source = fs.readFileSync(pipelineInfographicPath, "utf8");

    expect(source).toMatch(/useVideoConfig/);
    expect(source).toMatch(/const\s*\{\s*width,\s*height\s*\}\s*=\s*useVideoConfig\(\)/);
    expect(source).not.toMatch(/width:\s*CANVAS\.width/);
  });

  it("avoids hardcoded 1920x1080 sizing in the pipeline infographic children", () => {
    const arrowSource = fs.readFileSync(pipelineArrowPath, "utf8");
    const nodeSource = fs.readFileSync(pipelineNodePath, "utf8");

    expect(arrowSource).not.toMatch(/width:\s*1920/);
    expect(arrowSource).not.toMatch(/height:\s*1080/);
    expect(nodeSource).not.toMatch(/POSITIONS\.nodeY/);
    expect(nodeSource).not.toMatch(/POSITIONS\.descriptorY/);
  });
});
