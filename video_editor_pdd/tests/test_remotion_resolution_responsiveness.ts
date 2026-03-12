import fs from "fs";
import path from "path";

describe("resolution-aware Veo overlays", () => {
  const titleCardPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection01TitleCard/VeoSection01TitleCard.tsx"
  );
  const titleTextPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection01TitleCard/TitleText.tsx"
  );
  const horizontalRulePath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection01TitleCard/HorizontalRule.tsx"
  );
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
  const splitComparisonPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05SplitNatureComparison/VeoSection05SplitNatureComparison.tsx"
  );
  const splitPanelPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05SplitNatureComparison/SplitPanel.tsx"
  );
  const splitLabelPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05SplitNatureComparison/PanelLabel.tsx"
  );
  const splitDividerPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05SplitNatureComparison/VerticalDivider.tsx"
  );
  const narrationOverlayPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection07NarrationOverlayIntro/VeoSection07NarrationOverlayIntro.tsx"
  );

  it("derives the Veo title card layout from the active video config", () => {
    const source = fs.readFileSync(titleCardPath, "utf8");

    expect(source).toMatch(/useVideoConfig/);
    expect(source).toMatch(/const\s*\{\s*width,\s*height\s*\}\s*=\s*useVideoConfig\(\)/);
  });

  it("avoids hardcoded 1920x1080 sizing in the Veo title card children", () => {
    const titleSource = fs.readFileSync(titleTextPath, "utf8");
    const ruleSource = fs.readFileSync(horizontalRulePath, "utf8");

    expect(titleSource).not.toMatch(/width:\s*CANVAS\.width/);
    expect(titleSource).not.toMatch(/height:\s*CANVAS\.height/);
    expect(ruleSource).not.toMatch(/CANVAS\.width\s*\/\s*2/);
    expect(ruleSource).not.toMatch(/CANVAS\.height\s*\/\s*2/);
  });

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

  it("derives the split nature comparison layout from the active video config", () => {
    const source = fs.readFileSync(splitComparisonPath, "utf8");

    expect(source).toMatch(/useVideoConfig/);
    expect(source).toMatch(/const\s*\{\s*width,\s*height\s*\}\s*=\s*useVideoConfig\(\)/);
  });

  it("resolves split nature comparison media through shared visual aliases instead of hardcoded demo asset names", () => {
    const source = fs.readFileSync(splitComparisonPath, "utf8");

    expect(source).toMatch(/useVisualMediaSrc/);
    expect(source).toMatch(/leftSrc\s*=\s*useVisualMediaSrc\(\s*['"]leftSrc['"]/);
    expect(source).toMatch(/rightSrc\s*=\s*useVisualMediaSrc\(\s*['"]rightSrc['"]/);
    expect(source).not.toContain("veo/ocean_sunset.mp4");
    expect(source).not.toContain("veo/aerial_forest.mp4");
  });

  it("avoids hardcoded 1920x1080 sizing in the split nature comparison children", () => {
    const panelSource = fs.readFileSync(splitPanelPath, "utf8");
    const labelSource = fs.readFileSync(splitLabelPath, "utf8");
    const dividerSource = fs.readFileSync(splitDividerPath, "utf8");

    expect(panelSource).not.toMatch(/CANVAS\.width/);
    expect(panelSource).not.toMatch(/CANVAS\.height/);
    expect(labelSource).not.toMatch(/DIMENSIONS\.leftLabelX/);
    expect(labelSource).not.toMatch(/DIMENSIONS\.rightLabelX/);
    expect(dividerSource).not.toMatch(/DIMENSIONS\.dividerX/);
    expect(dividerSource).not.toMatch(/CANVAS\.height/);
  });

  it("keeps the narration overlay preview transparent so it can audit as an overlay layer", () => {
    const source = fs.readFileSync(narrationOverlayPath, "utf8");

    expect(source).toContain("pointerEvents: 'none'");
    expect(source).not.toContain("backgroundColor: '#0A1628'");
  });
});
