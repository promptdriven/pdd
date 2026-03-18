import fs from "fs";
import path from "path";

describe("shared generated media renderer", () => {
  const generatedMediaVisualPath = path.join(
    process.cwd(),
    "remotion/src/remotion/_shared/GeneratedMediaVisual.tsx"
  );
  const veoSectionPath = path.join(
    process.cwd(),
    "remotion/src/remotion/veo_section/index.tsx"
  );

  it("supports split media layouts from shared visual aliases instead of only a single defaultSrc", () => {
    const source = fs.readFileSync(generatedMediaVisualPath, "utf8");

    expect(source).toMatch(/const\s+leftSrc\s*=\s*useVisualMediaSrc\(\s*["']leftSrc["']/);
    expect(source).toMatch(/const\s+rightSrc\s*=\s*useVisualMediaSrc\(\s*["']rightSrc["']/);
    expect(source).toMatch(/leftSrc\s*&&\s*rightSrc/);
    expect(source).toMatch(/borderRadius/);
    expect(source).toMatch(/Ocean · Sunset|resolvePanelLabel|leftLabel/);
  });

  it("routes split media visuals through GeneratedMediaVisual when left/right aliases exist", () => {
    const source = fs.readFileSync(veoSectionPath, "utf8");

    expect(source).toMatch(/visualOverlayConfig\s*\|\|\s*visualMedia\?\.leftSrc\s*\|\|\s*visualMedia\?\.rightSrc/);
    expect(source).toMatch(/<GeneratedMediaVisual config=\{visualOverlayConfig\} \/>/);
  });

  it("uses asset-resolved media hooks in generated components that pass Veo sources directly to video elements", () => {
    const directVideoComponents = [
      path.join(
        process.cwd(),
        "remotion/src/remotion/ColdOpen01SplitScreenHook/ColdOpen01SplitScreenHook.tsx"
      ),
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift04DefectFixTheMold/Part2ParadigmShift04DefectFixTheMold.tsx"
      ),
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part5CompoundReturns06SockCallbackSplit/Part5CompoundReturns06SockCallbackSplit.tsx"
      ),
    ];

    for (const componentPath of directVideoComponents) {
      const source = fs.readFileSync(componentPath, "utf8");
      expect(source).toContain("useVisualMediaAssetSrc");
      expect(source).not.toMatch(/const\s+\w+Src\s*=\s*useVisualMediaSrc\(/);
    }
  });
});

describe("reusable animation template defaults", () => {
  const splitConstantsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection05SplitComparison/constants.ts"
  );
  const particleConstantsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection06ParticleBurst/constants.ts"
  );
  const particlePath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection06ParticleBurst/Particle.tsx"
  );
  const particleMotionPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection06ParticleBurst/motion.ts"
  );
  const keyVisualPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection08KeyVisual/AnimationSection08KeyVisual.tsx"
  );
  const keyVisualConstantsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection08KeyVisual/constants.ts"
  );
  const waveOverlayPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/VeoSection03WaveDataOverlay.tsx"
  );
  const waveOverlayConstantsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection03WaveDataOverlay/constants.ts"
  );
  const splitSummaryPath = path.join(
    process.cwd(),
    "remotion/src/remotion/AnimationSection09SplitSummary/GlowingDivider.tsx"
  );
  const infographicPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05VeoPipelineInfographic/VeoSection05VeoPipelineInfographic.tsx"
  );
  const infographicConstantsPath = path.join(
    process.cwd(),
    "remotion/src/remotion/VeoSection05VeoPipelineInfographic/constants.ts"
  );

  it("keeps split comparison labels above centered shapes at the spec positions", () => {
    const source = fs.readFileSync(splitConstantsPath, "utf8");

    expect(source).toMatch(/circleCenterY:\s*540/);
    expect(source).toMatch(/squareCenterY:\s*540/);
    expect(source).toMatch(/circleRadius:\s*50/);
    expect(source).toMatch(/squareSize:\s*100/);
    expect(source).toMatch(/labelY:\s*420/);
  });

  it("uses the near-black particle burst background and fades particles through the configured fade window", () => {
    const constantsSource = fs.readFileSync(particleConstantsPath, "utf8");
    const particleSource = fs.readFileSync(particlePath, "utf8");
    const particleMotionSource = fs.readFileSync(particleMotionPath, "utf8");

    expect(constantsSource).toContain("background: '#020617'");
    expect(constantsSource).toContain("tailStartOpacity: 0.35");
    expect(particleSource).toContain("resolveParticleOpacity");
    expect(particleMotionSource).toContain("TIMING.particleMoveEnd");
    expect(particleMotionSource).toContain("PARTICLES.tailStartOpacity");
  });

  it("anchors key visual bars to the bottom and reads heights from the structured contract", () => {
    const source = fs.readFileSync(keyVisualPath, "utf8");
    const constantsSource = fs.readFileSync(keyVisualConstantsPath, "utf8");

    expect(source).toMatch(/alignItems:\s*['"]flex-end['"]/);
    expect(source).toMatch(/bottom:/);
    expect(constantsSource).toMatch(/height:\s*300/);
    expect(constantsSource).toMatch(/height:\s*420/);
    expect(constantsSource).toMatch(/height:\s*260/);
    expect(constantsSource).toMatch(/height:\s*500/);
  });

  it("removes the wave overlay placeholder green fills and uses the gold spec palette", () => {
    const source = fs.readFileSync(waveOverlayPath, "utf8");
    const constantsSource = fs.readFileSync(waveOverlayConstantsPath, "utf8");

    expect(source).not.toContain("#00FF00");
    expect(source).toContain("resolveWaveOverlayBadges");
    expect(constantsSource).toContain("x: 120");
    expect(constantsSource).toContain("x: 860");
    expect(constantsSource).toContain("x: 1600");
  });

  it("keeps split summary divider rendering in the live component path covered by tests", () => {
    const source = fs.readFileSync(splitSummaryPath, "utf8");

    expect(source).toContain("dividerX");
    expect(source).toContain("DIVIDER.endX");
    expect(source).toContain("backgroundColor: DIVIDER.color");
  });

  it("drives infographic node sizing and positioning from the structured contract instead of hardcoded demo dimensions", () => {
    const source = fs.readFileSync(infographicPath, "utf8");
    const constantsSource = fs.readFileSync(infographicConstantsPath, "utf8");

    expect(source).toMatch(/useVisualContractData/);
    expect(source).toMatch(/resolvePipelineNodes/);
    expect(constantsSource).toContain("nodeWidth: 160");
    expect(constantsSource).toContain("nodeHeight: 160");
    expect(constantsSource).toContain('node1X: 330');
    expect(constantsSource).toContain('node2X: 870');
    expect(constantsSource).toContain('node3X: 1410');
  });
});
