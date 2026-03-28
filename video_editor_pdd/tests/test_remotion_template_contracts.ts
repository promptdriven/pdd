import fs from "fs";
import path from "path";

describe("shared generated media renderer", () => {
  const generatedMediaVisualPath = path.join(
    process.cwd(),
    "remotion/src/remotion/_shared/GeneratedMediaVisual.tsx"
  );
  const compositionGeneratorPath = path.join(
    process.cwd(),
    "scripts/generate_section_compositions.py"
  );

  it("supports split media layouts from shared visual aliases instead of only a single defaultSrc", () => {
    const source = fs.readFileSync(generatedMediaVisualPath, "utf8");

    expect(source).toMatch(/const\s+leftSrc\s*=\s*useVisualMediaAssetSrc\(\s*["']leftSrc["']/);
    expect(source).toMatch(/const\s+rightSrc\s*=\s*useVisualMediaAssetSrc\(\s*["']rightSrc["']/);
    expect(source).toMatch(/leftSrc\s*&&\s*rightSrc/);
    expect(source).toMatch(/borderRadius/);
    expect(source).toMatch(/resolvePanelMetadata|leftPanel|rightPanel/);
  });

  it("routes split media visuals through GeneratedMediaVisual when left/right aliases exist", () => {
    const source = fs.readFileSync(compositionGeneratorPath, "utf8");

    expect(source).toMatch(/needs_generated_media_visual\s*=\s*any\(/);
    expect(source).toMatch(/aliases\.get\('leftSrc'\)/);
    expect(source).toMatch(/aliases\.get\('rightSrc'\)/);
    expect(source).toMatch(/visualOverlayConfig \|\| visualMedia\?\.leftSrc \|\| visualMedia\?\.rightSrc/);
    expect(source).toMatch(/<GeneratedMediaVisual config=\{visualOverlayConfig\} \/>/);
  });

  it("supports generic generated-media overlays for counters and readable split metadata from the structured contract", () => {
    const source = fs.readFileSync(generatedMediaVisualPath, "utf8");

    expect(source).toMatch(/counterOverlay|counterPosition/);
    expect(source).toMatch(/terminalSnippet|costLabel|costSubLabel|caption/);
    expect(source).toMatch(/crossedOutIcon/);
    expect(source).toMatch(/Math\.max\(\s*18|Math\.max\(\s*20/);
  });

  it("supports authored fade windows for raw-media callback specs instead of rendering clips at full opacity for the entire slot", () => {
    const source = fs.readFileSync(generatedMediaVisualPath, "utf8");

    expect(source).toMatch(/fadeInFrames|fadeOutFrames/);
    expect(source).toMatch(/useCurrentFrame/);
    expect(source).toMatch(/opacity/);
    expect(source).toMatch(/interpolate\(/);
  });

  it("uses asset-resolved media hooks in generated components that pass Veo sources directly to video elements", () => {
    const directVideoComponents = [
      path.join(
        process.cwd(),
        "remotion/src/remotion/ColdOpen01SplitScreenHook/ColdOpen01SplitScreenHook.tsx"
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

  it("keeps Part1 sock-chart tick interpolation input ranges strictly ascending", () => {
    const source = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part1Economics02SockEconomicsChart/ChartAxes.tsx"
      ),
      "utf8"
    );

    expect(source).toContain("[py, py + 10]");
    expect(source).not.toContain("[py + 10, py]");
  });

  it("keeps compiler icon animation props aligned with generated scene callers", () => {
    const source = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift07VerilogSynthesisTriple/CompilerIcon.tsx"
      ),
      "utf8"
    );
    const constantsSource = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift07VerilogSynthesisTriple/constants.ts"
      ),
      "utf8"
    );

    expect(source).toMatch(/startFrame\?: number/);
    expect(source).toMatch(/label\?: string/);
    expect(source).toMatch(/const resolvedAppearStart = typeof startFrame === "number" \? startFrame : appearStart \?\? 0;/);
    expect(source).toMatch(/const resolvedAppearEnd = typeof appearEnd === "number" \? appearEnd : resolvedAppearStart \+ 15;/);
    expect(constantsSource).toContain("export const COMPILER_OPACITY =");
    expect(constantsSource).toContain("export const COMPILER_LABEL_OPACITY =");
    expect(constantsSource).toContain("export const COMPILER_LABEL_SIZE =");
    expect(constantsSource).toContain("export const UI_FONT =");
  });

  it("uses Remotion's supported exponential easing helper in the Part 1 crossing-lines flash effect", () => {
    const source = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part1Economics13CrossingLinesMoment/RadialFlash.tsx"
      ),
      "utf8"
    );

    expect(source).toContain("Easing.out(Easing.exp)");
    expect(source).not.toContain("Easing.expo");
  });

  it("keeps frame-gated helpers hook-safe by resolving memoized values before early frame returns", () => {
    const cases = [
      {
        file: "remotion/src/remotion/Part2ParadigmShift12VerilogSynthesis/GateStream.tsx",
        returnSnippet: "if (frame < GATE_STREAM_START) return null;",
        hookSnippet: "const gates = useMemo<GateSymbol[]>(() => {",
      },
      {
        file: "remotion/src/remotion/Part2ParadigmShift18PromptMoldFinale/CodeFlow.tsx",
        returnSnippet: "if (localFrame < 0) return null;",
        hookSnippet: "const particles = useMemo(",
      },
      {
        file: "remotion/src/remotion/09-ContextDegradationChart/TrendLine.tsx",
        returnSnippet: "if (frame < startFrame) return null;",
        hookSnippet: "const pathD = useMemo(() => {",
      },
    ];

    for (const { file, returnSnippet, hookSnippet } of cases) {
      const source = fs.readFileSync(path.join(process.cwd(), file), "utf8");
      const returnIndex = source.indexOf(returnSnippet);
      const hookIndex = source.indexOf(hookSnippet);

      expect(returnIndex).toBeGreaterThanOrEqual(0);
      expect(hookIndex).toBeGreaterThanOrEqual(0);
      expect(hookIndex).toBeLessThan(returnIndex);
    }
  });

  it("keeps gate netlist animation props aligned with generated scene callers", () => {
    const source = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift07VerilogSynthesisTriple/GateNetlist.tsx"
      ),
      "utf8"
    );
    const constantsSource = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift07VerilogSynthesisTriple/constants.ts"
      ),
      "utf8"
    );

    expect(source).toMatch(/layout\?: "horizontal" \| "horizontal_compact" \| "vertical_long" \| "mixed_optimized"/);
    expect(source).toMatch(/startFrame\?: number/);
    expect(source).toMatch(/const resolvedDrawStart = typeof startFrame === "number" \? startFrame : drawStart \?\? 0;/);
    expect(source).toMatch(/const resolvedLayout = typeof layoutIndex === "number"/);
    expect(constantsSource).toContain("export const GATE_OPACITY =");
    expect(constantsSource).toContain("export const WIRE_OPACITY =");
  });

  it("keeps abstraction staircase helper exports aligned with scene imports", () => {
    const sceneSource = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift09AbstractionStaircase/Part2ParadigmShift09AbstractionStaircase.tsx"
      ),
      "utf8"
    );
    const pulsingGlowSource = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift09AbstractionStaircase/PulsingGlow.tsx"
      ),
      "utf8"
    );
    const constantsSource = fs.readFileSync(
      path.join(
        process.cwd(),
        "remotion/src/remotion/Part2ParadigmShift09AbstractionStaircase/constants.ts"
      ),
      "utf8"
    );

    expect(sceneSource).toContain("import PulsingGlow from './PulsingGlow';");
    expect(pulsingGlowSource).toContain("export default PulsingGlow;");
    expect(constantsSource).toContain("export const ACTIVE_COLOR =");
    expect(constantsSource).toContain("export const PULSE_PERIOD =");
  });
});

describe("shared generated contract renderer", () => {
  const generatedContractVisualPath = path.join(
    process.cwd(),
    "remotion/src/remotion/_shared/GeneratedContractVisual.tsx"
  );
  const extractBlock = (source: string, startMarker: string, endMarker: string) => {
    const start = source.indexOf(startMarker);
    const end = source.indexOf(endMarker, start + 1);

    expect(start).toBeGreaterThanOrEqual(0);
    expect(end).toBeGreaterThan(start);

    return source.slice(start, end);
  };

  it("supports typed contract renderers for the authored fallback visual families instead of collapsing them into the generic diagram placeholder", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/visualType === "title_card"/);
    expect(source).toMatch(/visualType === "quote_card"/);
    expect(source).toMatch(/visualType === "transition"/);
    expect(source).toMatch(/visualType === "code_visualization"/);
    expect(source).toMatch(/visualType === "code_transformation"/);
    expect(source).toMatch(/visualType === "network_graph"/);
    expect(source).toMatch(/visualType === "dual_meter_animation"/);
    expect(source).toMatch(/visualType === "annotation_overlay"/);
    expect(source).toMatch(/visualType === "text_overlay_with_morph"/);
    expect(source).toMatch(/visualType === "animated_diagram"/);
  });

  it("can read split-panel media aliases from the visual contract runtime for contract-backed component fallbacks", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/useVisualMediaAssetSrc\(\s*["']leftSrc["']\s*\)/);
    expect(source).toMatch(/useVisualMediaAssetSrc\(\s*["']rightSrc["']\s*\)/);
    expect(source).toMatch(/OffthreadVideo/);
  });

  it("supports structured title cards and stillness beats without collapsing them into generic centered text", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const ghostBlock = extractBlock(source, "const GhostElements", "const TitleCardVisual");
    const titleBlock = extractBlock(source, "const TitleCardVisual", "const QuoteCardVisual");

    expect(source).toMatch(/style === ["']stillness_beat["']/);
    expect(source).toMatch(/sectionLabel/);
    expect(source).toMatch(/titleLine1|titleLine2|subtitle|tagline/);
    expect(source).toMatch(/ghostElements/);
    expect(source).toMatch(/divider|rule/i);
    expect(ghostBlock).toMatch(/codebase_tree/);
    expect(ghostBlock).toMatch(/mold_shell|mold_walls|mold_nozzle|mold_material/);
    expect(ghostBlock).toMatch(/quadratic_curve/);
    expect(ghostBlock).toMatch(/crossing_point/);
    expect(titleBlock).toMatch(/resolvedTitleLines\[0\]/);
    expect(titleBlock).toMatch(/resolvedTitleLines\[1\]/);
  });

  it("keeps code-underlay thesis cards on one title line and suppresses the cold-open eyebrow", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/const hideEyebrow/);
    expect(source).toMatch(/sectionNumber/);
    expect(source).toMatch(/cold open/i);
    expect(source).toMatch(/const prefersSingleLineTitle/);
    expect(source).toMatch(/hasCodeUnderlay/);
    expect(source).toMatch(/fontStyle:\s*subtitleFontStyle/);
  });

  it("renders multi-module code-transformation layouts from structured contracts instead of the generic placeholder panel", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/chartId === ["']source_of_truth_shift["']/);
    expect(source).toMatch(/transformedModules/);
    expect(source).toMatch(/pendingModules/);
    expect(source).toMatch(/source of truth/);
    expect(source).toMatch(/artifact/);
    expect(source).toMatch(/payment_processor\.py/);
    expect(source).toMatch(/prompt\.md/);
    expect(source).toMatch(/workflowStages/);
  });

  it("renders transitions and contract-first diagrams without the old placeholder badge", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).not.toContain("Generated from visual contract");
    expect(source).toMatch(/diagramId/);
    expect(source).toMatch(/promptNozzle|prompt_ratio|ratchet|five_generations|embedded_code_document|prompt_replaces_review|verilog_synthesis_triple/i);
    expect(source).toMatch(/echoes/);
  });

  it("supports richer split and code contract layouts using panel metadata instead of only a caption block", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/headerColor/);
    expect(source).toMatch(/tokenCount|scope|multiplier/);
    expect(source).toMatch(/codeComments|warningComments|lineCount|terminalCommands|workflow/);
  });

  it("supports precision-tradeoff chart annotations and constrains mold-flow panels inside the mold walls", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/chartId === "precision_tradeoff_curve"/);
    expect(source).toMatch(/parser_v1\.prompt/);
    expect(source).toMatch(/parser_v2\.prompt/);
    expect(source).toMatch(/pdd test parser/);
    expect(source).toMatch(/tests passing/);
    expect(source).toMatch(/50\+/);
    expect(source).toMatch(/clipPath/);
  });

  it("supports contract-authored quote cards instead of collapsing them into a generic quote fallback", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const quoteBlock = extractBlock(source, "const QuoteCardVisual", "const TransitionVisual");

    expect(quoteBlock).toMatch(/quoteLine1/);
    expect(quoteBlock).toMatch(/quoteLine2/);
    expect(quoteBlock).toMatch(/quoteLine2Color/);
    expect(quoteBlock).toMatch(/secondaryText/);
    expect(quoteBlock).toMatch(/Georgia/);
    expect(quoteBlock).toMatch(/width:\s*2/);
    expect(quoteBlock).toMatch(/usesMinimalQuoteLayout/);
    expect(quoteBlock).toMatch(/textAlign:\s*["']center["']/);
  });

  it("supports contract-first pie and compound-debt charts from structured data instead of relying on stale bespoke components", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const chartBlock = extractBlock(source, "const ChartVisual", "const SplitVisual");

    expect(chartBlock).toMatch(/maintenance_cost_pie/);
    expect(chartBlock).toMatch(/callouts/);
    expect(chartBlock).toMatch(/compound_debt_curve/);
    expect(chartBlock).toMatch(/dashed|strokeDasharray/);
    expect(chartBlock).toMatch(/stats/);
  });

  it("supports contract-first callback charts with the current label set instead of stale exact-component copy", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    expect(source).toMatch(/code_cost_triple_line/);
    expect(source).toMatch(/Immediate patch/);
    expect(source).toMatch(/Total cost of patching/);
    expect(source).toMatch(/Generate new/);
    expect(source).toMatch(/We are here\./);
    expect(source).toMatch(/When economics change, rational behavior changes\./);
  });

  it("renders transition cards without the old debug title and center divider artifact", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const transitionBlock = extractBlock(source, "const TransitionVisual", "const ChartVisual");

    expect(transitionBlock).not.toMatch(/resolveTitle\(data\)/);
    expect(transitionBlock).not.toMatch(/width:\s*640/);
  });

  it("supports authored split-context interiors and code regeneration details from structured contracts", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/context_window_cluttered/);
    expect(source).toMatch(/context_window_clean/);
    expect(source).toMatch(/buildContextWindowTokenBlocks/);
    expect(source).toMatch(/renderInsetTokenBadge/);
    expect(source).toMatch(/dense_code/);
    expect(source).toMatch(/prompt_blocks/);
    expect(source).toMatch(/quoteLine2Color/);
    expect(source).toMatch(/generatedLines/);
    expect(source).toMatch(/deletedLines/);
    expect(source).toMatch(/asRecord\(data\.terminal\)/);
    expect(source).toMatch(/Every token is author-curated\./);
    expect(source).toMatch(/No retrieval guessing\. No wasted space\./);
    expect(source).toMatch(/The entire context window is devoted to your problem\./);
  });

  it("keeps context-window panels centered and uses the authored clean-panel labels", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/width:\s*420/);
    expect(source).toMatch(/left:\s*["']50%["']/);
    expect(source).toMatch(/transform:\s*["']translateX\(-50%\)["']/);
    expect(source).toMatch(/normalizedLabel === "prompt"/);
    expect(source).toMatch(/normalizedLabel === "tests"/);
    expect(source).toMatch(/Grounding example/);
  });

  it("supports media-backed split reveals and element-driven precision panels from structured contracts", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/veo_clip_with_aura/);
    expect(source).toMatch(/veo_clip_then_zoom_out/);
    expect(source).toMatch(/coordinate_grid/);
    expect(source).toMatch(/printer_nozzle/);
    expect(source).toMatch(/mold_walls/);
    expect(source).toMatch(/liquid_flow/);
    expect(source).toMatch(/wall_glow_on_impact/);
  });

  it("does not leak internal split fallback labels or semantic content ids into rendered panel text", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).not.toMatch(/\?\?\s*["']Panel["']/);
    expect(source).not.toMatch(/caption\s*\?\?\s*content/);
    expect(source).not.toMatch(/caption\s*\?\?\s*thematicRole/);
  });

  it("supports contract-driven chart variants beyond the original line-series happy path", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/degradationRange|causalChain|crossings|debtResetNote/);
    expect(source).toMatch(/threshold|keyDates|debtShading/);
    expect(source).toMatch(/computeSeriesBounds/);
    expect(source).toMatch(/trapArrow|annotations/);
  });

  it("supports the remaining animated-diagram families that were still falling back to placeholders", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/diagramId === "context_compression"/);
    expect(source).toMatch(/diagramId === "bug_fork"/);
    expect(source).toMatch(/diagramId === "mold_defect_fix"/);
    expect(source).toMatch(/diagramId === "bug_add_wall"/);
    expect(source).toMatch(/diagramId === "grounding_feedback_loop"/);
    expect(source).toMatch(/diagramId === "ratchet_timelapse"/);
  });

  it("renders permanent-wall bug diagrams with the authored label, test checks, and permanence caption", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/That wall is permanent\. That bug can never occur again\./);
    expect(source).toMatch(/handles_null_userid/);
    expect(source).toMatch(/All tests passing/);
    expect(source).toMatch(/✓/);
  });

  it("supports the remaining high-fidelity morph and mold families from the authored contracts", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");

    expect(source).toMatch(/diagramId === "synopsys_pdd_equivalence"/);
    expect(source).toMatch(/diagramId === "test_walls_illuminate"/);
    expect(source).toMatch(/chartId === "dissolve_regenerate_loop"/);
    expect(source).toMatch(/diagramId === "research_annotations"/);
    expect(source).toMatch(/diagramId === "three_components_table"/);
    expect(source).toMatch(/Same architecture/);
    expect(source).toMatch(/Each test is a constraint/);
    expect(source).toMatch(/The walls aren't optional/);
    expect(source).toMatch(/The mold is what matters\./);
    expect(source).toMatch(/pdd generate/);
  });

  it("positions annotation overlays with chart-linked callout lines instead of stacking every card into a generic grid", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const annotationBlock = extractBlock(source, "const AnnotationVisual", "const TextMorphVisual");

    expect(annotationBlock).toMatch(/chartId === "code_cost_triple_line"/);
    expect(annotationBlock).toMatch(/targetPositions|annotationPositions/);
    expect(annotationBlock).toMatch(/callout/);
    expect(annotationBlock).toMatch(/debt_gap|debt_shading/);
  });

  it("supports dramatic long-quote cadence and attribution punctuation for minimal quote cards", () => {
    const source = fs.readFileSync(generatedContractVisualPath, "utf8");
    const quoteBlock = extractBlock(source, "const QuoteCardVisual", "const TransitionVisual");

    expect(quoteBlock).toMatch(/splitDramaticQuoteLines/);
    expect(quoteBlock).toMatch(/— \${attribution}|—\\s*\\$\\{attribution\\}/);
    expect(quoteBlock).toMatch(/fontWeight:\s*index === primaryLines\.length - 1 \? 700 : 400/);
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
