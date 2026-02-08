import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
  spring,
  useVideoConfig,
} from "remotion";
import {
  COLORS,
  VERILOG_BEATS,
  THREE_NETLISTS_BEATS,
  VERIFICATION_BEATS,
  TIMELINE_BEATS,
  VERILOG_SOURCE,
  VERILOG_KEYWORDS,
  NETLIST_LAYOUTS,
  STAIRCASE_STEPS,
  ChipDesignHistoryPropsType,
} from "./constants";

// ── Utility: Syntax-highlighted Verilog ──────────────────────────────

const highlightVerilog = (source: string): React.ReactNode[] => {
  const lines = source.split("\n");
  return lines.map((line, lineIdx) => {
    const tokens: React.ReactNode[] = [];
    let remaining = line;
    let tokenIdx = 0;

    while (remaining.length > 0) {
      // Check for keywords
      let matched = false;
      for (const keyword of VERILOG_KEYWORDS) {
        if (
          remaining.startsWith(keyword) &&
          (remaining.length === keyword.length ||
            /\W/.test(remaining[keyword.length]))
        ) {
          tokens.push(
            <span key={`${lineIdx}-${tokenIdx}`} style={{ color: COLORS.CODE_KEYWORD }}>
              {keyword}
            </span>
          );
          remaining = remaining.slice(keyword.length);
          tokenIdx++;
          matched = true;
          break;
        }
      }
      if (matched) continue;

      // Check for numbers
      const numMatch = remaining.match(/^(\d+'b[01]+|\d+)/);
      if (numMatch) {
        tokens.push(
          <span key={`${lineIdx}-${tokenIdx}`} style={{ color: COLORS.CODE_NUMBER }}>
            {numMatch[0]}
          </span>
        );
        remaining = remaining.slice(numMatch[0].length);
        tokenIdx++;
        continue;
      }

      // Check for comments
      if (remaining.startsWith("//")) {
        tokens.push(
          <span key={`${lineIdx}-${tokenIdx}`} style={{ color: COLORS.CODE_COMMENT }}>
            {remaining}
          </span>
        );
        remaining = "";
        tokenIdx++;
        continue;
      }

      // Default: consume one character as identifier
      tokens.push(
        <span key={`${lineIdx}-${tokenIdx}`} style={{ color: COLORS.CODE_IDENTIFIER }}>
          {remaining[0]}
        </span>
      );
      remaining = remaining.slice(1);
      tokenIdx++;
    }

    return (
      <div key={lineIdx} style={{ minHeight: "1.6em" }}>
        {tokens.length > 0 ? tokens : "\u00A0"}
      </div>
    );
  });
};

// ── Sub-component: VerilogCodeBlock ──────────────────────────────────

const VerilogCodeBlock: React.FC<{
  revealProgress: number;
  compact?: boolean;
  glowing?: boolean;
  x?: number;
  y?: number;
  scale?: number;
}> = ({
  revealProgress,
  compact = false,
  glowing = false,
  x = 460,
  y = 80,
  scale = 1,
}) => {
  const totalChars = VERILOG_SOURCE.length;
  const revealedChars = Math.floor(revealProgress * totalChars);
  const visibleSource = VERILOG_SOURCE.slice(0, revealedChars);

  const fontSize = compact ? 14 : 18;
  const padding = compact ? "16px 24px" : "24px 32px";
  const width = compact ? 360 : 500;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width,
        backgroundColor: COLORS.CODE_BG,
        borderRadius: 12,
        padding,
        fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
        fontSize,
        lineHeight: 1.6,
        transform: `scale(${scale})`,
        transformOrigin: "top left",
        boxShadow: glowing
          ? `0 0 30px ${COLORS.BLUE_GLOW_RGBA}, 0 0 60px rgba(74, 144, 217, 0.2)`
          : "0 4px 20px rgba(0, 0, 0, 0.3)",
        border: glowing
          ? `1px solid ${COLORS.BLUE_GLOW}`
          : "1px solid rgba(255, 255, 255, 0.05)",
      }}
    >
      {highlightVerilog(visibleSource)}
      {revealProgress < 1 && (
        <span
          style={{
            display: "inline-block",
            width: 2,
            height: fontSize + 2,
            backgroundColor: COLORS.CODE_KEYWORD,
            marginLeft: 2,
            animation: "blink 1s infinite",
          }}
        />
      )}
    </div>
  );
};

// ── Sub-component: SynthesisToolBox ──────────────────────────────────

const SynthesisToolBox: React.FC<{
  opacity: number;
  processing: boolean;
  frame: number;
  x?: number;
  y?: number;
}> = ({ opacity, processing, frame, x = 620, y = 520 }) => {
  const gearAngle = processing ? (frame * 3) % 360 : 0;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        width: 260,
        height: 70,
        border: `2px solid ${COLORS.SYNTH_BORDER}`,
        borderRadius: 10,
        backgroundColor: COLORS.SYNTH_FILL,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        gap: 12,
        opacity,
      }}
    >
      {/* Gear icon */}
      <svg width={28} height={28} viewBox="0 0 28 28">
        <g
          transform={`rotate(${gearAngle} 14 14)`}
          style={{ transformOrigin: "14px 14px" }}
        >
          <circle
            cx={14}
            cy={14}
            r={6}
            fill="none"
            stroke={COLORS.SYNTH_BORDER}
            strokeWidth={2}
          />
          {[0, 45, 90, 135, 180, 225, 270, 315].map((angle) => (
            <line
              key={angle}
              x1={14 + 6 * Math.cos((angle * Math.PI) / 180)}
              y1={14 + 6 * Math.sin((angle * Math.PI) / 180)}
              x2={14 + 10 * Math.cos((angle * Math.PI) / 180)}
              y2={14 + 10 * Math.sin((angle * Math.PI) / 180)}
              stroke={COLORS.SYNTH_BORDER}
              strokeWidth={2.5}
              strokeLinecap="round"
            />
          ))}
        </g>
      </svg>
      <div
        style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 16,
          color: COLORS.SYNTH_LABEL,
          fontWeight: 600,
          letterSpacing: 1,
        }}
      >
        SYNTHESIS
      </div>
    </div>
  );
};

// ── Sub-component: FlowArrow ─────────────────────────────────────────

const FlowArrow: React.FC<{
  x: number;
  y1: number;
  y2: number;
  opacity: number;
  color?: string;
}> = ({ x, y1, y2, opacity, color = COLORS.CODE_KEYWORD }) => {
  return (
    <svg
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
      width={1920}
      height={1080}
    >
      <line
        x1={x}
        y1={y1}
        x2={x}
        y2={y2 - 8}
        stroke={color}
        strokeWidth={2}
        opacity={opacity}
      />
      <polygon
        points={`${x},${y2} ${x - 6},${y2 - 10} ${x + 6},${y2 - 10}`}
        fill={color}
        opacity={opacity}
      />
    </svg>
  );
};

// ── Sub-component: GateSymbol ────────────────────────────────────────

const GateSymbol: React.FC<{
  type: string;
  x: number;
  y: number;
  color: string;
}> = ({ type, x, y, color }) => {
  const w = 40;
  const h = 28;

  const label =
    type === "AND"
      ? "&"
      : type === "OR"
        ? "\u22651"
        : type === "NOT"
          ? "1"
          : type === "NAND"
            ? "&"
            : type === "NOR"
              ? "\u22651"
              : "?";

  const hasNegation = type === "NOT" || type === "NAND" || type === "NOR";

  return (
    <g>
      <rect
        x={x}
        y={y}
        width={w}
        height={h}
        rx={4}
        fill="none"
        stroke={color}
        strokeWidth={1.5}
      />
      <text
        x={x + w / 2}
        y={y + h / 2 + 5}
        textAnchor="middle"
        fill={color}
        fontSize={12}
        fontFamily="'JetBrains Mono', monospace"
      >
        {label}
      </text>
      {hasNegation && (
        <circle
          cx={x + w + 5}
          cy={y + h / 2}
          r={4}
          fill="none"
          stroke={color}
          strokeWidth={1.5}
        />
      )}
    </g>
  );
};

// ── Sub-component: GateNetlist ───────────────────────────────────────

const GateNetlist: React.FC<{
  variant: "A" | "B" | "C";
  drawProgress: number;
  x: number;
  y: number;
  runLabel: string;
}> = ({ variant, drawProgress, x, y, runLabel }) => {
  const gates = NETLIST_LAYOUTS[variant];
  const visibleGates = Math.floor(drawProgress * gates.length);
  const netWidth = 220;
  const netHeight = 140;

  return (
    <g>
      <rect
        x={x}
        y={y}
        width={netWidth}
        height={netHeight}
        rx={8}
        fill={COLORS.NETLIST_BG}
        stroke={COLORS.NETLIST_BORDER}
        strokeWidth={1}
      />
      {gates.slice(0, visibleGates).map((gate, i) => (
        <GateSymbol
          key={i}
          type={gate.type}
          x={x + gate.x}
          y={y + gate.y}
          color={COLORS.NETLIST_TEAL}
        />
      ))}
      {/* Wire connections between visible gates */}
      {visibleGates >= 2 && (
        <g>
          {gates.slice(0, visibleGates - 1).map((gate, i) => {
            const nextGate = gates[i + 1];
            if (!nextGate) return null;
            return (
              <line
                key={`wire-${i}`}
                x1={x + gate.x + 40}
                y1={y + gate.y + 14}
                x2={x + nextGate.x}
                y2={y + nextGate.y + 14}
                stroke={COLORS.NETLIST_TEAL}
                strokeWidth={1}
                opacity={0.6}
              />
            );
          })}
        </g>
      )}
      {/* Run label */}
      <text
        x={x + netWidth / 2}
        y={y + netHeight + 22}
        textAnchor="middle"
        fill={COLORS.SYNTH_LABEL}
        fontSize={13}
        fontFamily="'JetBrains Mono', monospace"
      >
        {runLabel}
      </text>
    </g>
  );
};

// ── Sub-component: VerificationCheckmark ─────────────────────────────

const VerificationCheckmark: React.FC<{
  x: number;
  y: number;
  frame: number;
  delay: number;
  fps: number;
}> = ({ x, y, frame, delay, fps }) => {
  const adjustedFrame = frame - delay;
  if (adjustedFrame < 0) return null;

  const scaleValue = spring({
    frame: adjustedFrame,
    fps,
    config: {
      damping: 12,
      stiffness: 200,
      mass: 0.5,
    },
  });

  const opacity = interpolate(adjustedFrame, [0, 10], [0, 1], {
    extrapolateRight: "clamp",
  });

  return (
    <g
      transform={`translate(${x}, ${y}) scale(${scaleValue})`}
      opacity={opacity}
    >
      <circle
        cx={0}
        cy={0}
        r={24}
        fill="none"
        stroke={COLORS.CHECK_GREEN}
        strokeWidth={2.5}
      />
      <path
        d="M-10 0 L-3 7 L10 -6"
        fill="none"
        stroke={COLORS.CHECK_GREEN}
        strokeWidth={3.5}
        strokeLinecap="round"
        strokeLinejoin="round"
      />
    </g>
  );
};

// ── Sub-component: AbstractionStaircase ──────────────────────────────

const AbstractionStaircase: React.FC<{
  visibleSteps: number;
  arrowProgress: number[];
  pulseActive: boolean;
  frame: number;
  fps: number;
}> = ({ visibleSteps, arrowProgress, pulseActive, frame, fps }) => {
  const stepHeight = 70;
  const riserHeight = 40;
  const baseX = 140;
  const baseY = 780;

  // Pulse oscillation
  const pulseOpacity = pulseActive
    ? 0.7 + 0.3 * Math.sin((frame / fps) * 1.5 * Math.PI * 2)
    : 0.9;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Glow filter */}
      <defs>
        <filter id="staircase-glow">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {STAIRCASE_STEPS.slice(0, visibleSteps).map((step, i) => {
        const x = baseX + i * (step.width + 20);
        const y = baseY - i * (stepHeight + riserHeight);
        const isLast = i === STAIRCASE_STEPS.length - 1;
        const isPulsing = isLast && pulseActive;

        return (
          <g key={i}>
            {/* Vertical riser connecting to previous step */}
            {i > 0 && (
              <rect
                x={x - 20}
                y={y + stepHeight}
                width={20}
                height={riserHeight}
                fill={step.color}
                opacity={0.4}
              />
            )}

            {/* Step platform */}
            <rect
              x={x}
              y={y}
              width={step.width}
              height={stepHeight}
              fill={step.color}
              rx={6}
              opacity={isPulsing ? pulseOpacity : 0.85}
            />

            {/* Glow for pulsing step */}
            {isPulsing && (
              <rect
                x={x - 4}
                y={y - 4}
                width={step.width + 8}
                height={stepHeight + 8}
                fill="none"
                stroke={step.color}
                strokeWidth={3}
                opacity={pulseOpacity * 0.5}
                filter="url(#staircase-glow)"
                rx={8}
              />
            )}

            {/* Step label */}
            <text
              x={x + step.width / 2}
              y={y + stepHeight / 2 - (step.sublabel ? 4 : 0)}
              textAnchor="middle"
              fill={COLORS.WHITE}
              fontSize={15}
              fontFamily="'JetBrains Mono', monospace"
              fontWeight="bold"
            >
              {step.label}
            </text>

            {/* Sublabel (for "-> Code") */}
            {step.sublabel && (
              <text
                x={x + step.width / 2}
                y={y + stepHeight / 2 + 14}
                textAnchor="middle"
                fill={COLORS.WHITE}
                fontSize={14}
                fontFamily="'JetBrains Mono', monospace"
                fontWeight="bold"
              >
                {step.sublabel}
              </text>
            )}

            {/* Decade label below step */}
            <text
              x={x + step.width / 2}
              y={y + stepHeight + 18}
              textAnchor="middle"
              fill={COLORS.DECADE_LABEL}
              fontSize={12}
              fontFamily="'JetBrains Mono', monospace"
            >
              {step.decade}
            </text>

            {/* "Couldn't scale" arrow between steps */}
            {i > 0 && arrowProgress[i - 1] > 0 && (
              <g>
                {/* Arrow shaft */}
                <line
                  x1={x - 10}
                  y1={y + stepHeight + riserHeight - 5}
                  x2={x - 10}
                  y2={
                    y +
                    stepHeight +
                    riserHeight -
                    5 -
                    arrowProgress[i - 1] * (riserHeight - 10)
                  }
                  stroke={COLORS.ARROW_AMBER}
                  strokeWidth={2.5}
                  strokeLinecap="round"
                />
                {/* Arrow head */}
                {arrowProgress[i - 1] > 0.7 && (
                  <polygon
                    points={`${x - 10},${y + stepHeight + 5} ${x - 15},${y + stepHeight + 14} ${x - 5},${y + stepHeight + 14}`}
                    fill={COLORS.ARROW_AMBER}
                  />
                )}
                {/* Label */}
                {arrowProgress[i - 1] > 0.5 && (
                  <text
                    x={x + 8}
                    y={y + stepHeight + riserHeight / 2 + 4}
                    fill={COLORS.ARROW_AMBER}
                    fontSize={10}
                    fontFamily="'JetBrains Mono', monospace"
                    opacity={interpolate(
                      arrowProgress[i - 1],
                      [0.5, 1],
                      [0, 1],
                      {
                        extrapolateLeft: "clamp",
                        extrapolateRight: "clamp",
                      }
                    )}
                  >
                    Couldn&apos;t scale
                  </text>
                )}
              </g>
            )}
          </g>
        );
      })}
    </svg>
  );
};

// ── Phase: VerilogSynthesis ──────────────────────────────────────────

const VerilogSynthesisPhase: React.FC<{ frame: number; fps: number }> = ({
  frame,
  fps,
}) => {
  // Dissolving schematic (amber particles fading)
  const dissolveProgress = interpolate(
    frame,
    [VERILOG_BEATS.DISSOLVE_START, VERILOG_BEATS.DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const dissolveOpacity = interpolate(
    frame,
    [VERILOG_BEATS.DISSOLVE_START, VERILOG_BEATS.DISSOLVE_END],
    [0.8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Verilog code typewriter
  const codeProgress = interpolate(
    frame,
    [VERILOG_BEATS.CODE_TYPE_START, VERILOG_BEATS.CODE_TYPE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Synthesis tool fade-in
  const synthOpacity = interpolate(
    frame,
    [VERILOG_BEATS.SYNTH_START, VERILOG_BEATS.SYNTH_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Flow arrow from code to synth
  const arrowOpacity = interpolate(
    frame,
    [VERILOG_BEATS.SYNTH_START + 20, VERILOG_BEATS.SYNTH_START + 50],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Netlist draw progress
  const netlistProgress = interpolate(
    frame,
    [VERILOG_BEATS.NETLIST_START, VERILOG_BEATS.NETLIST_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Netlist opacity
  const netlistOpacity = interpolate(
    frame,
    [VERILOG_BEATS.NETLIST_START, VERILOG_BEATS.NETLIST_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Arrow from synth to netlist
  const arrow2Opacity = interpolate(
    frame,
    [VERILOG_BEATS.NETLIST_START, VERILOG_BEATS.NETLIST_START + 30],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const isProcessing = frame >= VERILOG_BEATS.SYNTH_START;

  return (
    <>
      {/* Dissolving schematic particles */}
      {dissolveOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 460,
            top: 80,
            width: 500,
            height: 400,
            opacity: dissolveOpacity,
          }}
        >
          {Array.from({ length: 30 }).map((_, i) => {
            const px = 50 + ((i * 137) % 400);
            const py = 30 + ((i * 97) % 340);
            const spread = dissolveProgress * 60;
            const dx = (Math.sin(i * 2.1) * spread);
            const dy = -(Math.cos(i * 1.7) * spread + dissolveProgress * 40);
            return (
              <div
                key={i}
                style={{
                  position: "absolute",
                  left: px + dx,
                  top: py + dy,
                  width: 4 + (i % 3) * 2,
                  height: 4 + (i % 3) * 2,
                  borderRadius: "50%",
                  backgroundColor: COLORS.ARROW_AMBER,
                  opacity: 1 - dissolveProgress,
                }}
              />
            );
          })}
        </div>
      )}

      {/* Verilog code block */}
      {frame >= VERILOG_BEATS.CODE_TYPE_START && (
        <VerilogCodeBlock
          revealProgress={codeProgress}
          glowing={frame >= VERILOG_BEATS.HOLD_START}
          x={460}
          y={80}
        />
      )}

      {/* Flow arrow: code to synth */}
      {arrowOpacity > 0 && (
        <FlowArrow x={710} y1={480} y2={520} opacity={arrowOpacity} />
      )}

      {/* Synthesis tool */}
      {synthOpacity > 0 && (
        <SynthesisToolBox
          opacity={synthOpacity}
          processing={isProcessing}
          frame={frame}
          x={620}
          y={520}
        />
      )}

      {/* Flow arrow: synth to netlist */}
      {arrow2Opacity > 0 && (
        <FlowArrow x={710} y1={590} y2={640} opacity={arrow2Opacity} />
      )}

      {/* Single netlist output */}
      {netlistOpacity > 0 && (
        <svg
          width={1920}
          height={1080}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            opacity: netlistOpacity,
          }}
        >
          <GateNetlist
            variant="A"
            drawProgress={netlistProgress}
            x={640}
            y={650}
            runLabel="Generated Netlist"
          />
        </svg>
      )}

      {/* "Automatic" label */}
      {frame >= VERILOG_BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            left: 640,
            top: 830,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 14,
            color: COLORS.CODE_KEYWORD,
            letterSpacing: 1,
            textTransform: "uppercase",
            opacity: interpolate(
              frame,
              [VERILOG_BEATS.HOLD_START, VERILOG_BEATS.HOLD_START + 30],
              [0, 0.8],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          Auto-generated gates
        </div>
      )}
    </>
  );
};

// ── Phase: ThreeNetlists ─────────────────────────────────────────────

const ThreeNetlistsPhase: React.FC<{ frame: number; fps: number }> = ({
  frame,
  fps,
}) => {
  // Verilog code (always visible, compact, glowing)
  const codeOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Three netlist draw progresses
  const netlist1Progress = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN1_START, THREE_NETLISTS_BEATS.RUN1_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const netlist2Progress = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN2_START, THREE_NETLISTS_BEATS.RUN2_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const netlist3Progress = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN3_START, THREE_NETLISTS_BEATS.RUN3_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Netlist opacities
  const net1Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN1_START, THREE_NETLISTS_BEATS.RUN1_START + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const net2Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN2_START, THREE_NETLISTS_BEATS.RUN2_START + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const net3Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN3_START, THREE_NETLISTS_BEATS.RUN3_START + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Arrow opacities
  const arrow1Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN1_START, THREE_NETLISTS_BEATS.RUN1_START + 20],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const arrow2Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN2_START, THREE_NETLISTS_BEATS.RUN2_START + 20],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const arrow3Opacity = interpolate(
    frame,
    [THREE_NETLISTS_BEATS.RUN3_START, THREE_NETLISTS_BEATS.RUN3_START + 20],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Netlist positions
  const netY = 580;
  const netX1 = 200;
  const netX2 = 850;
  const netX3 = 1500;

  return (
    <>
      {/* Verilog code block (compact, top center, glowing) */}
      {codeOpacity > 0 && (
        <div style={{ opacity: codeOpacity }}>
          <VerilogCodeBlock
            revealProgress={1}
            compact
            glowing
            x={580}
            y={40}
            scale={0.85}
          />
        </div>
      )}

      {/* "Same input" label */}
      <div
        style={{
          position: "absolute",
          left: 0,
          right: 0,
          top: 350,
          textAlign: "center",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 14,
          color: COLORS.SYNTH_LABEL,
          letterSpacing: 2,
          textTransform: "uppercase",
          opacity: codeOpacity * 0.6,
        }}
      >
        Same Verilog Source
      </div>

      {/* Flow arrows from code to each netlist */}
      {arrow1Opacity > 0 && (
        <FlowArrow x={netX1 + 110} y1={380} y2={netY} opacity={arrow1Opacity} />
      )}
      {arrow2Opacity > 0 && (
        <FlowArrow x={netX2 + 110} y1={380} y2={netY} opacity={arrow2Opacity} />
      )}
      {arrow3Opacity > 0 && (
        <FlowArrow x={netX3 + 110} y1={380} y2={netY} opacity={arrow3Opacity} />
      )}

      {/* Three netlists */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {net1Opacity > 0 && (
          <g opacity={net1Opacity}>
            <GateNetlist
              variant="A"
              drawProgress={netlist1Progress}
              x={netX1}
              y={netY}
              runLabel="Run 1"
            />
          </g>
        )}
        {net2Opacity > 0 && (
          <g opacity={net2Opacity}>
            <GateNetlist
              variant="B"
              drawProgress={netlist2Progress}
              x={netX2}
              y={netY}
              runLabel="Run 2"
            />
          </g>
        )}
        {net3Opacity > 0 && (
          <g opacity={net3Opacity}>
            <GateNetlist
              variant="C"
              drawProgress={netlist3Progress}
              x={netX3}
              y={netY}
              runLabel="Run 3"
            />
          </g>
        )}
      </svg>

      {/* "Different every time" label at the bottom */}
      {frame >= THREE_NETLISTS_BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: 100,
            textAlign: "center",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 20,
            color: COLORS.ARROW_AMBER,
            opacity: interpolate(
              frame,
              [
                THREE_NETLISTS_BEATS.HOLD_START,
                THREE_NETLISTS_BEATS.HOLD_START + 30,
              ],
              [0, 0.9],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          Different gates. Different wiring. Every time.
        </div>
      )}
    </>
  );
};

// ── Phase: Verification ──────────────────────────────────────────────

const VerificationPhase: React.FC<{ frame: number; fps: number }> = ({
  frame,
  fps,
}) => {
  // Code block always visible
  const codeOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Three netlists always visible
  const netY = 500;
  const netX1 = 200;
  const netX2 = 850;
  const netX3 = 1500;

  // "Functionally Equivalent" label
  const labelOpacity = interpolate(
    frame,
    [VERIFICATION_BEATS.LABEL_START, VERIFICATION_BEATS.LABEL_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <>
      {/* Verilog code block (compact, top center, glowing) */}
      {codeOpacity > 0 && (
        <div style={{ opacity: codeOpacity }}>
          <VerilogCodeBlock
            revealProgress={1}
            compact
            glowing
            x={580}
            y={30}
            scale={0.8}
          />
        </div>
      )}

      {/* "Same input" label */}
      <div
        style={{
          position: "absolute",
          left: 0,
          right: 0,
          top: 310,
          textAlign: "center",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 13,
          color: COLORS.SYNTH_LABEL,
          letterSpacing: 2,
          textTransform: "uppercase",
          opacity: codeOpacity * 0.5,
        }}
      >
        Same Verilog Source
      </div>

      {/* Flow arrows */}
      <FlowArrow x={netX1 + 110} y1={340} y2={netY} opacity={0.4} />
      <FlowArrow x={netX2 + 110} y1={340} y2={netY} opacity={0.4} />
      <FlowArrow x={netX3 + 110} y1={340} y2={netY} opacity={0.4} />

      {/* Three netlists (fully drawn) */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <GateNetlist
          variant="A"
          drawProgress={1}
          x={netX1}
          y={netY}
          runLabel="Run 1"
        />
        <GateNetlist
          variant="B"
          drawProgress={1}
          x={netX2}
          y={netY}
          runLabel="Run 2"
        />
        <GateNetlist
          variant="C"
          drawProgress={1}
          x={netX3}
          y={netY}
          runLabel="Run 3"
        />

        {/* Verification checkmarks */}
        <VerificationCheckmark
          x={netX1 + 110}
          y={netY + 70}
          frame={frame}
          delay={VERIFICATION_BEATS.CHECK1_START}
          fps={fps}
        />
        <VerificationCheckmark
          x={netX2 + 110}
          y={netY + 70}
          frame={frame}
          delay={VERIFICATION_BEATS.CHECK2_START}
          fps={fps}
        />
        <VerificationCheckmark
          x={netX3 + 110}
          y={netY + 70}
          frame={frame}
          delay={VERIFICATION_BEATS.CHECK3_START}
          fps={fps}
        />
      </svg>

      {/* "Functionally Equivalent" label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: 120,
            textAlign: "center",
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              display: "inline-block",
              padding: "12px 40px",
              borderRadius: 8,
              border: `2px solid ${COLORS.CHECK_GREEN}`,
              backgroundColor: "rgba(90, 170, 110, 0.1)",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 22,
              fontWeight: 600,
              color: COLORS.CHECK_GREEN,
              letterSpacing: 2,
            }}
          >
            Functionally Equivalent
          </div>
          <div
            style={{
              marginTop: 12,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 13,
              color: "rgba(255, 255, 255, 0.5)",
            }}
          >
            Formal equivalence checking via SAT/SMT solvers
          </div>
        </div>
      )}
    </>
  );
};

// ── Phase: AbstractionTimeline ────────────────────────────────────────

const AbstractionTimelinePhase: React.FC<{ frame: number; fps: number }> = ({
  frame,
  fps,
}) => {
  // Calculate visible steps based on frame
  let visibleSteps = 0;
  if (frame >= TIMELINE_BEATS.STEP1_START) visibleSteps = 1;
  if (frame >= TIMELINE_BEATS.STEP2_START) visibleSteps = 2;
  if (frame >= TIMELINE_BEATS.STEP3_START) visibleSteps = 3;
  if (frame >= TIMELINE_BEATS.STEP4_START) visibleSteps = 4;
  if (frame >= TIMELINE_BEATS.STEP5_START) visibleSteps = 5;

  // Arrow progress for each transition (0-1)
  const arrowProgress = [
    interpolate(
      frame,
      [TIMELINE_BEATS.STEP2_START, TIMELINE_BEATS.STEP2_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ),
    interpolate(
      frame,
      [TIMELINE_BEATS.STEP3_START, TIMELINE_BEATS.STEP3_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ),
    interpolate(
      frame,
      [TIMELINE_BEATS.STEP4_START, TIMELINE_BEATS.STEP4_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ),
    interpolate(
      frame,
      [TIMELINE_BEATS.STEP5_START, TIMELINE_BEATS.STEP5_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ),
  ];

  const pulseActive = frame >= TIMELINE_BEATS.PULSE_START;

  // Title label
  const titleOpacity = interpolate(frame, [0, 30], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <>
      {/* Title */}
      <div
        style={{
          position: "absolute",
          left: 0,
          right: 0,
          top: 50,
          textAlign: "center",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 16,
          letterSpacing: 3,
          textTransform: "uppercase",
          color: COLORS.WHITE,
          opacity: titleOpacity,
        }}
      >
        The Abstraction Staircase
      </div>

      {/* Staircase */}
      <AbstractionStaircase
        visibleSteps={visibleSteps}
        arrowProgress={arrowProgress}
        pulseActive={pulseActive}
        frame={frame}
        fps={fps}
      />

      {/* "The pattern repeats" narration-sync label */}
      {frame >= TIMELINE_BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: 80,
            textAlign: "center",
            fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
            fontSize: 24,
            color: COLORS.NARRATION_WHITE,
            opacity: interpolate(
              frame,
              [TIMELINE_BEATS.HOLD_START, TIMELINE_BEATS.HOLD_START + 40],
              [0, 0.9],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          The designer stopped specifying{" "}
          <span style={{ fontStyle: "italic" }}>how</span> and started
          specifying <span style={{ fontStyle: "italic" }}>what</span>.
        </div>
      )}
    </>
  );
};

// ── Main Component ───────────────────────────────────────────────────

/**
 * 19a-ChipDesignHistory: Covers the chip design narrative from Verilog
 * synthesis through three netlists with verification checkmarks to the
 * abstraction staircase timeline.
 *
 * Phases:
 *   - verilogSynthesis: Schematic dissolves, Verilog code types in,
 *     synthesis tool generates netlist
 *   - threeNetlists: Same code produces three different netlists
 *   - verification: Green checkmarks confirm functional equivalence
 *   - abstractionTimeline: Rising staircase of abstraction levels
 */
export const ChipDesignHistory: React.FC<ChipDesignHistoryPropsType> = ({
  phase = "verilogSynthesis",
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {phase === "verilogSynthesis" && (
        <VerilogSynthesisPhase frame={frame} fps={fps} />
      )}
      {phase === "threeNetlists" && (
        <ThreeNetlistsPhase frame={frame} fps={fps} />
      )}
      {phase === "verification" && (
        <VerificationPhase frame={frame} fps={fps} />
      )}
      {phase === "abstractionTimeline" && (
        <AbstractionTimelinePhase frame={frame} fps={fps} />
      )}
    </AbsoluteFill>
  );
};
