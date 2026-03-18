import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import { COLORS, SHORT_PROMPT_LINES, MODULE_PROMPTS } from './constants';

/**
 * Beat 3 — Compression Ratio (frames 0-240 relative, 360-600 absolute)
 * Shows prompt vs code size comparison, then context window comparison.
 */

// Generate fake dense code lines
const generateCodeLines = (count: number): string[] => {
  const patterns = [
    '    if not isinstance(value, str):',
    '        return ValidationError("invalid")',
    '    result = self._cache.get(key)',
    '    if result is not None:',
    '        return result',
    '    try:',
    '        parsed = json.loads(raw_input)',
    '    except JSONDecodeError as e:',
    '        logger.warning(f"Parse fail: {e}")',
    '        return None',
    '    for item in batch:',
    '        validated = self.validate(item)',
    '        if validated:',
    '            output.append(validated)',
    '    connection = pool.acquire()',
    '    cursor = connection.cursor()',
    '    cursor.execute(query, params)',
    '    rows = cursor.fetchall()',
    '    return [Row(**r) for r in rows]',
    '    def __init__(self, config):',
    '        self._config = config',
    '        self._initialized = False',
    '    @property',
    '    def is_valid(self) -> bool:',
    '        return self._state == "valid"',
    '    async def process(self, data):',
    '        async with self._lock:',
    '            await self._handle(data)',
    '    class Config:',
    '        max_retries: int = 3',
    '        timeout: float = 30.0',
    '        debug: bool = False',
  ];
  const lines: string[] = [];
  for (let i = 0; i < count; i++) {
    lines.push(patterns[i % patterns.length]);
  }
  return lines;
};

const DENSE_CODE_LINES = generateCodeLines(200);

const PromptPanel: React.FC<{
  opacity: number;
  glowIntensity: number;
}> = ({ opacity, glowIntensity }) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: 100,
        top: 180,
        width: 300,
        height: 300,
        backgroundColor: COLORS.codePanel,
        border: `1px solid ${COLORS.codeBorder}`,
        borderRadius: 6,
        padding: 16,
        opacity,
        boxShadow: `0 0 ${20 * glowIntensity}px ${COLORS.nozzleBlue}33`,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.labelMuted,
          marginBottom: 8,
          borderBottom: `1px solid ${COLORS.codeBorder}`,
          paddingBottom: 6,
        }}
      >
        user_parser.prompt
      </div>
      {SHORT_PROMPT_LINES.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 11,
            color: line.startsWith('#')
              ? COLORS.nozzleBlue
              : COLORS.textLight,
            opacity: line.startsWith('#') ? 0.8 : 0.7,
            lineHeight: '16px',
            minHeight: 16,
          }}
        >
          {line || '\u00A0'}
        </div>
      ))}
    </div>
  );
};

const CodeScrollPanel: React.FC<{
  opacity: number;
  scrollOffset: number;
}> = ({ opacity, scrollOffset }) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: 450,
        top: 80,
        width: 300,
        height: 600,
        backgroundColor: COLORS.codePanel,
        border: `1px solid ${COLORS.codeBorder}`,
        borderRadius: 6,
        padding: '8px 12px',
        opacity: opacity * 0.6,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 10,
          color: COLORS.labelMuted,
          marginBottom: 8,
          borderBottom: `1px solid ${COLORS.codeBorder}`,
          paddingBottom: 6,
        }}
      >
        user_parser.py — 200+ lines
      </div>
      <div
        style={{
          transform: `translateY(${-scrollOffset}px)`,
          transition: 'none',
        }}
      >
        {DENSE_CODE_LINES.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 9,
              color: COLORS.codeText,
              opacity: 0.3,
              lineHeight: '13px',
              whiteSpace: 'nowrap',
              overflow: 'hidden',
            }}
          >
            <span style={{ color: COLORS.labelMuted, opacity: 0.3, marginRight: 8, display: 'inline-block', width: 24, textAlign: 'right' }}>
              {i + 1}
            </span>
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};

const HeightArrow: React.FC<{
  opacity: number;
}> = ({ opacity }) => {
  return (
    <svg
      width={60}
      height={400}
      style={{
        position: 'absolute',
        left: 400,
        top: 180,
        opacity,
      }}
    >
      {/* Vertical line */}
      <line
        x1={30}
        y1={20}
        x2={30}
        y2={380}
        stroke={COLORS.nozzleBlue}
        strokeWidth={2}
        opacity={0.5}
      />
      {/* Top arrow */}
      <polygon
        points="30,10 24,22 36,22"
        fill={COLORS.nozzleBlue}
        opacity={0.5}
      />
      {/* Bottom arrow */}
      <polygon
        points="30,390 24,378 36,378"
        fill={COLORS.nozzleBlue}
        opacity={0.5}
      />
      {/* Label */}
      <text
        x={30}
        y={205}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={16}
        fontWeight={700}
        fill={COLORS.nozzleBlue}
      >
        10×
      </text>
    </svg>
  );
};

const ContextWindowComparison: React.FC<{
  opacity: number;
  slideProgress: number;
  pulsePhase: number;
  captionOpacity: number;
}> = ({ opacity, slideProgress, pulsePhase, captionOpacity }) => {
  const slideX = interpolate(slideProgress, [0, 1], [40, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        left: 820,
        top: 0,
        width: 1100,
        height: 1080,
        opacity,
        transform: `translateX(${slideX}px)`,
      }}
    >
      {/* LEFT window — dense code */}
      <div style={{ position: 'absolute', left: 80, top: 160 }}>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: COLORS.labelMuted,
            marginBottom: 8,
          }}
        >
          15,000 tokens of code
        </div>
        <div
          style={{
            width: 400,
            height: 600,
            backgroundColor: COLORS.codePanel,
            borderRadius: 6,
            border: `1px solid ${COLORS.codeBorder}`,
            padding: 12,
            overflow: 'hidden',
          }}
        >
          {/* Dense overwhelming code representation */}
          {Array.from({ length: 45 }).map((_, i) => (
            <div
              key={i}
              style={{
                height: 11,
                marginBottom: 2,
                display: 'flex',
                gap: 3,
              }}
            >
              {/* Variable-width "code" blocks */}
              {Array.from({ length: 4 + (i % 3) }).map((_, j) => (
                <div
                  key={j}
                  style={{
                    height: '100%',
                    width: 20 + ((i * 7 + j * 13) % 60),
                    backgroundColor: COLORS.codeText,
                    opacity: 0.15,
                    borderRadius: 2,
                  }}
                />
              ))}
            </div>
          ))}
        </div>
      </div>

      {/* RIGHT window — clean prompts */}
      <div style={{ position: 'absolute', left: 530, top: 160 }}>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: COLORS.nozzleBlue,
            marginBottom: 8,
          }}
        >
          Prompts for 10 modules
        </div>
        <div
          style={{
            width: 400,
            height: 600,
            backgroundColor: COLORS.codePanel,
            borderRadius: 6,
            border: `1px solid ${COLORS.codeBorder}`,
            padding: 16,
            overflow: 'hidden',
            boxShadow:
              pulsePhase > 0
                ? `0 0 ${12 + 6 * Math.sin(pulsePhase)}px ${COLORS.nozzleBlue}22`
                : 'none',
          }}
        >
          {/* Clean prompt blocks */}
          {MODULE_PROMPTS.map((name, i) => (
            <div
              key={i}
              style={{
                backgroundColor: `${COLORS.nozzleBlue}26`,
                borderRadius: 4,
                padding: '8px 12px',
                marginBottom: 8,
                border: `1px solid ${COLORS.nozzleBlue}33`,
              }}
            >
              <div
                style={{
                  fontFamily: 'JetBrains Mono, monospace',
                  fontSize: 9,
                  color: COLORS.nozzleBlue,
                  opacity: 0.7,
                  marginBottom: 3,
                }}
              >
                {name}
              </div>
              {/* Fake prompt lines */}
              <div style={{ display: 'flex', gap: 4, flexWrap: 'wrap' }}>
                {Array.from({ length: 2 + (i % 2) }).map((_, j) => (
                  <div
                    key={j}
                    style={{
                      height: 6,
                      width: 40 + ((i * 11 + j * 17) % 80),
                      backgroundColor: COLORS.nozzleBlue,
                      opacity: 0.15,
                      borderRadius: 2,
                    }}
                  />
                ))}
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Caption below both */}
      <div
        style={{
          position: 'absolute',
          left: 80,
          top: 800,
          width: 850,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: COLORS.textLight,
          opacity: captionOpacity * 0.7,
          lineHeight: '22px',
        }}
      >
        Same context window. <span style={{ fontWeight: 700, color: COLORS.nozzleBlue }}>10×</span> more system knowledge.
      </div>
    </div>
  );
};

export const Beat3CompressionRatio: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panels appear (frame 0-30 relative)
  const panelFadeIn = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Code scroll (continuous from frame 30)
  const scrollOffset = frame > 30 ? (frame - 30) * 0.5 : 0;

  // Height arrow appears
  const arrowOpacity = interpolate(frame, [30, 50], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Ratio badge spring animation at frame 30
  const badgeScale =
    frame >= 30
      ? spring({
          frame: frame - 30,
          fps,
          config: { stiffness: 150, damping: 12 },
          from: 0.8,
          to: 1,
        })
      : 0;
  const badgeOpacity = interpolate(frame, [30, 45], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Glow pulse on prompt panel
  const glowIntensity =
    frame > 20
      ? 0.5 + 0.5 * Math.sin(((frame - 20) / 40) * Math.PI * 2)
      : 0;

  // Context window slides in at frame 90
  const contextOpacity = interpolate(frame, [90, 115], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const contextSlide = interpolate(frame, [90, 115], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(3)),
  });

  // Caption at frame 150
  const captionOpacity = interpolate(frame, [150, 170], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Blue pulse on right window (frames 180+)
  const pulsePhase =
    frame > 180
      ? ((frame - 180) / 40) * Math.PI * 2
      : 0;

  return (
    <AbsoluteFill>
      {/* Prompt panel */}
      <PromptPanel opacity={panelFadeIn} glowIntensity={glowIntensity} />

      {/* Code scroll panel */}
      <CodeScrollPanel opacity={panelFadeIn} scrollOffset={scrollOffset} />

      {/* Height comparison arrow */}
      <HeightArrow opacity={arrowOpacity} />

      {/* Ratio badge */}
      <div
        style={{
          position: 'absolute',
          left: 180,
          top: 520,
          transform: `scale(${badgeScale})`,
          opacity: badgeOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 24,
            fontWeight: 700,
            color: COLORS.nozzleBlue,
            backgroundColor: `${COLORS.nozzleBlue}1A`,
            padding: '8px 24px',
            borderRadius: 24,
            border: `1px solid ${COLORS.nozzleBlue}33`,
            whiteSpace: 'nowrap',
          }}
        >
          1:5 to 1:10
        </div>
      </div>

      {/* Context window comparison */}
      <ContextWindowComparison
        opacity={contextOpacity}
        slideProgress={contextSlide}
        pulsePhase={frame > 180 ? pulsePhase : 0}
        captionOpacity={captionOpacity}
      />
    </AbsoluteFill>
  );
};
