import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { LiquidFlow } from './LiquidFlow';
import { Annotation } from './Annotation';
import { WallFocus } from './WallFocus';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  WALLS,
  FOCUS_WALL_INDEX,
  ANNOTATION_RED,
  ANNOTATION_GREEN,
  ANNOTATION_1_POS,
  ANNOTATION_2_POS,
  PHASE_ZOOM_START,
  PHASE_ZOOM_DURATION,
  PHASE_ZOOM_END,
  PHASE_PULLBACK_DURATION,
  PHASE_ANNOTATION_1_IN,
  PHASE_ANNOTATION_2_IN,
} from './constants';

export const defaultPart3MoldParts04LiquidInjectionProps = {};

/**
 * Section 3.4: Liquid Injection — Code Constrained by Walls
 *
 * Animated liquid (representing code generation) is injected into a mold cavity,
 * flowing until it hits test-wall constraints. Includes zoom focus on the
 * "null → None" wall and research annotation overlays.
 *
 * Duration: 870 frames @ 30fps (~29s)
 */
export const Part3MoldParts04LiquidInjection: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Camera zoom for null→None wall focus (frames 180-270) ──
  // Zoom in from frame 180-210, hold, then zoom out 270-300
  const zoomIn = interpolate(
    frame,
    [PHASE_ZOOM_START, PHASE_ZOOM_START + PHASE_ZOOM_DURATION],
    [1, 1.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const zoomOut = interpolate(
    frame,
    [PHASE_ZOOM_END, PHASE_ZOOM_END + PHASE_PULLBACK_DURATION],
    [1.3, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  let scale = 1;
  if (frame >= PHASE_ZOOM_START && frame < PHASE_ZOOM_END) {
    scale = zoomIn;
  } else if (frame >= PHASE_ZOOM_END && frame < PHASE_ZOOM_END + PHASE_PULLBACK_DURATION) {
    scale = zoomOut;
  }

  // Focus point for zoom (center on the null→None wall)
  const focusWall = WALLS[FOCUS_WALL_INDEX];
  const focusX = focusWall.x;
  const focusY = focusWall.y + focusWall.height / 2;

  // Calculate translate to keep focus point centered during zoom
  const translateX = (1 - scale) * focusX;
  const translateY = (1 - scale) * focusY;

  // Connector targets for annotations (point at wall region)
  const connectorTarget1 = { x: 980, y: 360 };
  const connectorTarget2 = { x: 980, y: 420 };

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Zoomable content layer */}
      <AbsoluteFill
        style={{
          transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
          transformOrigin: '0 0',
        }}
      >
        {/* Mold cross-section with walls */}
        <MoldCrossSection />

        {/* Liquid flow animation — runs from frame 0 */}
        <LiquidFlow />

        {/* Wall focus overlay during zoom phase */}
        <Sequence from={PHASE_ZOOM_START} durationInFrames={PHASE_ZOOM_END - PHASE_ZOOM_START + PHASE_PULLBACK_DURATION}>
          <WallFocus />
        </Sequence>
      </AbsoluteFill>

      {/* Annotations — positioned outside the zoom layer so they stay stable */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Annotation 1: CodeRabbit stat */}
        <Annotation
          text="AI code: 1.7× more issues"
          source="(CodeRabbit, 2025)"
          textColor={ANNOTATION_RED}
          position={ANNOTATION_1_POS}
          fadeInFrame={PHASE_ANNOTATION_1_IN}
          connectorTarget={connectorTarget1}
        />

        {/* Annotation 2: DORA stat */}
        <Annotation
          text="AI + strong tests = amplified delivery"
          source="(DORA, 2025)"
          textColor={ANNOTATION_GREEN}
          position={ANNOTATION_2_POS}
          fadeInFrame={PHASE_ANNOTATION_2_IN}
          connectorTarget={connectorTarget2}
        />
      </Sequence>

      {/* Title label at top */}
      <div
        style={{
          position: 'absolute',
          top: 40,
          left: 0,
          width: '100%',
          display: 'flex',
          justifyContent: 'center',
          opacity: interpolate(frame, [0, 15], [0.8, 0.8], {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }),
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 22,
            fontWeight: 600,
            color: '#E2E8F0',
            letterSpacing: 2,
            textTransform: 'uppercase',
            opacity: 0.85,
          }}
        >
          Liquid Injection — Code Constrained by Walls
        </span>
      </div>

      {/* Bottom-right frame/phase indicator (subtle) */}
      <div
        style={{
          position: 'absolute',
          bottom: 30,
          right: 40,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          color: '#475569',
          opacity: 0.5,
        }}
      >
        {frame} / {TOTAL_FRAMES}
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldParts04LiquidInjection;
