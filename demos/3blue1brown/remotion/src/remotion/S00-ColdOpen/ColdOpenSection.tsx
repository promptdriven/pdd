import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";
import { HoldAccumulatedWeight } from "./HoldAccumulatedWeight";
import { CodeBlinks } from "./CodeBlinks";
import { CodeRegeneratesVisual } from "./CodeRegeneratesVisual";


export const ColdOpenSection: React.FC<ColdOpenSectionPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#1a1a2e" }}>
      {/* Narration audio */}
      <Audio src={staticFile("cold_open_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - If you use Cursor, Claude Code, Copilot, getting g */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01a_establish.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 1: Veo clip - Great-grandmother figured out sixty years ago */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01d_zoom_out.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 1B: Hold on accumulated weight (01e) - 6 second contemplative hold */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_01B_START}>
          <AbsoluteFill>
            <HoldAccumulatedWeight
              durationFrames={BEATS.VISUAL_01B_END - BEATS.VISUAL_01B_START}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 2: Veo clip - When socks got cheap enough she stopped */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01f_modern_sock_toss.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 3: Code Blinks (01f) - Code just got that cheap */}
      {/* Standalone contemplative beat: full-frame patched code with blinking cursor. */}
      {/* The only motion is the cursor blink -- viewer absorbs accumulated technical debt. */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <CodeBlinks
            durationFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}
          />
        </Sequence>
      )}

      {/* Visual 3B: Code Regenerates (01g) - Deletion, empty beat, line-by-line regeneration
          Spec 01g: 15-second sequence with 7 animation phases:
            selection flash (0.2s) -> delete sweep (0.8s) -> empty beat (1s) ->
            terminal activity (0.2s) -> regeneration (0.8s) -> terminal done (0.2s) ->
            hold on clean code (11.8s) with title crossfade in final 3s.
          "The empty beat is critical -- do not rush it." */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_03B_START}>
          <AbsoluteFill>
            <CodeRegeneratesVisual
              localFrame={frame - BEATS.VISUAL_03B_START}
              totalFrames={BEATS.VISUAL_03B_END - BEATS.VISUAL_03B_START}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 4: Title card — "Prompt-Driven Development" over dimmed code
          Spec: ~10 seconds (300 frames at 30fps).
          Frame 0-60: code dims 1.0->0.15, editor chrome fades, terminal fades, vignette fades in.
          Frame 30-90: title fades in with upward drift, overlapping code dim.
          Frame 45-90: glow blooms gently behind title (delayed accent).
          Frame 90-270: contemplative hold — pure stillness, no animation.
          Frame 270-300: transition prep — title at full opacity at cut. */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <TitleCardVisual parentFrame={frame} startFrame={BEATS.VISUAL_04_START} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};


/**
 * Title Card visual (VISUAL_04) — the "poster frame" of the entire video.
 * Implements the full spec: animated code dimming (easeInOutCubic),
 * editor chrome fade-out, terminal fade-out, vignette overlay,
 * title with separate glow layer, easeOutCubic easing, and 6-second hold.
 */
const TitleCardVisual: React.FC<{ parentFrame: number; startFrame: number }> = ({
  parentFrame,
  startFrame,
}) => {
  // Local frame relative to VISUAL_04_START
  const f = parentFrame - startFrame;

  // Scaled from original 300-frame (10s) design to 90 frames (3s) — ratio 0.3.
  // Frame 0-18: code dims, chrome/terminal fade. Frame 9-27: title fades in.
  // Frame 27-90: hold with title at full opacity.

  // ── Frame 0-18 (0-0.6s): Background code dims from 1.0 to 0.15 ──
  const codeDim = interpolate(
    f,
    [0, 18],
    [1, 0.15],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // ── Frame 0-14: Editor chrome fades out ──
  const chromeFade = interpolate(
    f,
    [0, 14],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Frame 0-9: Terminal snippet fades out ──
  const terminalFade = interpolate(
    f,
    [0, 9],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Frame 9-27 (0.3-0.9s): Title fades in with upward drift ──
  const titleOpacity = interpolate(
    f,
    [9, 27],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const titleY = interpolate(
    f,
    [9, 27],
    [20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Frame 14-27: Glow blooms gently ──
  const glowOpacity = interpolate(
    f,
    [14, 27],
    [0, 0.15],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // ── Frame 0-18: Vignette fades in ──
  const vignetteOpacity = interpolate(
    f,
    [0, 18],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Frames 27-90: Hold (pure stillness) — title at full opacity at cut.

  return (
    <AbsoluteFill style={{ backgroundColor: "#1E1E2E" }}>
      {/* Dimmed regenerated code backdrop — animates from full to 0.15 opacity */}
      <div style={{
        position: "absolute",
        top: "50%",
        left: "50%",
        transform: "translate(-50%, -50%)",
        opacity: codeDim,
      }}>
        <div style={{ background: "#1E1E2E", padding: 24, borderRadius: 12, border: "1px solid #333", width: 880 }}>
          <pre style={{ fontSize: 14, fontFamily: "'JetBrains Mono', monospace", color: "#8a9caf", margin: 0, lineHeight: 1.6 }}>{`def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:\n    """Parse and validate user input string.\n\n    Args:\n        raw_input: The raw input string to parse, or None.\n        context: Optional context dictionary for strict mode filtering.\n\n    Returns:\n        Parsed result dictionary, or error dictionary on failure.\n    """\n    if raw_input is None:\n        return {"error": "null_input", "value": None}\n    text = raw_input if isinstance(raw_input, str) else raw_input.decode("utf-8", errors="replace")\n    result = _inner_parse(text)\n    if context and context.get("strict_mode"):\n        result = {k: v for k, v in result.items() if not k.startswith("_")}\n    return result`}</pre>
        </div>
      </div>

      {/* Editor chrome — top bar fading out */}
      <div style={{
        position: "absolute",
        top: 0,
        left: 0,
        right: 0,
        height: 36,
        background: "#252535",
        borderBottom: "1px solid #333",
        display: "flex",
        alignItems: "center",
        paddingLeft: 16,
        opacity: chromeFade,
      }}>
        <div style={{ display: "flex", gap: 6 }}>
          <div style={{ width: 12, height: 12, borderRadius: "50%", background: "#FF5F56" }} />
          <div style={{ width: 12, height: 12, borderRadius: "50%", background: "#FFBD2E" }} />
          <div style={{ width: 12, height: 12, borderRadius: "50%", background: "#27C93F" }} />
        </div>
        <span style={{ marginLeft: 16, fontFamily: "'JetBrains Mono', monospace", fontSize: 12, color: "#888" }}>
          user_parser.py
        </span>
      </div>

      {/* Editor chrome — line number gutter fading out */}
      <div style={{
        position: "absolute",
        top: 36,
        left: 0,
        width: 48,
        bottom: 0,
        background: "#1a1a28",
        borderRight: "1px solid #2a2a3e",
        opacity: chromeFade,
        display: "flex",
        flexDirection: "column",
        alignItems: "flex-end",
        paddingRight: 8,
        paddingTop: 12,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 12,
        color: "#555",
        lineHeight: "1.6",
      }}>
        {Array.from({ length: 16 }, (_, i) => (
          <div key={i}>{47 + i}</div>
        ))}
      </div>

      {/* Terminal snippet — fades out completely over first second */}
      <div style={{
        position: "absolute",
        bottom: 40,
        right: 40,
        opacity: terminalFade,
      }}>
        <div style={{
          width: 300,
          padding: "8px 12px",
          backgroundColor: "#252535",
          borderRadius: 6,
          border: "1px solid #333",
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 12,
        }}>
          <div style={{ color: "#E0E0E0" }}>$ pdd generate user_parser</div>
          <div style={{ color: "#888" }}>Generating from prompt...</div>
          <div style={{ color: "#5AAA6E" }}>Done. (0.8s) {"\u2713"}</div>
        </div>
      </div>

      {/* Vignette overlay — soft radial darkening, center bright, edges ~85% darkness */}
      <div style={{
        position: "absolute",
        top: 0,
        left: 0,
        right: 0,
        bottom: 0,
        background: "radial-gradient(ellipse at center, transparent 40%, rgba(0, 0, 0, 0.85) 100%)",
        opacity: vignetteOpacity,
        pointerEvents: "none",
      }} />

      {/* Title container — positioned ~5% above true center (top: 45%) for visual balance */}
      <div style={{
        position: "absolute",
        top: "45%",
        left: "50%",
        transform: `translate(-50%, -50%) translateY(${titleY}px)`,
        opacity: titleOpacity,
        textAlign: "center",
      }}>
        {/* Glow layer (behind text) — separate div with radial gradient per spec */}
        {/* Bloom radius ~40px via inset: -40, filter: blur(20px) */}
        <div style={{
          position: "absolute",
          inset: -40,
          background: `radial-gradient(ellipse at center, rgba(74, 144, 217, ${glowOpacity}) 0%, transparent 70%)`,
          filter: "blur(20px)",
          pointerEvents: "none",
        }} />

        {/* Title text */}
        <h1 style={{
          fontFamily: "Inter, -apple-system, sans-serif",
          fontWeight: 600,
          fontSize: 72,
          color: "#F8F4F0",
          letterSpacing: "0.02em",
          lineHeight: 1.2,
          margin: 0,
          position: "relative",
          textShadow: "0 2px 20px rgba(0,0,0,0.5)",
        }}>
          Prompt-Driven Development
        </h1>
      </div>
    </AbsoluteFill>
  );
};
