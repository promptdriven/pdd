import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

const COL_WIDTHS = [200, 300, 200];
const TABLE_W = 800;
const ROW_BG = "#0F172A";
const ROW_BORDER = "#1E293B";
const VALUE_COLOR = "#E2E8F0";
const PAREN_COLOR = "#94A3B8";
const OWNER_COLOR = "#CDD6F4";
const ACCENT_W = 3;
const ROW_H = 60;
const TESTS_ACCENT = "#4A90D9";

interface TableRowProps {
  component: string;
  encodes: string;
  parenthetical: string;
  owner: string;
  accentColor: string;
  /** Frame at which this row starts animating */
  startFrame: number;
  /** Vertical position (top) */
  topY: number;
}

export const TableRowItem: React.FC<TableRowProps> = ({
  component,
  encodes,
  parenthetical,
  owner,
  accentColor,
  startFrame,
  topY,
}) => {
  const frame = useCurrentFrame();

  const localFrame = frame - startFrame;

  // Slide in from left
  const slideX = interpolate(localFrame, [0, 20], [-40, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const opacity = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Tests row glow effect
  const isTestsRow = accentColor === TESTS_ACCENT;
  let glowOpacity = 0;
  if (isTestsRow && localFrame >= 20) {
    const glowLocal = localFrame - 20;
    glowOpacity = interpolate(glowLocal, [0, 10, 25], [0, 0.35, 0], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    });
  }

  if (localFrame < 0) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: topY,
        left: (1920 - TABLE_W) / 2,
        width: TABLE_W,
        height: ROW_H,
        opacity,
        transform: `translateX(${slideX}px)`,
      }}
    >
      {/* Glow behind row for Tests */}
      {isTestsRow && glowOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            inset: -4,
            borderRadius: 4,
            boxShadow: `0 0 20px 4px ${TESTS_ACCENT}`,
            opacity: glowOpacity,
            pointerEvents: "none",
          }}
        />
      )}

      <div
        style={{
          width: "100%",
          height: "100%",
          backgroundColor: ROW_BG,
          borderBottom: `1px solid ${ROW_BORDER}`,
          borderLeft: `${ACCENT_W}px solid ${accentColor}`,
          display: "flex",
          flexDirection: "row",
          alignItems: "center",
        }}
      >
        {/* Component name */}
        <div
          style={{
            width: COL_WIDTHS[0] - ACCENT_W,
            paddingLeft: 24 - ACCENT_W,
            paddingRight: 24,
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            fontWeight: 700,
            color: accentColor,
          }}
        >
          {component}
        </div>

        {/* Encodes */}
        <div
          style={{
            width: COL_WIDTHS[1],
            paddingLeft: 24,
            paddingRight: 24,
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            fontWeight: 400,
            color: VALUE_COLOR,
            display: "flex",
            alignItems: "baseline",
            gap: 6,
          }}
        >
          <span>{encodes}</span>
          {parenthetical && (
            <span
              style={{
                fontSize: 14,
                color: PAREN_COLOR,
              }}
            >
              {parenthetical}
            </span>
          )}
        </div>

        {/* Owner */}
        <div
          style={{
            width: COL_WIDTHS[2],
            paddingLeft: 24,
            paddingRight: 24,
            fontFamily: "Inter, sans-serif",
            fontSize: 16,
            fontWeight: 400,
            color: OWNER_COLOR,
          }}
        >
          {owner}
        </div>
      </div>
    </div>
  );
};

export default TableRowItem;
