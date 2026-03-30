import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_FONT_FAMILY,
  LABEL_FADE_START,
  LABEL_FADE_END,
} from "./constants";

interface DebtLayerProps {
  /** Absolute left position within the zoomed container */
  left: number;
  /** Absolute top position within the zoomed container */
  top: number;
  /** Width of the layer rectangle */
  width: number;
  /** Height of the layer rectangle */
  height: number;
  /** Fill color for the layer */
  fillColor: string;
  /** Fill opacity for the layer */
  fillOpacity: number;
  /** Text label to display centered in the layer */
  label: string;
  /** Color for the label text */
  labelColor: string;
  /** Whether to show the label (controls fade-in animation) */
  showLabel: boolean;
  /** Optional children (e.g., noise overlay) */
  children?: React.ReactNode;
}

/**
 * A single debt layer rectangle with centered label.
 * Used for both "Code Complexity" (lower) and "Context Rot" (upper) layers.
 */
export const DebtLayer: React.FC<DebtLayerProps> = ({
  left,
  top,
  width,
  height,
  fillColor,
  fillOpacity,
  label,
  labelColor,
  showLabel,
  children,
}) => {
  const frame = useCurrentFrame();

  // Label fade-in animation
  const labelOpacity = showLabel
    ? interpolate(
        frame,
        [LABEL_FADE_START, LABEL_FADE_END],
        [0, 0.95],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        }
      )
    : 0;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width,
        height,
        overflow: "hidden",
        borderRadius: 2,
      }}
    >
      {/* Layer fill */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundColor: fillColor,
          opacity: fillOpacity,
        }}
      />

      {/* Optional children (noise texture, etc.) */}
      {children}

      {/* Centered label */}
      {showLabel && (
        <div
          style={{
            position: "absolute",
            inset: 0,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            opacity: labelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: LABEL_FONT_FAMILY,
              fontSize: LABEL_FONT_SIZE,
              fontWeight: LABEL_FONT_WEIGHT,
              color: labelColor,
              letterSpacing: "0.05em",
              textTransform: "uppercase",
              textShadow: `0 1px 4px rgba(0,0,0,0.6)`,
            }}
          >
            {label}
          </span>
        </div>
      )}
    </div>
  );
};

export default DebtLayer;
