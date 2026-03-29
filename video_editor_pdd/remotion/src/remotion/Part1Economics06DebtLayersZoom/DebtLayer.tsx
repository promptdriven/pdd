// DebtLayer.tsx — A single debt layer with fill, optional noise, and label
import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import { NoiseTexture } from "./NoiseTexture";
import {
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_FONT_FAMILY,
  LABEL_MIN_OPACITY,
  LABEL_FADE_START,
  LABEL_FADE_END,
} from "./constants";

interface DebtLayerProps {
  /** Absolute top position of this layer */
  top: number;
  /** Height of this layer */
  layerHeight: number;
  /** Left edge */
  left: number;
  /** Width of the layer */
  layerWidth: number;
  /** Fill color */
  fillColor: string;
  /** Fill opacity */
  fillOpacity: number;
  /** Label text */
  label: string;
  /** Label color */
  labelColor: string;
  /** Whether to show noise texture overlay */
  showNoise?: boolean;
  /** Current opacity of the entire layer (for split animation) */
  layerOpacity?: number;
}

export const DebtLayer: React.FC<DebtLayerProps> = ({
  top,
  layerHeight,
  left,
  layerWidth,
  fillColor,
  fillOpacity,
  label,
  labelColor,
  showNoise = false,
  layerOpacity = 1,
}) => {
  const frame = useCurrentFrame();

  // Label fades in from frame 180-200
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, LABEL_MIN_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top,
        left,
        width: layerWidth,
        height: layerHeight,
        opacity: layerOpacity,
        overflow: "hidden",
      }}
    >
      {/* Fill background */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          backgroundColor: fillColor,
          opacity: fillOpacity,
        }}
      />

      {/* Optional noise overlay for Context Rot */}
      {showNoise && (
        <NoiseTexture width={layerWidth} height={layerHeight} />
      )}

      {/* Label centered within the layer */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
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
          }}
        >
          {label}
        </span>
      </div>
    </div>
  );
};

export default DebtLayer;
