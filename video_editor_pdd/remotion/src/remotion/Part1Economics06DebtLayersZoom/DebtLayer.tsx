import React from "react";

interface DebtLayerProps {
  /** Top offset of the layer */
  top: number;
  /** Height of the layer */
  layerHeight: number;
  /** Width of the layer */
  layerWidth: number;
  /** Left offset */
  left: number;
  /** Fill color */
  fillColor: string;
  /** Fill opacity */
  fillOpacity: number;
  /** Label text */
  label: string;
  /** Label color */
  labelColor: string;
  /** Label opacity (0-1) for fade-in */
  labelOpacity: number;
  /** Label font size */
  labelFontSize: number;
  /** Label font weight */
  labelFontWeight: number;
  /** Font family */
  fontFamily: string;
  /** Optional children (e.g., noise overlay) */
  children?: React.ReactNode;
  /** Border radius for the shape */
  borderRadius?: number;
}

const DebtLayer: React.FC<DebtLayerProps> = ({
  top,
  layerHeight,
  layerWidth,
  left,
  fillColor,
  fillOpacity,
  label,
  labelColor,
  labelOpacity,
  labelFontSize,
  labelFontWeight,
  fontFamily,
  children,
  borderRadius = 4,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        top,
        left,
        width: layerWidth,
        height: layerHeight,
        borderRadius,
        overflow: "hidden",
      }}
    >
      {/* Layer fill */}
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

      {/* Noise overlay or other children */}
      {children}

      {/* Label — centered in the layer */}
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
          pointerEvents: "none",
        }}
      >
        <span
          style={{
            fontFamily,
            fontSize: labelFontSize,
            fontWeight: labelFontWeight,
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
