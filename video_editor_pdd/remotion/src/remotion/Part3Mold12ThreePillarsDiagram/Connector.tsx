import React from "react";
import { CONNECTOR_FONT_SIZE, CONNECTOR_COLOR, EQUALS_FONT_SIZE, EQUALS_COLOR } from "./constants";

interface ConnectorProps {
  text: string;
  opacity: number;
  scale?: number;
  isEquals?: boolean;
}

export const Connector: React.FC<ConnectorProps> = ({
  text,
  opacity,
  scale = 1,
  isEquals = false,
}) => {
  return (
    <div
      style={{
        fontFamily: "Inter, sans-serif",
        fontWeight: 700,
        fontSize: isEquals ? EQUALS_FONT_SIZE : CONNECTOR_FONT_SIZE,
        color: isEquals ? EQUALS_COLOR : CONNECTOR_COLOR,
        opacity,
        transform: `scale(${scale})`,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        flexShrink: 0,
        width: 40,
      }}
    >
      {text}
    </div>
  );
};

export default Connector;
