import React from "react";

export const AccentBar: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        bottom: 0,
        width: 4,
        borderRadius: "16px 0 0 16px",
        background: "linear-gradient(to bottom, #EF4444, #F59E0B)",
      }}
    />
  );
};

export default AccentBar;
