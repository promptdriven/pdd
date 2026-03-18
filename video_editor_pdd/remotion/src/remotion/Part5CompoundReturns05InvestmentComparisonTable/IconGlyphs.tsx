import React from "react";

const ICON_COLOR = "rgba(148, 163, 184, 0.4)";
const ICON_SIZE = 20;

export const BugIcon: React.FC = () => (
  <svg
    width={ICON_SIZE}
    height={ICON_SIZE}
    viewBox="0 0 24 24"
    fill="none"
    stroke={ICON_COLOR}
    strokeWidth={2}
    strokeLinecap="round"
    strokeLinejoin="round"
    style={{ marginRight: 10, flexShrink: 0 }}
  >
    {/* Bug body */}
    <ellipse cx="12" cy="14" rx="5" ry="6" />
    {/* Head */}
    <circle cx="12" cy="7" r="2" />
    {/* Antennae */}
    <line x1="10" y1="5.5" x2="7" y2="2" />
    <line x1="14" y1="5.5" x2="17" y2="2" />
    {/* Legs left */}
    <line x1="7" y1="11" x2="4" y2="9" />
    <line x1="7" y1="14" x2="4" y2="14" />
    <line x1="7" y1="17" x2="4" y2="19" />
    {/* Legs right */}
    <line x1="17" y1="11" x2="20" y2="9" />
    <line x1="17" y1="14" x2="20" y2="14" />
    <line x1="17" y1="17" x2="20" y2="19" />
  </svg>
);

export const CodeIcon: React.FC = () => (
  <svg
    width={ICON_SIZE}
    height={ICON_SIZE}
    viewBox="0 0 24 24"
    fill="none"
    stroke={ICON_COLOR}
    strokeWidth={2}
    strokeLinecap="round"
    strokeLinejoin="round"
    style={{ marginRight: 10, flexShrink: 0 }}
  >
    {/* Code brackets with arrow */}
    <polyline points="16 18 22 12 16 6" />
    <polyline points="8 6 2 12 8 18" />
    <line x1="14" y1="4" x2="10" y2="20" />
  </svg>
);

export const DocIcon: React.FC = () => (
  <svg
    width={ICON_SIZE}
    height={ICON_SIZE}
    viewBox="0 0 24 24"
    fill="none"
    stroke={ICON_COLOR}
    strokeWidth={2}
    strokeLinecap="round"
    strokeLinejoin="round"
    style={{ marginRight: 10, flexShrink: 0 }}
  >
    {/* Document */}
    <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z" />
    <polyline points="14 2 14 8 20 8" />
    <line x1="8" y1="13" x2="16" y2="13" />
    <line x1="8" y1="17" x2="16" y2="17" />
  </svg>
);

export const getIcon = (type: string): React.ReactNode => {
  switch (type) {
    case "bug":
      return <BugIcon />;
    case "code":
      return <CodeIcon />;
    case "doc":
      return <DocIcon />;
    default:
      return null;
  }
};
