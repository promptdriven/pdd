import React from "react";

interface IconProps {
  size: number;
  color: string;
}

/* ── BEFORE icons (manual / warm amber) ── */

export const NeedleThreadIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <line
      x1="16" y1="48" x2="44" y2="12"
      stroke={color} strokeWidth={2.5} strokeLinecap="round"
    />
    <circle cx="46" cy="10" r="3" stroke={color} strokeWidth={2} />
    <path
      d="M16 48C16 48 10 40 18 34C26 28 22 20 14 22C6 24 8 34 16 36C24 38 28 30 24 24"
      stroke={color} strokeWidth={2} strokeLinecap="round" fill="none" opacity={0.7}
    />
  </svg>
);

export const HandsSculptingIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <ellipse cx="32" cy="38" rx="14" ry="10" stroke={color} strokeWidth={2.5} />
    <path d="M10 30C10 30 14 28 18 32L20 36" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M8 26L12 28" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M8 30L10 30" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M54 30C54 30 50 28 46 32L44 36" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M56 26L52 28" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M56 30L54 30" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M26 36C28 34 36 34 38 36" stroke={color} strokeWidth={1.5} opacity={0.5} />
  </svg>
);

export const PencilRulerIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <path
      d="M18 50L12 54L14 48L38 16L42 20L18 50Z"
      stroke={color} strokeWidth={2} strokeLinejoin="round"
    />
    <path d="M38 16L42 20" stroke={color} strokeWidth={2.5} strokeLinecap="round" />
    <line x1="14" y1="48" x2="18" y2="50" stroke={color} strokeWidth={1.5} />
    <rect
      x="36" y="22" width="6" height="34" rx="1"
      stroke={color} strokeWidth={2} transform="rotate(-20 39 39)"
    />
    <line x1="38" y1="30" x2="42" y2="29" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="39" y1="34" x2="43" y2="33" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="40" y1="38" x2="44" y2="37" stroke={color} strokeWidth={1.5} opacity={0.6} />
  </svg>
);

/* ── AFTER icons (specification / cool blue) ── */

export const FactoryLoomIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <rect x="12" y="14" width="40" height="36" rx="2" stroke={color} strokeWidth={2.5} />
    <line x1="16" y1="24" x2="48" y2="24" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="16" y1="30" x2="48" y2="30" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="16" y1="36" x2="48" y2="36" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="16" y1="42" x2="48" y2="42" stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1="22" y1="18" x2="22" y2="46" stroke={color} strokeWidth={1.5} opacity={0.4} />
    <line x1="32" y1="18" x2="32" y2="46" stroke={color} strokeWidth={1.5} opacity={0.4} />
    <line x1="42" y1="18" x2="42" y2="46" stroke={color} strokeWidth={1.5} opacity={0.4} />
    <circle cx="52" cy="14" r="5" stroke={color} strokeWidth={2} />
    <circle cx="52" cy="14" r="2" fill={color} opacity={0.4} />
  </svg>
);

export const InjectionMoldIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <rect x="14" y="10" width="36" height="16" rx="2" stroke={color} strokeWidth={2.5} />
    <rect x="14" y="38" width="36" height="16" rx="2" stroke={color} strokeWidth={2.5} />
    <path
      d="M22 26L22 30C22 33 26 38 32 38C38 38 42 33 42 30L42 26"
      stroke={color} strokeWidth={2} opacity={0.6}
    />
    <path d="M32 4L32 10" stroke={color} strokeWidth={3} strokeLinecap="round" />
    <path d="M28 4L36 4" stroke={color} strokeWidth={2} strokeLinecap="round" />
    <path d="M8 20L12 20" stroke={color} strokeWidth={1.5} strokeLinecap="round" opacity={0.5} />
    <path d="M8 44L12 44" stroke={color} strokeWidth={1.5} strokeLinecap="round" opacity={0.5} />
  </svg>
);

export const CodeTerminalIcon: React.FC<IconProps> = ({ size, color }) => (
  <svg width={size} height={size} viewBox="0 0 64 64" fill="none">
    <rect x="8" y="12" width="48" height="40" rx="4" stroke={color} strokeWidth={2.5} />
    <line x1="8" y1="22" x2="56" y2="22" stroke={color} strokeWidth={2} />
    <circle cx="16" cy="17" r="2" fill={color} opacity={0.5} />
    <circle cx="23" cy="17" r="2" fill={color} opacity={0.5} />
    <circle cx="30" cy="17" r="2" fill={color} opacity={0.5} />
    <path
      d="M16 30L22 34L16 38"
      stroke={color} strokeWidth={2} strokeLinecap="round" strokeLinejoin="round"
    />
    <line x1="26" y1="38" x2="42" y2="38" stroke={color} strokeWidth={2} strokeLinecap="round" opacity={0.6} />
    <line x1="26" y1="44" x2="38" y2="44" stroke={color} strokeWidth={2} strokeLinecap="round" opacity={0.4} />
  </svg>
);

/* ── Type maps ── */

export type BeforeIconType = "needle_thread" | "hands_sculpting" | "pencil_ruler";
export type AfterIconType = "factory_loom" | "injection_mold" | "code_terminal";

export const BEFORE_ICON_MAP: Record<BeforeIconType, React.FC<IconProps>> = {
  needle_thread: NeedleThreadIcon,
  hands_sculpting: HandsSculptingIcon,
  pencil_ruler: PencilRulerIcon,
};

export const AFTER_ICON_MAP: Record<AfterIconType, React.FC<IconProps>> = {
  factory_loom: FactoryLoomIcon,
  injection_mold: InjectionMoldIcon,
  code_terminal: CodeTerminalIcon,
};
