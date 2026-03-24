[Remotion]

# Section 0.5: Code Blink — Patched Function

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description

Return to the code side from the opening split. A dark IDE canvas fills the screen — full-width now, no split. The viewer sees a complex function (~25 lines) in a dark-themed editor. The function is visibly patched: inline comments like `// patched 2024-01`, `// workaround for edge case`, `// TODO: clean this up`, and multiple indentation levels revealing accumulated complexity.

A cursor blinks at the end of line 14, inside the densest section of the function. The code is readable but clearly burdened — this function has been maintained, not designed. It *works*, but it carries the weight of every fix that came before.

The scene holds for a beat. Then a hard cut to the next spec (code regeneration).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (dark IDE background)
- No split — full-screen code view

### Chart/Visual Elements

#### IDE Chrome
- Top bar: thin `#161B22` bar, 32px tall, with three dots (red/yellow/green at left), filename `auth_handler.py` in `#94A3B8` at 0.5
- Line numbers: `#484F58` at 0.4, JetBrains Mono 13px, right-aligned in a 48px gutter
- Code area: starts at x: 60, full width minus 40px right padding

#### Function Code
- Font: JetBrains Mono, 14px
- Base code color: `#E2E8F0` at 0.7
- Keywords (`def`, `if`, `return`, `try`, `except`): `#FF7B72` (red-orange)
- Strings: `#A5D6FF` (light blue)
- Comments: `#8B949E` at 0.5 (gray)
- Patch comments (highlighted): `#D9944A` at 0.6 (amber) — these stand out
- Function name: `#D2A8FF` (purple)
- Indentation guides: `#21262D` 1px vertical lines

#### Patch Comments (visible)
- Line 3: `# patched 2024-01 — handle None case`
- Line 8: `# workaround: upstream API sometimes returns 403`
- Line 14: `# TODO: clean this up after migration`
- Line 19: `# edge case fix (see ticket #4721)`

#### Cursor
- Blinking block cursor at end of line 14, color `#58A6FF`, 500ms on/off cycle
- Position: after `# TODO: clean this up after migration`

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut from sock toss. Full-screen IDE appears instantly.
2. **Frame 5-15 (0.17-0.5s):** Code fades in with subtle `#0D1117` → visible text transition.
3. **Frame 15-45 (0.5-1.5s):** Code fully visible. Cursor blinks. The function sits with all its accumulated patches. Hold.
4. **Frame 45-60 (1.5-2s):** Continue hold. Cursor blinks once more. Beat before the delete.

### Typography
- Code: JetBrains Mono, 14px, various syntax colors
- Comments: JetBrains Mono, 14px, `#8B949E` at 0.5
- Patch comments: JetBrains Mono, 14px, `#D9944A` at 0.6
- Line numbers: JetBrains Mono, 13px, `#484F58` at 0.4
- Filename: Inter, 13px, `#94A3B8` at 0.5

### Easing
- Code fade-in: `easeOut(quad)` over 10 frames
- Cursor blink: linear on/off, 15 frames per phase (500ms cycle)

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_005`

- **0:14** ("Code just got"): Full-screen code visible, cursor blinking on patched function
- **0:15** ("that cheap"): Hold — the function sits heavy with accumulated patches

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* IDE chrome — top bar */}
    <IDETopBar filename="auth_handler.py" />

    {/* Code block with syntax highlighting */}
    <Sequence from={5}>
      <FadeIn duration={10}>
        <CodeBlock
          language="python"
          font="JetBrains Mono"
          fontSize={14}
          lineNumberColor="#484F58"
          lines={[
            { code: 'def validate_auth_token(token, context=None):', type: 'function_def' },
            { code: '    """Validate and decode auth token."""', type: 'docstring' },
            { code: '    # patched 2024-01 — handle None case', type: 'patch_comment' },
            { code: '    if token is None:', type: 'keyword' },
            { code: '        return AuthResult(valid=False, reason="empty")', type: 'normal' },
            { code: '    try:', type: 'keyword' },
            { code: '        decoded = jwt.decode(token, SECRET, algorithms=["HS256"])', type: 'normal' },
            { code: '        # workaround: upstream API sometimes returns 403', type: 'patch_comment' },
            { code: '        if decoded.get("exp") and decoded["exp"] < time.time():', type: 'normal' },
            { code: '            if context and context.get("allow_grace"):', type: 'normal' },
            { code: '                decoded["exp"] = time.time() + 300', type: 'normal' },
            { code: '            else:', type: 'keyword' },
            { code: '                return AuthResult(valid=False, reason="expired")', type: 'normal' },
            { code: '        # TODO: clean this up after migration', type: 'patch_comment' },
            { code: '        user = lookup_user(decoded.get("sub", ""))', type: 'normal' },
            { code: '        if not user:', type: 'keyword' },
            { code: '            user = create_provisional_user(decoded)', type: 'normal' },
            { code: '        return AuthResult(valid=True, user=user, token=decoded)', type: 'normal' },
            { code: '    # edge case fix (see ticket #4721)', type: 'patch_comment' },
            { code: '    except jwt.InvalidSignatureError:', type: 'keyword' },
            { code: '        log_security_event("invalid_sig", token[:8])', type: 'normal' },
            { code: '        return AuthResult(valid=False, reason="bad_signature")', type: 'normal' },
            { code: '    except Exception as e:', type: 'keyword' },
            { code: '        return AuthResult(valid=False, reason=str(e))', type: 'normal' }
          ]}
        />
      </FadeIn>
    </Sequence>

    {/* Blinking cursor at line 14 */}
    <Sequence from={15}>
      <BlinkingCursor
        line={14}
        column={48}
        color="#58A6FF"
        blinkRate={15}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_display",
  "language": "python",
  "filename": "auth_handler.py",
  "lineCount": 24,
  "patchComments": [
    { "line": 3, "text": "# patched 2024-01 — handle None case" },
    { "line": 8, "text": "# workaround: upstream API sometimes returns 403" },
    { "line": 14, "text": "# TODO: clean this up after migration" },
    { "line": 19, "text": "# edge case fix (see ticket #4721)" }
  ],
  "cursorPosition": { "line": 14, "column": 48 },
  "theme": "dark_ide",
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_005"]
}
```

---
