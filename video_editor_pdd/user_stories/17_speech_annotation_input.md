# User Story 17: Speech-to-Text Annotation Input

**As a** director reviewing video,
**I want to** speak my annotation feedback aloud while drawing,
**So that** I can describe issues hands-free without switching between drawing and typing.

## Acceptance Criteria

- [ ] Web Speech API recognition starts automatically when Space is pressed (annotation mode activated)
- [ ] Speech recognition stops when Space is pressed again (annotation mode deactivated)
- [ ] Transcribed speech text is combined with any typed text into the annotation's `text` field
- [ ] Annotation records `inputMethod` as `"typed"`, `"speech"`, or `"mixed"` depending on how text was entered
- [ ] Mic toggle shortcut (M) allows pausing/resuming speech recognition during annotation
- [ ] Visual indicator shows when speech recognition is active (e.g., pulsing mic icon)
- [ ] Speech recognition errors (e.g., browser not supported, permission denied) show a non-blocking warning and fall back to text-only input

## Mapping to PRD

- Section 4.2 (The Spacebar Workflow — speech recognition starts/stops with Space)
- Section 4.1 (Annotation Model — `text.inputMethod: "typed" | "speech" | "mixed"`)
- Section 9.2 (Review/Fix Loop — speech-to-text input)

## Technical Notes

- Uses browser-native Web Speech API (`webkitSpeechRecognition` / `SpeechRecognition`)
- Speech text is appended to any typed text with a space separator
- Recognition should use `continuous: true` and `interimResults: true` for real-time feedback
- Not all browsers support Web Speech API; graceful degradation required
