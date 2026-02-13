/**
 * Main app controller - initializes modules and handles keyboard shortcuts.
 */
(async function () {
  // Load sections from server
  const sections = await ApiClient.getSections();

  // Initialize modules
  VideoPlayer.init(sections);
  CanvasOverlay.init();
  AnnotationPanel.init();
  SpeechInput.init();

  // Export button
  document.getElementById('export-btn').addEventListener('click', () => {
    window.open(ApiClient.exportUrl(), '_blank');
  });

  // Draw toggle
  document.getElementById('draw-toggle').addEventListener('click', () => {
    CanvasOverlay.toggleActive();
  });

  // Undo
  document.getElementById('undo-btn').addEventListener('click', () => {
    CanvasOverlay.undo();
  });

  // Auto-pause and enable drawing when draw mode activated
  // (Video pauses when you start drawing for a smoother experience)

  // Spacebar annotation mode toggle
  let annotating = false;
  let saving = false;

  async function finishAnnotating() {
    if (saving) return;
    saving = true;
    SpeechInput.stop();
    CanvasOverlay.setActive(false);
    try {
      await AnnotationPanel.save();
    } finally {
      annotating = false;
      saving = false;
      VideoPlayer.video.play();
    }
  }

  // Keyboard shortcuts
  document.addEventListener('keydown', (e) => {
    // Don't capture when typing in inputs
    const tag = e.target.tagName;
    if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') {
      // Allow Ctrl+S in textarea
      if (e.key === 's' && (e.ctrlKey || e.metaKey)) {
        e.preventDefault();
        AnnotationPanel.save();
      }
      return;
    }

    switch (e.key) {
      case ' ':
        e.preventDefault();
        if (saving) break;
        if (!annotating) {
          // First press: pause, enable mic + draw
          VideoPlayer.video.pause();
          annotating = true;
          if (AnnotationPanel.editingId) AnnotationPanel.exitEditMode();
          CanvasOverlay.setActive(true);
          SpeechInput.start();
        } else {
          // Second press: stop mic + draw, save, resume
          finishAnnotating();
        }
        break;

      case 'k':
      case 'K':
        VideoPlayer.togglePlay();
        break;

      case 'd':
      case 'D':
        CanvasOverlay.toggleActive();
        break;

      case 'm':
      case 'M':
        SpeechInput.toggle();
        break;

      case 'z':
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          CanvasOverlay.undo();
        }
        break;

      case 'Escape':
        annotating = false;
        CanvasOverlay.setActive(false);
        SpeechInput.stop();
        break;

      case 's':
        if (e.ctrlKey || e.metaKey) {
          e.preventDefault();
          AnnotationPanel.save();
        }
        break;

      case 'ArrowLeft':
        e.preventDefault();
        if (e.shiftKey) {
          VideoPlayer.frameStep(-1);
        } else {
          VideoPlayer.seekRelative(-5);
        }
        break;

      case 'ArrowRight':
        e.preventDefault();
        if (e.shiftKey) {
          VideoPlayer.frameStep(1);
        } else {
          VideoPlayer.seekRelative(5);
        }
        break;

      case 'f':
      case 'F':
        CanvasOverlay.setTool('freehand');
        break;

      case 'r':
      case 'R':
        CanvasOverlay.setTool('rectangle');
        break;

      case 'c':
      case 'C':
        CanvasOverlay.setTool('circle');
        break;

      case 'a':
      case 'A':
        CanvasOverlay.setTool('arrow');
        break;

      case 't':
      case 'T':
        CanvasOverlay.setTool('text');
        break;
    }
  });

  // Add keyboard shortcuts hint
  const hint = document.createElement('div');
  hint.className = 'shortcuts-hint';
  hint.innerHTML = '<kbd>Space</kbd> Annotate (pause+mic+draw → save+resume) &middot; <kbd>K</kbd> Play/Pause &middot; <kbd>D</kbd> Draw &middot; <kbd>M</kbd> Mic &middot; <kbd>Ctrl+S</kbd> Save &middot; <kbd>Ctrl+Z</kbd> Undo &middot; <kbd>&larr;&rarr;</kbd> Seek &middot; <kbd>Shift+&larr;&rarr;</kbd> Frame step';
  document.querySelector('.video-area').appendChild(hint);
})();
