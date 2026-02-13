/**
 * Video player module - HTML5 video wrapper with custom controls and section switching.
 */
const VideoPlayer = {
  video: null,
  seekBar: null,
  playBtn: null,
  timeDisplay: null,
  speedSelect: null,
  sectionSelect: null,
  sections: [],
  currentSection: null, // null = full video

  init(sections) {
    this.video = document.getElementById('video-player');
    this.seekBar = document.getElementById('seek-bar');
    this.playBtn = document.getElementById('play-btn');
    this.timeDisplay = document.getElementById('time-display');
    this.speedSelect = document.getElementById('speed-select');
    this.sectionSelect = document.getElementById('section-select');
    this.sections = sections;

    this._populateSections();
    this._bindEvents();
  },

  _populateSections() {
    // Section select in toolbar
    this.sectionSelect.innerHTML = '<option value="full">Full Video</option>';
    for (const s of this.sections) {
      const opt = document.createElement('option');
      opt.value = s.id;
      opt.textContent = s.label;
      this.sectionSelect.appendChild(opt);
    }

    // Section context dropdown (for full video mode - tag which section an annotation is for)
    const contextSelect = document.getElementById('section-context');
    contextSelect.innerHTML = '';
    for (const s of this.sections) {
      const opt = document.createElement('option');
      opt.value = s.id;
      opt.textContent = s.label;
      contextSelect.appendChild(opt);
    }

    // Filter dropdown
    const filterSection = document.getElementById('filter-section');
    filterSection.innerHTML = '<option value="">All Sections</option>';
    for (const s of this.sections) {
      const opt = document.createElement('option');
      opt.value = s.id;
      opt.textContent = s.label;
      filterSection.appendChild(opt);
    }
  },

  _bindEvents() {
    this.video.addEventListener('timeupdate', () => this._onTimeUpdate());
    this.video.addEventListener('loadedmetadata', () => this._onMetadata());
    this.video.addEventListener('play', () => { this.playBtn.textContent = 'Pause'; });
    this.video.addEventListener('pause', () => { this.playBtn.textContent = 'Play'; });

    this.playBtn.addEventListener('click', () => this.togglePlay());

    this.seekBar.addEventListener('input', () => {
      const time = (this.seekBar.value / 100) * this.video.duration;
      this.video.currentTime = time;
    });

    this.speedSelect.addEventListener('change', () => {
      this.video.playbackRate = parseFloat(this.speedSelect.value);
    });

    this.sectionSelect.addEventListener('change', () => {
      this._switchSection(this.sectionSelect.value);
    });
  },

  _switchSection(value) {
    const wasPlaying = !this.video.paused;
    if (value === 'full') {
      this.currentSection = null;
      this.video.src = '/video/full';
      document.getElementById('section-context-row').style.display = '';
    } else {
      const section = this.sections.find(s => s.id === value);
      if (!section) return;
      this.currentSection = section;
      this.video.src = `/video/sections/${section.file}`;
      document.getElementById('section-context-row').style.display = 'none';
    }
    this.video.load();
    if (wasPlaying) {
      this.video.play().catch(() => {});
    }
    // Clear canvas when switching
    if (typeof CanvasOverlay !== 'undefined') {
      CanvasOverlay.clear();
    }
  },

  _onTimeUpdate() {
    if (!this.video.duration) return;
    const pct = (this.video.currentTime / this.video.duration) * 100;
    this.seekBar.value = pct;
    this.timeDisplay.textContent =
      `${this._formatTime(this.video.currentTime)} / ${this._formatTime(this.video.duration)}`;
  },

  _onMetadata() {
    this.seekBar.max = 100;
    this._onTimeUpdate();
  },

  _formatTime(seconds) {
    const m = Math.floor(seconds / 60);
    const s = seconds % 60;
    return `${String(m).padStart(2, '0')}:${s.toFixed(1).padStart(4, '0')}`;
  },

  togglePlay() {
    if (this.video.paused) {
      this.video.play().catch(() => {});
    } else {
      this.video.pause();
    }
  },

  seekRelative(seconds) {
    this.video.currentTime = Math.max(0, Math.min(this.video.duration, this.video.currentTime + seconds));
  },

  frameStep(direction) {
    this.video.pause();
    // Approximate frame step at 30fps
    this.video.currentTime = Math.max(0,
      Math.min(this.video.duration, this.video.currentTime + (direction * (1 / 30))));
  },

  seekTo(time) {
    this.video.currentTime = time;
  },

  getCurrentTime() {
    return this.video.currentTime;
  },

  getFormattedTime() {
    return this._formatTime(this.video.currentTime);
  },

  getCurrentSectionId() {
    if (this.currentSection) return this.currentSection.id;
    // In full video mode, use the section-context selector
    return document.getElementById('section-context').value;
  },

  getCurrentFile() {
    if (this.currentSection) return this.currentSection.file;
    return 'full_video.mp4';
  },

  getSourceType() {
    return this.currentSection ? 'section' : 'full';
  },

  captureFrame() {
    const canvas = document.createElement('canvas');
    canvas.width = this.video.videoWidth || 1920;
    canvas.height = this.video.videoHeight || 1080;
    const ctx = canvas.getContext('2d');
    ctx.drawImage(this.video, 0, 0, canvas.width, canvas.height);
    return canvas.toDataURL('image/jpeg', 0.7);
  },

  switchToSection(sectionId) {
    this.sectionSelect.value = sectionId === null ? 'full' : sectionId;
    this._switchSection(this.sectionSelect.value);
  },
};
