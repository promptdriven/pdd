/**
 * Speech input module - Web Speech API wrapper.
 */
const SpeechInput = {
  recognition: null,
  isRecording: false,
  wasUsed: false,
  supported: false,

  init() {
    const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
    if (!SpeechRecognition) {
      document.getElementById('mic-btn').style.display = 'none';
      return;
    }

    this.supported = true;
    this.recognition = new SpeechRecognition();
    this.recognition.continuous = true;
    this.recognition.interimResults = true;
    this.recognition.lang = 'en-US';

    this._bindEvents();
  },

  _bindEvents() {
    const micBtn = document.getElementById('mic-btn');
    micBtn.addEventListener('click', () => this.toggle());

    this.recognition.onresult = (event) => {
      const textarea = document.getElementById('annotation-text');
      let interim = '';
      let final = '';

      for (let i = event.resultIndex; i < event.results.length; i++) {
        const transcript = event.results[i][0].transcript;
        if (event.results[i].isFinal) {
          final += transcript;
        } else {
          interim += transcript;
        }
      }

      if (final) {
        // Append final text with a space separator
        const existing = textarea.value;
        textarea.value = existing + (existing ? ' ' : '') + final;
        this.wasUsed = true;
      }
    };

    this.recognition.onerror = (event) => {
      console.error('Speech recognition error:', event.error);
      this.stop();
    };

    this.recognition.onend = () => {
      // Restart if still supposed to be recording (continuous mode can stop unexpectedly)
      if (this.isRecording) {
        try {
          this.recognition.start();
        } catch (e) {
          this.stop();
        }
      }
    };
  },

  toggle() {
    if (this.isRecording) {
      this.stop();
    } else {
      this.start();
    }
  },

  start() {
    if (!this.supported || this.isRecording) return;
    try {
      this.recognition.start();
      this.isRecording = true;
      document.getElementById('mic-btn').classList.add('recording');
    } catch (e) {
      console.error('Failed to start speech recognition:', e);
    }
  },

  stop() {
    if (!this.supported) return;
    this.isRecording = false;
    document.getElementById('mic-btn').classList.remove('recording');
    try {
      this.recognition.stop();
    } catch (e) {
      // ignore
    }
  },
};
