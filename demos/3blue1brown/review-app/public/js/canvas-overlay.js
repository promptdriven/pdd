/**
 * Canvas overlay module - drawing layer over the video.
 */
const CanvasOverlay = {
  canvas: null,
  ctx: null,
  active: false,
  currentTool: 'freehand',
  color: '#ff4444',
  strokeWidth: 4,
  paths: [],
  _drawing: false,
  _currentPath: null,
  _startX: 0,
  _startY: 0,
  INTERNAL_W: 1920,
  INTERNAL_H: 1080,

  init() {
    this.canvas = document.getElementById('draw-canvas');
    this.ctx = this.canvas.getContext('2d');
    this.canvas.width = this.INTERNAL_W;
    this.canvas.height = this.INTERNAL_H;

    this._bindEvents();
  },

  _bindEvents() {
    this.canvas.addEventListener('pointerdown', e => this._onPointerDown(e));
    this.canvas.addEventListener('pointermove', e => this._onPointerMove(e));
    this.canvas.addEventListener('pointerup', e => this._onPointerUp(e));
    this.canvas.addEventListener('pointerleave', e => this._onPointerUp(e));

    // Color and stroke width
    document.getElementById('draw-color').addEventListener('input', e => {
      this.color = e.target.value;
    });
    document.getElementById('stroke-width').addEventListener('change', e => {
      this.strokeWidth = parseInt(e.target.value, 10);
    });

    // Tool buttons
    document.querySelectorAll('.tool-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        this.setTool(btn.dataset.tool);
      });
    });
  },

  setActive(active) {
    this.active = active;
    this.canvas.classList.toggle('active', active);
    document.getElementById('draw-toggle').classList.toggle('active', active);
  },

  toggleActive() {
    this.setActive(!this.active);
  },

  setTool(tool) {
    this.currentTool = tool;
    document.querySelectorAll('.tool-btn').forEach(btn => {
      btn.classList.toggle('active', btn.dataset.tool === tool);
    });
    // Activate drawing if not already
    if (!this.active) this.setActive(true);
  },

  _toCanvasCoords(e) {
    const rect = this.canvas.getBoundingClientRect();
    return {
      x: ((e.clientX - rect.left) / rect.width) * this.INTERNAL_W,
      y: ((e.clientY - rect.top) / rect.height) * this.INTERNAL_H,
    };
  },

  _onPointerDown(e) {
    if (!this.active) return;
    this._drawing = true;
    const { x, y } = this._toCanvasCoords(e);
    this._startX = x;
    this._startY = y;

    if (this.currentTool === 'text') {
      this._drawing = false;
      this._showTextDialog(x, y);
      return;
    }

    if (this.currentTool === 'freehand') {
      this._currentPath = {
        tool: 'freehand',
        color: this.color,
        strokeWidth: this.strokeWidth,
        points: [{ x, y }],
      };
    } else {
      this._currentPath = {
        tool: this.currentTool,
        color: this.color,
        strokeWidth: this.strokeWidth,
        startX: x,
        startY: y,
        endX: x,
        endY: y,
      };
    }
  },

  _onPointerMove(e) {
    if (!this._drawing || !this._currentPath) return;
    const { x, y } = this._toCanvasCoords(e);

    if (this.currentTool === 'freehand') {
      this._currentPath.points.push({ x, y });
    } else {
      this._currentPath.endX = x;
      this._currentPath.endY = y;
    }
    this._render();
  },

  _onPointerUp(e) {
    if (!this._drawing || !this._currentPath) return;
    this._drawing = false;

    // For freehand, ignore very short paths (accidental clicks)
    if (this.currentTool === 'freehand' && this._currentPath.points.length < 2) {
      this._currentPath = null;
      return;
    }

    this.paths.push(this._currentPath);
    this._currentPath = null;
    this._render();
  },

  _showTextDialog(x, y) {
    const dialog = document.getElementById('text-dialog');
    const input = document.getElementById('text-dialog-input');
    const rect = this.canvas.getBoundingClientRect();

    // Position dialog near click point
    const domX = rect.left + (x / this.INTERNAL_W) * rect.width;
    const domY = rect.top + (y / this.INTERNAL_H) * rect.height;
    dialog.style.left = `${domX}px`;
    dialog.style.top = `${domY}px`;
    dialog.style.display = 'flex';
    input.value = '';
    input.focus();

    const cleanup = () => {
      dialog.style.display = 'none';
      okBtn.removeEventListener('click', onOk);
      cancelBtn.removeEventListener('click', onCancel);
      input.removeEventListener('keydown', onKey);
    };

    const onOk = () => {
      if (input.value.trim()) {
        this.paths.push({
          tool: 'text',
          color: this.color,
          strokeWidth: this.strokeWidth,
          x,
          y,
          text: input.value.trim(),
        });
        this._render();
      }
      cleanup();
    };

    const onCancel = () => cleanup();

    const onKey = (e) => {
      if (e.key === 'Enter') onOk();
      if (e.key === 'Escape') onCancel();
    };

    const okBtn = document.getElementById('text-dialog-ok');
    const cancelBtn = document.getElementById('text-dialog-cancel');
    okBtn.addEventListener('click', onOk);
    cancelBtn.addEventListener('click', onCancel);
    input.addEventListener('keydown', onKey);
  },

  _render() {
    this.ctx.clearRect(0, 0, this.INTERNAL_W, this.INTERNAL_H);

    // Draw all committed paths
    for (const p of this.paths) {
      this._drawPath(p);
    }

    // Draw current in-progress path
    if (this._currentPath) {
      this._drawPath(this._currentPath);
    }
  },

  _drawPath(p) {
    this.ctx.strokeStyle = p.color;
    this.ctx.fillStyle = p.color;
    this.ctx.lineWidth = p.strokeWidth;
    this.ctx.lineCap = 'round';
    this.ctx.lineJoin = 'round';

    switch (p.tool) {
      case 'freehand':
        if (p.points.length < 2) return;
        this.ctx.beginPath();
        this.ctx.moveTo(p.points[0].x, p.points[0].y);
        for (let i = 1; i < p.points.length; i++) {
          this.ctx.lineTo(p.points[i].x, p.points[i].y);
        }
        this.ctx.stroke();
        break;

      case 'rectangle':
        this.ctx.beginPath();
        this.ctx.rect(p.startX, p.startY, p.endX - p.startX, p.endY - p.startY);
        this.ctx.stroke();
        break;

      case 'circle': {
        const rx = Math.abs(p.endX - p.startX) / 2;
        const ry = Math.abs(p.endY - p.startY) / 2;
        const cx = (p.startX + p.endX) / 2;
        const cy = (p.startY + p.endY) / 2;
        this.ctx.beginPath();
        this.ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI * 2);
        this.ctx.stroke();
        break;
      }

      case 'arrow': {
        const dx = p.endX - p.startX;
        const dy = p.endY - p.startY;
        const angle = Math.atan2(dy, dx);
        const headLen = Math.max(15, p.strokeWidth * 4);

        // Shaft
        this.ctx.beginPath();
        this.ctx.moveTo(p.startX, p.startY);
        this.ctx.lineTo(p.endX, p.endY);
        this.ctx.stroke();

        // Arrowhead
        this.ctx.beginPath();
        this.ctx.moveTo(p.endX, p.endY);
        this.ctx.lineTo(
          p.endX - headLen * Math.cos(angle - Math.PI / 6),
          p.endY - headLen * Math.sin(angle - Math.PI / 6)
        );
        this.ctx.moveTo(p.endX, p.endY);
        this.ctx.lineTo(
          p.endX - headLen * Math.cos(angle + Math.PI / 6),
          p.endY - headLen * Math.sin(angle + Math.PI / 6)
        );
        this.ctx.stroke();
        break;
      }

      case 'text':
        this.ctx.font = `${Math.max(20, p.strokeWidth * 6)}px sans-serif`;
        this.ctx.fillText(p.text, p.x, p.y);
        break;
    }
  },

  undo() {
    if (this.paths.length === 0) return;
    this.paths.pop();
    this._render();
  },

  clear() {
    this.paths = [];
    this._render();
  },

  getDrawingData() {
    return {
      canvasWidth: this.INTERNAL_W,
      canvasHeight: this.INTERNAL_H,
      paths: JSON.parse(JSON.stringify(this.paths)),
    };
  },

  loadDrawingData(data) {
    if (!data || !data.paths) {
      this.paths = [];
    } else {
      this.paths = JSON.parse(JSON.stringify(data.paths));
    }
    this._render();
  },

  compositeWithVideo(videoEl) {
    const canvas = document.createElement('canvas');
    canvas.width = this.INTERNAL_W;
    canvas.height = this.INTERNAL_H;
    const ctx = canvas.getContext('2d');
    ctx.drawImage(videoEl, 0, 0, this.INTERNAL_W, this.INTERNAL_H);
    ctx.drawImage(this.canvas, 0, 0);
    return canvas.toDataURL('image/jpeg', 0.8);
  },

  hasDrawing() {
    return this.paths.length > 0;
  },
};
