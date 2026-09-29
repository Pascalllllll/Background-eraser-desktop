'use strict';
(() => {
  // The photo lives in two full resolution RGBA buffers: `orig` (never modified) and `work`.
  // Display and history both use 512px tiles so edits only touch the pixels they change.
  const TS = 512, SH = 9;
  const MAX_PX = 60e6;

  const $ = (s) => document.querySelector(s);
  const $$ = (s) => Array.from(document.querySelectorAll(s));
  const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  const frame = () => new Promise((r) => requestAnimationFrame(() => r()));
  const yieldUI = () => new Promise((r) => setTimeout(r, 0));
  const store = {
    get(k) { try { return localStorage.getItem(k); } catch { return null; } },
    set(k, v) { try { localStorage.setItem(k, v); } catch { /* private mode */ } },
  };

  const view = $('#view');
  const vctx = view.getContext('2d');
  const wrap = $('#wrap');

  let W = 0, H = 0, orig = null, work = null, work32 = null, fileBase = 'photo';
  let tiles = [], cols = 0;
  const cam = { s: 1, x: 0, y: 0, fitted: true };
  let cw = 0, ch = 0, dpr = 1;
  let tool = 'erase';
  const brush = { size: 60, hardness: 70, strength: 100 };
  const sn = { mode: 'click', reach: 'contiguous', tol: 14, soft: 10, sample: 3, sampling: 'once', clean: true, color: null };
  let bgMode = 'checker', comparing = false, busy = false, spaceDown = false, unsaved = false;
  const hist = { undo: [], redo: [], bytes: 0 };
  const mem = navigator.deviceMemory || 4;
  const BUDGET = (mem >= 8 ? 900 : mem >= 4 ? 450 : 200) * 1048576;
  let lastFill = null;
  let stroke = null;
  let gesture = null;
  const pointers = new Map();
  const hover = { on: false, x: 0, y: 0, touch: false };
  const colors = { accent: '#b196ff', checkA: '#37324a', checkB: '#2a263a' };
  let checker = null;

  /* ------------------------------------------------------------------ color matching */

  const LIN = new Float64Array(256);
  for (let i = 0; i < 256; i++) {
    const c = i / 255;
    LIN[i] = c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4);
  }
  const fl = (t) => (t > 0.008856 ? Math.cbrt(t) : 7.787 * t + 16 / 116);
  function toLab(r, g, b) {
    const R = LIN[r], G = LIN[g], B = LIN[b];
    const x = fl((R * 0.4124564 + G * 0.3575761 + B * 0.1804375) / 0.95047);
    const y = fl(R * 0.2126729 + G * 0.7151522 + B * 0.072175);
    const z = fl((R * 0.0193339 + G * 0.119192 + B * 0.9503041) / 1.08883);
    return [116 * y - 16, 500 * (x - y), 200 * (y - z)];
  }

  // Returns how strongly a pixel matches the target: 1 inside tolerance, fading to 0 across
  // the softness band. Distance is CIELAB delta E, so tolerance tracks what the eye sees.
  // A small direct-mapped cache makes flat backgrounds nearly free.
  function makeMatcher(col, tol, soft) {
    const keys = new Int32Array(16384).fill(-1);
    const vals = new Float32Array(16384);
    let L0 = 0, A0 = 0, B0 = 0;
    const fn = (r, g, b) => {
      const key = (r << 16) | (g << 8) | b;
      const h = Math.imul(key, 0x9e3779b1) >>> 18;
      if (keys[h] === key) return vals[h];
      const R = LIN[r], G = LIN[g], B = LIN[b];
      const x = fl((R * 0.4124564 + G * 0.3575761 + B * 0.1804375) / 0.95047);
      const y = fl(R * 0.2126729 + G * 0.7151522 + B * 0.072175);
      const z = fl((R * 0.0193339 + G * 0.119192 + B * 0.9503041) / 1.08883);
      const dl = 116 * y - 16 - L0, da = 500 * (x - y) - A0, db = 200 * (y - z) - B0;
      const d = Math.sqrt(dl * dl + da * da + db * db);
      const m = d <= tol ? 1 : soft > 0 && d < tol + soft ? 1 - (d - tol) / soft : 0;
      keys[h] = key; vals[h] = m;
      return m;
    };
    fn.set = (c) => { [L0, A0, B0] = toLab(c[0], c[1], c[2]); keys.fill(-1); };
    fn.set(col);
    return fn;
  }

  const hex = (c) => '#' + c.map((v) => v.toString(16).padStart(2, '0')).join('');
  const sameColor = (a, b) => a && b && a[0] === b[0] && a[1] === b[1] && a[2] === b[2];

  /* ------------------------------------------------------------------ tiles */

  function buildTiles() {
    for (const t of tiles) t.cv.width = t.cv.height = 0;
    tiles = [];
    cols = Math.ceil(W / TS);
    const rows = Math.ceil(H / TS);
    for (let ty = 0; ty < rows; ty++) {
      for (let tx = 0; tx < cols; tx++) {
        const x = tx * TS, y = ty * TS, w = Math.min(TS, W - x), h = Math.min(TS, H - y);
        const cv = document.createElement('canvas');
        cv.width = w; cv.height = h;
        tiles.push({ x, y, w, h, cv, ctx: cv.getContext('2d'), dirty: true });
      }
    }
  }

  const idCache = new Map();
  function scratchID(w, h) {
    const k = w * 65536 + h;
    let id = idCache.get(k);
    if (!id) { id = new ImageData(w, h); idCache.set(k, id); }
    return id;
  }

  function flushTiles() {
    const src = comparing ? orig : work;
    for (const t of tiles) {
      if (!t.dirty) continue;
      const id = scratchID(t.w, t.h), d = id.data, rl = t.w * 4;
      for (let y = 0; y < t.h; y++) {
        const a = ((t.y + y) * W + t.x) * 4;
        d.set(src.subarray(a, a + rl), y * rl);
      }
      t.ctx.putImageData(id, 0, 0);
      t.dirty = false;
    }
  }
  function markAll() { for (const t of tiles) t.dirty = true; req(); }

  function readTile(ti) {
    const t = tiles[ti], rl = t.w * 4, buf = new Uint8ClampedArray(rl * t.h);
    for (let y = 0; y < t.h; y++) {
      const a = ((t.y + y) * W + t.x) * 4;
      buf.set(work.subarray(a, a + rl), y * rl);
    }
    return buf;
  }
  function writeTile(ti, buf) {
    const t = tiles[ti], rl = t.w * 4;
    for (let y = 0; y < t.h; y++) work.set(buf.subarray(y * rl, (y + 1) * rl), ((t.y + y) * W + t.x) * 4);
  }
  const rowTmp = new Uint8ClampedArray(TS * 4);
  function swapTile(ti, buf) {
    const t = tiles[ti], rl = t.w * 4;
    for (let y = 0; y < t.h; y++) {
      const a = ((t.y + y) * W + t.x) * 4, o = y * rl;
      rowTmp.set(work.subarray(a, a + rl));
      work.set(buf.subarray(o, o + rl), a);
      buf.set(rowTmp.subarray(0, rl), o);
    }
  }
  function sameTile(ti, buf) {
    const t = tiles[ti], b32 = new Uint32Array(buf.buffer);
    for (let y = 0; y < t.h; y++) {
      const a = (t.y + y) * W + t.x, o = y * t.w;
      for (let x = 0; x < t.w; x++) if (work32[a + x] !== b32[o + x]) return false;
    }
    return true;
  }

  /* ------------------------------------------------------------------ history */

  // An Op snapshots each tile the first time it is touched. On commit, unchanged tiles are
  // dropped and the rest become the undo entry. Undo and redo swap the stored tile with the
  // live one, so every entry holds one copy per changed tile, not two.
  class Op {
    constructor(label) { this.label = label; this.snaps = new Array(tiles.length); this.list = []; }
    touch(ti) {
      let s = this.snaps[ti];
      if (!s) { s = this.snaps[ti] = readTile(ti); this.list.push(ti); }
      return s;
    }
    revert() {
      for (const ti of this.list) { writeTile(ti, this.snaps[ti]); tiles[ti].dirty = true; }
      req();
    }
  }

  function commit(op, keepFill) {
    const parts = [];
    let bytes = 0;
    for (const ti of op.list) {
      const s = op.snaps[ti];
      if (!sameTile(ti, s)) { parts.push({ ti, buf: s }); bytes += s.byteLength; }
    }
    if (!keepFill) lastFill = null;
    if (!parts.length) return null;
    const e = { label: op.label, parts, bytes };
    for (const r of hist.redo) hist.bytes -= r.bytes;
    hist.redo = [];
    hist.undo.push(e);
    hist.bytes += bytes;
    while (hist.bytes > BUDGET && hist.undo.length > 1) hist.bytes -= hist.undo.shift().bytes;
    unsaved = true;
    syncHistory();
    return e;
  }
  function swapEntry(e) {
    for (const p of e.parts) { swapTile(p.ti, p.buf); tiles[p.ti].dirty = true; }
    req();
  }
  function undo() {
    if (busy || stroke || !hist.undo.length) return;
    const e = hist.undo.pop();
    swapEntry(e);
    hist.redo.push(e);
    lastFill = null; unsaved = true;
    syncHistory();
  }
  function redo() {
    if (busy || stroke || !hist.redo.length) return;
    const e = hist.redo.pop();
    swapEntry(e);
    hist.undo.push(e);
    lastFill = null; unsaved = true;
    syncHistory();
  }
  function syncHistory() {
    const u = hist.undo[hist.undo.length - 1], r = hist.redo[hist.redo.length - 1];
    $('#undoBtn').disabled = !u;
    $('#redoBtn').disabled = !r;
    $('#undoBtn').title = u ? `Undo ${u.label} (Ctrl+Z)` : 'Undo (Ctrl+Z)';
    $('#redoBtn').title = r ? `Redo ${r.label} (Ctrl+Shift+Z)` : 'Redo (Ctrl+Shift+Z)';
  }

  /* ------------------------------------------------------------------ brush strokes */

  // Each stroke keeps a per pixel coverage map, so overlapping dabs never stack: a pixel's
  // result depends on the strongest dab that reached it, computed from the pre-stroke snapshot.
  function sampleAt(x, y, k) {
    x = Math.floor(x); y = Math.floor(y);
    if (x < 0 || y < 0 || x >= W || y >= H) return null;
    const h = (k - 1) >> 1;
    let r = 0, g = 0, b = 0, ws = 0;
    for (let yy = y - h; yy <= y + h; yy++) {
      for (let xx = x - h; xx <= x + h; xx++) {
        if (xx < 0 || yy < 0 || xx >= W || yy >= H) continue;
        const i = (yy * W + xx) * 4, a = work[i + 3];
        if (!a) continue;
        r += work[i] * a; g += work[i + 1] * a; b += work[i + 2] * a; ws += a;
      }
    }
    if (!ws || !work[(y * W + x) * 4 + 3]) return null;
    return [Math.round(r / ws), Math.round(g / ws), Math.round(b / ws)];
  }

  function beginStroke(p) {
    const kind = tool;
    const label = kind === 'erase' ? 'Erase' : kind === 'restore' ? 'Restore' : 'Sniper brush';
    stroke = { kind, op: new Op(label), cov: new Array(tiles.length), lx: p.x, ly: p.y, col: null, match: null };
    if (kind === 'sniper') {
      if (sn.sampling === 'swatch') {
        if (!sn.color) toast('Pick a target color first, or switch Sampling to Once.');
        else setStrokeColor(sn.color);
      } else {
        const c = sampleAt(p.x, p.y, 1);
        if (c) setStrokeColor(c);
      }
    }
    dabAt(p.x, p.y);
  }
  function setStrokeColor(c) {
    stroke.col = c;
    if (stroke.match) stroke.match.set(c);
    else stroke.match = makeMatcher(c, sn.tol, sn.soft);
    if (!sameColor(sn.color, c)) { sn.color = c; syncSwatch(); }
  }
  function strokeTo(p) {
    const s = stroke;
    const dx = p.x - s.lx, dy = p.y - s.ly, dist = Math.hypot(dx, dy);
    const step = Math.max(0.5, brush.size * 0.08);
    if (dist < step) return;
    const n = Math.floor(dist / step), ux = dx / dist * step, uy = dy / dist * step;
    for (let i = 1; i <= n; i++) dabAt(s.lx + ux * i, s.ly + uy * i);
    s.lx += ux * n; s.ly += uy * n;
  }
  function endStroke() {
    if (!stroke) return;
    const op = stroke.op;
    stroke = null;
    commit(op);
  }
  function cancelStroke() {
    if (!stroke) return;
    stroke.op.revert();
    stroke = null;
  }

  let bfsVis = new Uint8Array(0);
  function dabAt(cx, cy) {
    const s = stroke;
    const r = Math.max(0.5, brush.size / 2);
    if (brush.size <= 2) { cx = Math.floor(cx) + 0.5; cy = Math.floor(cy) + 0.5; }
    const x0 = Math.max(0, Math.floor(cx - r)), x1 = Math.min(W, Math.ceil(cx + r));
    const y0 = Math.max(0, Math.floor(cy - r)), y1 = Math.min(H, Math.ceil(cy + r));
    if (x0 >= x1 || y0 >= y1) return;

    for (let ty = y0 >> SH; ty <= (y1 - 1) >> SH; ty++) {
      for (let tx = x0 >> SH; tx <= (x1 - 1) >> SH; tx++) {
        const ti = ty * cols + tx;
        s.op.touch(ti);
        if (!s.cov[ti]) s.cov[ti] = new Uint8Array(tiles[ti].w * tiles[ti].h);
        tiles[ti].dirty = true;
      }
    }
    const inner = r * brush.hardness / 100, band = Math.max(1e-6, r - inner), str = brush.strength / 100;
    const falloff = (d) => { if (d <= inner) return 1; const t = (r - d) / band; return t * t * (3 - 2 * t); };

    if (s.kind !== 'sniper') {
      const erase = s.kind === 'erase';
      for (let y = y0; y < y1; y++) {
        const dy = y + 0.5 - cy;
        for (let x = x0; x < x1; x++) {
          const dx = x + 0.5 - cx, d = Math.sqrt(dx * dx + dy * dy);
          if (d >= r) continue;
          const c = (falloff(d) * 255 + 0.5) | 0;
          if (!c) continue;
          const ti = (y >> SH) * cols + (x >> SH), t = tiles[ti];
          const k = (y - t.y) * t.w + (x - t.x), cov = s.cov[ti];
          if (c <= cov[k]) continue;
          cov[k] = c;
          const snap = s.op.snaps[ti], j = k * 4, i = (y * W + x) * 4, amt = c / 255 * str;
          if (erase) {
            work[i + 3] = snap[j + 3] * (1 - amt);
          } else {
            work[i] = snap[j] + (orig[i] - snap[j]) * amt;
            work[i + 1] = snap[j + 1] + (orig[i + 1] - snap[j + 1]) * amt;
            work[i + 2] = snap[j + 2] + (orig[i + 2] - snap[j + 2]) * amt;
            work[i + 3] = snap[j + 3] + (orig[i + 3] - snap[j + 3]) * amt;
          }
        }
      }
      req();
      return;
    }

    // Sniper brush: like Photoshop's Background Eraser. Only pixels close to the sampled
    // color are erased, scaled by the brush falloff.
    const sx = clamp(Math.floor(cx), x0, x1 - 1), sy = clamp(Math.floor(cy), y0, y1 - 1);
    if (sn.sampling === 'continuous' || !s.col) {
      if (sn.sampling !== 'swatch') {
        const ti = (sy >> SH) * cols + (sx >> SH), t = tiles[ti];
        const snap = s.op.snaps[ti], j = ((sy - t.y) * t.w + (sx - t.x)) * 4;
        if (snap[j + 3] >= 128) {
          const c = [snap[j], snap[j + 1], snap[j + 2]];
          if (!sameColor(c, s.col)) setStrokeColor(c);
        }
      }
    }
    if (!s.match) return;
    const match = s.match, [br, bgc, bb] = s.col, clean = sn.clean;

    const applyPx = (x, y, f) => {
      const ti = (y >> SH) * cols + (x >> SH), t = tiles[ti];
      const k = (y - t.y) * t.w + (x - t.x), snap = s.op.snaps[ti], j = k * 4;
      if (!snap[j + 3]) return -1;
      const m = match(snap[j], snap[j + 1], snap[j + 2]);
      if (m <= 0) return 0;
      const c = (f * m * 255 + 0.5) | 0, cov = s.cov[ti];
      if (c > cov[k]) {
        cov[k] = c;
        const i = (y * W + x) * 4, keep = 1 - c / 255 * str;
        work[i + 3] = snap[j + 3] * keep;
        if (clean && keep > 0.004 && keep < 1) {
          const q = 1 - keep, inv = 1 / keep;
          work[i] = (snap[j] - q * br) * inv;
          work[i + 1] = (snap[j + 1] - q * bgc) * inv;
          work[i + 2] = (snap[j + 2] - q * bb) * inv;
        } else {
          work[i] = snap[j]; work[i + 1] = snap[j + 1]; work[i + 2] = snap[j + 2];
        }
      }
      return m;
    };

    if (sn.reach === 'global') {
      for (let y = y0; y < y1; y++) {
        const dy = y + 0.5 - cy;
        for (let x = x0; x < x1; x++) {
          const dx = x + 0.5 - cx, d = Math.sqrt(dx * dx + dy * dy);
          if (d < r) applyPx(x, y, falloff(d));
        }
      }
    } else {
      const bw = x1 - x0, bh = y1 - y0, n = bw * bh;
      if (bfsVis.length < n) bfsVis = new Uint8Array(n);
      else bfsVis.fill(0, 0, n);
      const start = (sy - y0) * bw + (sx - x0);
      const stack = [start];
      bfsVis[start] = 1;
      while (stack.length) {
        const p = stack.pop(), lx = p % bw, ly = (p - lx) / bw, x = lx + x0, y = ly + y0;
        const dx = x + 0.5 - cx, dy = y + 0.5 - cy, d = Math.sqrt(dx * dx + dy * dy);
        if (d >= r && p !== start) continue;
        const m = applyPx(x, y, d < r ? falloff(d) : 0);
        if (m < 1 && p !== start) continue;
        if (lx > 0 && !bfsVis[p - 1]) { bfsVis[p - 1] = 1; stack.push(p - 1); }
        if (lx < bw - 1 && !bfsVis[p + 1]) { bfsVis[p + 1] = 1; stack.push(p + 1); }
        if (ly > 0 && !bfsVis[p - bw]) { bfsVis[p - bw] = 1; stack.push(p - bw); }
        if (ly < bh - 1 && !bfsVis[p + bw]) { bfsVis[p + bw] = 1; stack.push(p + bw); }
      }
    }
    req();
  }

  /* ------------------------------------------------------------------ sniper click */

  // Like Photoshop's Magic Eraser, plus edge decontamination: a pixel that only partly
  // matches keeps the matching fraction as transparency, and that share of the target color
  // is subtracted from its RGB, so no halo of the old background is left on the edge.
  function runFill(x, y, col, reach) {
    const op = new Op('Sniper');
    const match = makeMatcher(col, sn.tol, sn.soft), clean = sn.clean;
    const [br, bgc, bb] = col;
    const apply = (i, ti, m) => {
      if (!op.snaps[ti]) op.touch(ti);
      const keep = 1 - m;
      if (clean && keep > 0.004 && keep < 1) {
        const q = 1 - keep, inv = 1 / keep;
        work[i] = (work[i] - q * br) * inv;
        work[i + 1] = (work[i + 1] - q * bgc) * inv;
        work[i + 2] = (work[i + 2] - q * bb) * inv;
      }
      work[i + 3] = work[i + 3] * keep;
      tiles[ti].dirty = true;
    };

    if (reach === 'global' || x == null) {
      for (let ti = 0; ti < tiles.length; ti++) {
        const t = tiles[ti];
        for (let yy = t.y; yy < t.y + t.h; yy++) {
          let i = (yy * W + t.x) * 4;
          for (let xx = 0; xx < t.w; xx++, i += 4) {
            if (!work[i + 3]) continue;
            const m = match(work[i], work[i + 1], work[i + 2]);
            if (m > 0) apply(i, ti, m);
          }
        }
      }
    } else {
      // Flood only spreads through pixels fully inside tolerance; softness shapes the border.
      const vis = new Uint8Array(W * H), start = y * W + x, stack = [start];
      vis[start] = 1;
      while (stack.length) {
        const p = stack.pop(), i = p * 4;
        if (!work[i + 3]) continue;
        const m = match(work[i], work[i + 1], work[i + 2]);
        if (m <= 0) continue;
        const px = p % W, py = (p - px) / W;
        apply(i, (py >> SH) * cols + (px >> SH), m);
        if (m < 1 && p !== start) continue;
        if (px > 0 && !vis[p - 1]) { vis[p - 1] = 1; stack.push(p - 1); }
        if (px < W - 1 && !vis[p + 1]) { vis[p + 1] = 1; stack.push(p + 1); }
        if (py > 0 && !vis[p - W]) { vis[p - W] = 1; stack.push(p - W); }
        if (py < H - 1 && !vis[p + W]) { vis[p + W] = 1; stack.push(p + W); }
      }
    }
    req();
    return commit(op, true);
  }

  async function fire(x, y, col, reach) {
    if (busy) return;
    const heavy = (reach === 'global' || x == null) && W * H > 4e6;
    if (heavy) { setBusy('Erasing'); await frame(); await frame(); }
    try {
      lastFill = { x, y, col, entry: null };
      lastFill.entry = runFill(x, y, col, reach);
    } finally {
      if (heavy) setBusy(null);
    }
    if (!lastFill.entry) toast('Nothing matched. Try a higher tolerance.');
  }

  function sniperClick(p) {
    const x = Math.floor(p.x), y = Math.floor(p.y);
    if (x < 0 || y < 0 || x >= W || y >= H) return;
    const col = sampleAt(x, y, sn.sample);
    if (!col) { toast('That spot is already clear.'); return; }
    sn.color = col;
    syncSwatch();
    fire(x, y, col, sn.reach);
  }

  // Re-run the last sniper click with the current settings, replacing its history entry.
  let retuneQueued = false;
  function retune() {
    if (!lastFill || retuneQueued) return;
    retuneQueued = true;
    requestAnimationFrame(() => {
      retuneQueued = false;
      const lf = lastFill;
      if (!lf || busy || stroke) return;
      if (lf.entry) {
        if (hist.undo[hist.undo.length - 1] !== lf.entry) { lastFill = null; return; }
        hist.undo.pop();
        hist.bytes -= lf.entry.bytes;
        swapEntry(lf.entry);
      }
      lf.entry = runFill(lf.x, lf.y, lf.col, lf.x == null ? 'global' : sn.reach);
      lastFill = lf;
      syncHistory();
    });
  }

  function restoreAll() {
    if (!W || busy) return;
    const op = new Op('Restore all');
    for (let ti = 0; ti < tiles.length; ti++) op.touch(ti);
    work.set(orig);
    markAll();
    if (commit(op)) toast('Whole photo restored. Undo brings your edits back.');
  }

  /* ------------------------------------------------------------------ auto */

  // Auto finds the main subject with RMBG-1.4, a 44 MB segmentation model run on this device
  // by ONNX Runtime Web. The model only sees a 1024 × 1024 copy, so its mask is then fitted
  // to the photo: a color guided filter snaps the upscaled outline onto real edges, and
  // blur-fusion foreground estimation takes the old background's tint out of soft edges.
  const ORT_URL = 'https://cdn.jsdelivr.net/npm/onnxruntime-web@1.22.0/dist/';
  const MODEL_URL = 'https://huggingface.co/briaai/RMBG-1.4/resolve/main/onnx/model_quantized.onnx';
  const MODEL_BYTES = 44403226, MS = 1024;
  const au = { remove: 'background', cutoff: 50, soft: 60, fit: true, clean: true };
  let auModel = null, auModelLoading = null;
  let auData = null;   // the detection for the current photo, kept so tuning never re-runs the model
  let lastAuto = null; // history entry of the last Auto run, replaced while tuning

  function pansOnly() { return tool === 'hand' || tool === 'auto'; }

  async function fetchModel(onProg) {
    let cache = null;
    try {
      cache = await caches.open('pluck-models');
      const hit = await cache.match(MODEL_URL);
      if (hit) return new Uint8Array(await hit.arrayBuffer());
    } catch { cache = null; /* no Cache API on file:// or in private mode */ }
    const res = await fetch(MODEL_URL);
    if (!res.ok || !res.body) throw new Error(`model download failed (${res.status})`);
    const total = +res.headers.get('content-length') || MODEL_BYTES;
    const reader = res.body.getReader(), chunks = [];
    let got = 0;
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value); got += value.length;
      onProg(Math.min(1, got / total));
    }
    const buf = new Uint8Array(got);
    let o = 0;
    for (const c of chunks) { buf.set(c, o); o += c.length; }
    if (cache) cache.put(MODEL_URL, new Response(buf)).catch(() => {});
    return buf;
  }

  async function loadModel() {
    if (auModel) return auModel;
    if (!auModelLoading) {
      auModelLoading = (async () => {
        const ort = await import(ORT_URL + 'ort.webgpu.min.mjs');
        ort.env.wasm.wasmPaths = ORT_URL;
        ort.env.wasm.numThreads = self.crossOriginIsolated ? Math.min(4, navigator.hardwareConcurrency || 1) : 1;
        const bytes = await fetchModel((f) => setBusy(`Downloading detection model ${Math.round(f * 100)}%`));
        setBusy('Starting detection model');
        await frame();
        let session = null;
        if (navigator.gpu) {
          try { session = await ort.InferenceSession.create(bytes, { executionProviders: ['webgpu'] }); } catch (err) { console.warn('WebGPU unavailable, using WebAssembly', err); }
        }
        if (!session) session = await ort.InferenceSession.create(bytes, { executionProviders: ['wasm'] });
        return { ort, session };
      })();
    }
    try { auModel = await auModelLoading; } finally { auModelLoading = null; }
    return auModel;
  }

  // Averages every source pixel into its target cell, straight from the full resolution
  // buffer, into planar 0–1 channels. Targets must not be larger than the photo.
  function shrink(src, tw, th) {
    const n = tw * th, R = new Float32Array(n), G = new Float32Array(n), B = new Float32Array(n), cnt = new Float32Array(n);
    const xm = new Int32Array(W);
    for (let x = 0; x < W; x++) xm[x] = Math.min(tw - 1, Math.floor(x * tw / W));
    for (let y = 0; y < H; y++) {
      const row = Math.min(th - 1, Math.floor(y * th / H)) * tw;
      let i = y * W * 4;
      for (let x = 0; x < W; x++, i += 4) {
        const k = row + xm[x];
        R[k] += src[i]; G[k] += src[i + 1]; B[k] += src[i + 2]; cnt[k]++;
      }
    }
    for (let k = 0; k < n; k++) { const s = 1 / (255 * cnt[k]); R[k] *= s; G[k] *= s; B[k] *= s; }
    return [R, G, B];
  }

  // Bilinear resize of one planar channel, pixel centers aligned.
  function resizeCh(src, sw, sh, tw, th) {
    const out = new Float32Array(tw * th), xa = new Int32Array(tw), xb = new Int32Array(tw), xf = new Float32Array(tw);
    for (let x = 0; x < tw; x++) {
      const f = clamp((x + 0.5) * sw / tw - 0.5, 0, sw - 1);
      xa[x] = Math.floor(f); xb[x] = Math.min(sw - 1, xa[x] + 1); xf[x] = f - xa[x];
    }
    for (let y = 0; y < th; y++) {
      const f = clamp((y + 0.5) * sh / th - 0.5, 0, sh - 1), y0 = Math.floor(f), fy = f - y0;
      const r0 = y0 * sw, r1 = Math.min(sh - 1, y0 + 1) * sw, o = y * tw;
      for (let x = 0; x < tw; x++) {
        const a = src[r0 + xa[x]] + (src[r0 + xb[x]] - src[r0 + xa[x]]) * xf[x];
        const b = src[r1 + xa[x]] + (src[r1 + xb[x]] - src[r1 + xa[x]]) * xf[x];
        out[o + x] = a + (b - a) * fy;
      }
    }
    return out;
  }

  // Mean over a (2r+1)² window, shrinking at the borders. Two running-sum passes, O(n).
  function boxMean(src, w, h, r) {
    const tmp = new Float32Array(w * h), out = new Float32Array(w * h);
    for (let y = 0; y < h; y++) {
      const o = y * w;
      let s = 0;
      for (let x = 0; x <= Math.min(r, w - 1); x++) s += src[o + x];
      for (let x = 0; x < w; x++) {
        const lo = x - r, hi = x + r;
        tmp[o + x] = s / (Math.min(hi, w - 1) - Math.max(lo, 0) + 1);
        if (hi + 1 < w) s += src[o + hi + 1];
        if (lo >= 0) s -= src[o + lo];
      }
    }
    for (let x = 0; x < w; x++) {
      let s = 0;
      for (let y = 0; y <= Math.min(r, h - 1); y++) s += tmp[y * w + x];
      for (let y = 0; y < h; y++) {
        const lo = y - r, hi = y + r;
        out[y * w + x] = s / (Math.min(hi, h - 1) - Math.max(lo, 0) + 1);
        if (hi + 1 < h) s += tmp[(hi + 1) * w + x];
        if (lo >= 0) s -= tmp[lo * w + x];
      }
    }
    return out;
  }

  const mul = (a, b) => { const o = new Float32Array(a.length); for (let i = 0; i < a.length; i++) o[i] = a[i] * b[i]; return o; };

  // Color guided filter (He et al.): the mask becomes a local linear function of the photo's
  // RGB, so the outline follows edges the photo actually has instead of the model's blur.
  function guidedFilter(I, p, w, h, r, eps) {
    const n = w * h, [R, G, B] = I, m = (a) => boxMean(a, w, h, r);
    const mR = m(R), mG = m(G), mB = m(B), mp = m(p);
    const mRp = m(mul(R, p)), mGp = m(mul(G, p)), mBp = m(mul(B, p));
    const vRR = m(mul(R, R)), vRG = m(mul(R, G)), vRB = m(mul(R, B)), vGG = m(mul(G, G)), vGB = m(mul(G, B)), vBB = m(mul(B, B));
    const aR = new Float32Array(n), aG = new Float32Array(n), aB = new Float32Array(n), bb = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const r_ = mR[i], g_ = mG[i], b_ = mB[i], P = mp[i];
      const cR = mRp[i] - r_ * P, cG = mGp[i] - g_ * P, cB = mBp[i] - b_ * P;
      const a11 = vRR[i] - r_ * r_ + eps, a12 = vRG[i] - r_ * g_, a13 = vRB[i] - r_ * b_;
      const a22 = vGG[i] - g_ * g_ + eps, a23 = vGB[i] - g_ * b_, a33 = vBB[i] - b_ * b_ + eps;
      const i11 = a22 * a33 - a23 * a23, i12 = a13 * a23 - a12 * a33, i13 = a12 * a23 - a13 * a22;
      const i22 = a11 * a33 - a13 * a13, i23 = a12 * a13 - a11 * a23, i33 = a11 * a22 - a12 * a12;
      const inv = 1 / (a11 * i11 + a12 * i12 + a13 * i13);
      const x = (i11 * cR + i12 * cG + i13 * cB) * inv;
      const y = (i12 * cR + i22 * cG + i23 * cB) * inv;
      const z = (i13 * cR + i23 * cG + i33 * cB) * inv;
      aR[i] = x; aG[i] = y; aB[i] = z; bb[i] = P - x * r_ - y * g_ - z * b_;
    }
    const maR = m(aR), maG = m(aG), maB = m(aB), mb = m(bb), q = new Float32Array(n);
    for (let i = 0; i < n; i++) q[i] = clamp(maR[i] * R[i] + maG[i] * G[i] + maB[i] * B[i] + mb[i], 0, 1);
    return q;
  }

  // Blur-fusion foreground and background estimation (Forte & Pitié 2021): the true colors
  // of each layer behind a half transparent pixel, found with two box-blur passes.
  function blurFusion(I, F, Bk, A, w, h, r) {
    const n = w * h, bA = boxMean(A, w, h, r), inv = new Float32Array(n), F2 = [], B2 = [];
    for (let i = 0; i < n; i++) inv[i] = 1 - A[i];
    for (let c = 0; c < 3; c++) {
      const bF = boxMean(mul(F[c], A), w, h, r), bB = boxMean(mul(Bk[c], inv), w, h, r);
      const f = new Float32Array(n), b = new Float32Array(n), Ic = I[c];
      for (let i = 0; i < n; i++) {
        const fv = bF[i] / (bA[i] + 1e-5), bv = bB[i] / (1 - bA[i] + 1e-5), a = A[i];
        const resid = Ic[i] - a * fv - (1 - a) * bv;
        f[i] = clamp(fv + a * resid, 0, 1);
        b[i] = clamp(bv + (1 - a) * resid, 0, 1);
      }
      F2.push(f); B2.push(b);
    }
    return { F: F2, B: B2 };
  }

  async function detect() {
    const { ort, session } = await loadModel();
    setBusy('Finding the subject');
    await frame(); await frame();
    // Guide resolution: as sharp as memory allows for the filters, never above the photo.
    const s = Math.min(1, 2048 / Math.max(W, H), Math.sqrt(2.4e6 / (W * H)));
    const gw = Math.max(1, Math.round(W * s)), gh = Math.max(1, Math.round(H * s));
    const rgb = shrink(orig, gw, gh);
    const input = new Float32Array(3 * MS * MS);
    for (let c = 0; c < 3; c++) {
      const ch = resizeCh(rgb[c], gw, gh, MS, MS);
      for (let i = 0; i < ch.length; i++) input[c * MS * MS + i] = ch[i] - 0.5;
    }
    const out = await session.run({ [session.inputNames[0]]: new ort.Tensor('float32', input, [1, 3, MS, MS]) });
    const pred = out[session.outputNames[0]].data;
    let lo = Infinity, hi = -Infinity;
    for (let i = 0; i < pred.length; i++) { const v = pred[i]; if (v < lo) lo = v; if (v > hi) hi = v; }
    const norm = new Float32Array(MS * MS), span = hi - lo || 1;
    for (let i = 0; i < norm.length; i++) norm[i] = (pred[i] - lo) / span;
    setBusy('Fitting edges');
    await frame();
    const raw = resizeCh(norm, MS, MS, gw, gh);
    return { gw, gh, rgb, raw, fitted: null, empty: hi - lo < 0.05 };
  }

  // Everything below runs from the cached detection, so tuning a slider is quick.
  function autoLayers() {
    const d = auData, { gw, gh } = d, n = gw * gh, long = Math.max(gw, gh);
    if (au.fit && !d.fitted) d.fitted = guidedFilter(d.rgb, d.raw, gw, gh, Math.max(2, Math.round(long / 300)), 2e-3);
    const src = au.fit ? d.fitted : d.raw;
    const c = au.cutoff / 100, wid = 0.02 + au.soft / 100 * 0.98, subj = new Float32Array(n);
    for (let i = 0; i < n; i++) subj[i] = clamp((src[i] - c) / wid + 0.5, 0, 1);
    const keepSubject = au.remove === 'background';
    const keep = keepSubject ? subj : subj.map((v) => 1 - v);
    let delta = null;
    if (au.clean) {
      const a = blurFusion(d.rgb, d.rgb, d.rgb, subj, gw, gh, Math.max(4, Math.round(long * 0.044)));
      const b = blurFusion(d.rgb, a.F, a.B, subj, gw, gh, Math.max(1, Math.round(long * 0.0015)));
      const est = keepSubject ? b.F : b.B;
      delta = est.map((ch, k) => { const o = new Float32Array(n); for (let i = 0; i < n; i++) o[i] = (ch[i] - d.rgb[k][i]) * 255; return o; });
    }
    return { keep, delta };
  }

  function applyAuto() {
    const { gw, gh } = auData, { keep, delta } = autoLayers();
    const op = new Op(au.remove === 'background' ? 'Remove background' : 'Remove subject');
    const xa = new Int32Array(W), xb = new Int32Array(W), xf = new Float32Array(W);
    for (let x = 0; x < W; x++) {
      const f = clamp((x + 0.5) * gw / W - 0.5, 0, gw - 1);
      xa[x] = Math.floor(f); xb[x] = Math.min(gw - 1, xa[x] + 1); xf[x] = f - xa[x];
    }
    const lerp2 = (m, r0, r1, x, fy) => {
      const a = m[r0 + xa[x]] + (m[r0 + xb[x]] - m[r0 + xa[x]]) * xf[x];
      const b = m[r1 + xa[x]] + (m[r1 + xb[x]] - m[r1 + xa[x]]) * xf[x];
      return a + (b - a) * fy;
    };
    for (let ti = 0; ti < tiles.length; ti++) {
      const t = tiles[ti];
      let touched = false;
      for (let y = t.y; y < t.y + t.h; y++) {
        const f = clamp((y + 0.5) * gh / H - 0.5, 0, gh - 1), y0 = Math.floor(f), fy = f - y0;
        const r0 = y0 * gw, r1 = Math.min(gh - 1, y0 + 1) * gw;
        let i = (y * W + t.x) * 4;
        for (let x = t.x; x < t.x + t.w; x++, i += 4) {
          if (!work[i + 3]) continue;
          const k = lerp2(keep, r0, r1, x, fy);
          if (k >= 0.998) continue;
          if (!touched) { op.touch(ti); touched = true; }
          if (delta && k > 0.004) {
            work[i] += lerp2(delta[0], r0, r1, x, fy);
            work[i + 1] += lerp2(delta[1], r0, r1, x, fy);
            work[i + 2] += lerp2(delta[2], r0, r1, x, fy);
          }
          work[i + 3] = work[i + 3] * k;
        }
      }
      if (touched) t.dirty = true;
    }
    req();
    return commit(op);
  }

  async function runAuto() {
    if (!W || busy) return;
    const mine = orig;
    setBusy(auModel ? 'Finding the subject' : 'Loading detection model');
    try {
      if (!auData) {
        const d = await detect();
        if (orig !== mine) return;
        auData = d;
      }
      if (auData.empty) { toast("Couldn't find a clear subject in this photo. Try the Sniper or the Eraser.", true); return; }
      setBusy('Fitting edges');
      await frame();
      lastAuto = applyAuto();
    } catch (err) {
      console.error(err);
      toast(auModel
        ? 'Detection failed on this device. Try a smaller photo, or use the Sniper.'
        : "The detection model couldn't be loaded. Check your connection and try again.", true);
      return;
    } finally {
      setBusy(null);
    }
    toast(lastAuto
      ? (au.remove === 'background' ? 'Background removed.' : 'Subject removed.') + ' Tune the edges here, or touch up with Erase and Restore.'
      : 'Nothing to remove here.');
  }

  // Re-apply the last Auto run with the current settings, replacing its history entry.
  let autoQueued = false;
  function retuneAuto() {
    if (!lastAuto || !auData || autoQueued) return;
    autoQueued = true;
    requestAnimationFrame(() => {
      autoQueued = false;
      if (!lastAuto || busy || stroke || hist.undo[hist.undo.length - 1] !== lastAuto) { lastAuto = null; return; }
      hist.undo.pop();
      hist.bytes -= lastAuto.bytes;
      swapEntry(lastAuto);
      lastAuto = applyAuto();
      syncHistory();
    });
  }
  function syncAutoBtn() {
    const b = $('#autoBtn');
    b.disabled = !W;
    b.textContent = au.remove === 'background' ? 'Remove background' : 'Remove subject';
  }

  /* ------------------------------------------------------------------ camera */

  function fitScale() {
    const pad = cw < 600 ? 16 : 40;
    return Math.max(0.001, Math.min((cw - pad * 2) / W, (ch - pad * 2) / H, 8));
  }
  function fit() {
    if (!W) return;
    const s = fitScale();
    cam.s = s; cam.x = (cw - W * s) / 2; cam.y = (ch - H * s) / 2; cam.fitted = true;
    syncZoom(); req();
  }
  function zoomTo(ns, x, y) {
    if (!W) return;
    ns = clamp(ns, Math.min(fitScale() * 0.5, 0.5), 64);
    cam.x = x - (x - cam.x) * ns / cam.s;
    cam.y = y - (y - cam.y) * ns / cam.s;
    cam.s = ns; cam.fitted = false;
    syncZoom(); req();
  }
  const zoomAt = (f, x, y) => zoomTo(cam.s * f, x, y);
  function syncZoom() {
    const p = cam.s * 100;
    $('#zoomLbl').textContent = (p >= 10 ? Math.round(p) : p.toFixed(1)) + '%';
  }
  const toImg = (x, y) => ({ x: (x - cam.x) / cam.s, y: (y - cam.y) / cam.s });

  function resize() {
    const r = wrap.getBoundingClientRect();
    const ow = cw, oh = ch;
    cw = r.width; ch = r.height; dpr = window.devicePixelRatio || 1;
    view.width = Math.max(1, Math.round(cw * dpr));
    view.height = Math.max(1, Math.round(ch * dpr));
    makeChecker();
    if (W) {
      if (cam.fitted) fit();
      else { cam.x += (cw - ow) / 2; cam.y += (ch - oh) / 2; }
    }
    req();
  }

  /* ------------------------------------------------------------------ rendering */

  let raf = 0;
  function req() { if (!raf) raf = requestAnimationFrame(render); }

  function makeChecker() {
    const q = Math.max(4, Math.round(8 * dpr)), c = document.createElement('canvas');
    c.width = c.height = q * 2;
    const x = c.getContext('2d');
    x.fillStyle = colors.checkA; x.fillRect(0, 0, q * 2, q * 2);
    x.fillStyle = colors.checkB; x.fillRect(0, 0, q, q); x.fillRect(q, q, q, q);
    checker = vctx.createPattern(c, 'repeat');
  }
  const BG = { white: '#ffffff', black: '#000000', green: '#00b140' };

  function render() {
    raf = 0;
    const c = vctx;
    c.setTransform(1, 0, 0, 1, 0, 0);
    c.clearRect(0, 0, view.width, view.height);
    if (!W) return;
    flushTiles();
    const s = cam.s * dpr, ox = cam.x * dpr, oy = cam.y * dpr, VW = view.width, VH = view.height;
    const ix0 = Math.round(ox), iy0 = Math.round(oy), ix1 = Math.round(ox + W * s), iy1 = Math.round(oy + H * s);
    const vx0 = Math.max(0, ix0), vy0 = Math.max(0, iy0), vx1 = Math.min(VW, ix1), vy1 = Math.min(VH, iy1);
    if (vx1 > vx0 && vy1 > vy0) {
      c.fillStyle = bgMode === 'checker' ? checker : BG[bgMode];
      c.fillRect(vx0, vy0, vx1 - vx0, vy1 - vy0);
    }
    // Above 100% pixels are drawn as crisp squares so single-pixel work is visible.
    c.imageSmoothingEnabled = cam.s < 1;
    c.imageSmoothingQuality = 'high';
    for (const t of tiles) {
      const dx0 = Math.round(ox + t.x * s), dx1 = Math.round(ox + (t.x + t.w) * s);
      const dy0 = Math.round(oy + t.y * s), dy1 = Math.round(oy + (t.y + t.h) * s);
      if (dx1 <= 0 || dy1 <= 0 || dx0 >= VW || dy0 >= VH || dx1 === dx0 || dy1 === dy0) continue;
      c.drawImage(t.cv, dx0, dy0, dx1 - dx0, dy1 - dy0);
    }
    drawOverlay(c);
  }

  function ring(c, x, y, r) {
    c.beginPath(); c.arc(x, y, r, 0, Math.PI * 2);
    c.lineWidth = 3 * dpr; c.strokeStyle = 'rgba(0,0,0,.55)'; c.stroke();
    c.lineWidth = 1.25 * dpr; c.strokeStyle = '#fff'; c.stroke();
  }
  function cross(c, x, y, s, gap) {
    c.beginPath();
    c.moveTo(x - s, y); c.lineTo(x - gap, y); c.moveTo(x + gap, y); c.lineTo(x + s, y);
    c.moveTo(x, y - s); c.lineTo(x, y - gap); c.moveTo(x, y + gap); c.lineTo(x, y + s);
    c.lineWidth = 3 * dpr; c.strokeStyle = 'rgba(0,0,0,.55)'; c.stroke();
    c.lineWidth = 1.25 * dpr; c.strokeStyle = '#fff'; c.stroke();
  }

  const LN = 15;
  const lcv = document.createElement('canvas');
  lcv.width = lcv.height = LN;
  const lctx = lcv.getContext('2d');
  const lid = new ImageData(LN, LN);

  // Magnified view of the pixels under the reticle, with the exact value of the center pixel.
  function drawLoupe(c, px, py, ix, iy) {
    const d = lid.data, h = (LN - 1) >> 1;
    for (let y = 0; y < LN; y++) {
      for (let x = 0; x < LN; x++) {
        const sx = ix + x - h, sy = iy + y - h, o = (y * LN + x) * 4;
        if (sx < 0 || sy < 0 || sx >= W || sy >= H) { d[o + 3] = 0; continue; }
        const i = (sy * W + sx) * 4;
        d[o] = work[i]; d[o + 1] = work[i + 1]; d[o + 2] = work[i + 2]; d[o + 3] = work[i + 3];
      }
    }
    lctx.putImageData(lid, 0, 0);
    const cell = Math.round(7 * dpr), size = cell * LN, R = size / 2, gap = 30 * dpr;
    let lx, ly;
    if (hover.touch) {
      lx = px - R; ly = py - size - 70 * dpr;
      if (ly < 8 * dpr) ly = py + 70 * dpr;
    } else {
      lx = px + gap; ly = py + gap;
      if (lx + size > view.width - 8 * dpr) lx = px - gap - size;
      if (ly + size + 30 * dpr > view.height) ly = py - gap - size;
    }
    lx = clamp(lx, 8 * dpr, Math.max(8 * dpr, view.width - size - 8 * dpr));
    c.save();
    c.beginPath(); c.arc(lx + R, ly + R, R, 0, Math.PI * 2); c.clip();
    c.fillStyle = checker; c.fillRect(lx, ly, size, size);
    c.imageSmoothingEnabled = false;
    c.drawImage(lcv, lx, ly, size, size);
    const cx = lx + cell * h, cy = ly + cell * h;
    c.lineWidth = 3 * dpr; c.strokeStyle = 'rgba(0,0,0,.6)'; c.strokeRect(cx, cy, cell, cell);
    c.lineWidth = 1.25 * dpr; c.strokeStyle = '#fff'; c.strokeRect(cx, cy, cell, cell);
    c.restore();
    c.beginPath(); c.arc(lx + R, ly + R, R, 0, Math.PI * 2);
    c.lineWidth = 2 * dpr; c.strokeStyle = colors.accent; c.stroke();

    let label = 'Outside';
    if (ix >= 0 && iy >= 0 && ix < W && iy < H) {
      const i = (iy * W + ix) * 4, a = work[i + 3];
      label = a === 0 ? 'Clear' : hex([work[i], work[i + 1], work[i + 2]]) + (a < 255 ? `  ${Math.round(a / 2.55)}%` : '');
    }
    c.font = `${12 * dpr}px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace`;
    const tw = c.measureText(label).width, pw = tw + 16 * dpr, ph = 22 * dpr;
    const tx = lx + R - pw / 2, ty = ly + size + 6 * dpr;
    c.fillStyle = 'rgba(12,12,14,.82)';
    c.fillRect(tx, ty, pw, ph);
    c.fillStyle = '#fff'; c.textBaseline = 'middle';
    c.fillText(label, tx + 8 * dpr, ty + ph / 2);
  }

  function drawOverlay(c) {
    if (!hover.on || comparing || busy) return;
    if (pansOnly() || spaceDown || (gesture && (gesture.kind === 'pan' || gesture.kind === 'pinch' || gesture.kind === 'idle'))) return;
    if (hover.touch && !gesture) return;
    const px = hover.x * dpr, py = hover.y * dpr;
    const brushy = tool !== 'sniper' || sn.mode === 'brush';
    c.save();
    if (brushy) {
      const r = brush.size / 2 * cam.s * dpr;
      ring(c, px, py, Math.max(r, 2 * dpr));
      if (tool === 'sniper' || r < 6 * dpr) cross(c, px, py, 6 * dpr, 0);
    } else {
      const r = 10 * dpr;
      c.beginPath(); c.arc(px, py, r, 0, Math.PI * 2);
      c.lineWidth = 3 * dpr; c.strokeStyle = 'rgba(0,0,0,.55)'; c.stroke();
      c.lineWidth = 1.5 * dpr; c.strokeStyle = colors.accent; c.stroke();
      cross(c, px, py, 16 * dpr, 4 * dpr);
    }
    c.restore();
    if (tool === 'sniper') {
      const ip = toImg(hover.x, hover.y);
      drawLoupe(c, px, py, Math.floor(ip.x), Math.floor(ip.y));
    }
  }

  /* ------------------------------------------------------------------ pointer input */

  const local = (e) => { const r = view.getBoundingClientRect(); return { x: e.clientX - r.left, y: e.clientY - r.top }; };
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });

  function startPinch() {
    const [a, b] = [...pointers.values()];
    return { kind: 'pinch', d: Math.max(1, dist(a, b)), c: mid(a, b), s: cam.s, x: cam.x, y: cam.y };
  }
  function updatePinch(g) {
    const [a, b] = [...pointers.values()];
    const c = mid(a, b);
    const ns = clamp(g.s * dist(a, b) / g.d, Math.min(fitScale() * 0.5, 0.5), 64);
    const ix = (g.c.x - g.x) / g.s, iy = (g.c.y - g.y) / g.s;
    cam.s = ns; cam.x = c.x - ix * ns; cam.y = c.y - iy * ns; cam.fitted = false;
    syncZoom();
  }

  view.addEventListener('pointerdown', (e) => {
    if (!W || busy) return;
    view.setPointerCapture(e.pointerId);
    const p = local(e);
    pointers.set(e.pointerId, p);
    hover.on = true; hover.x = p.x; hover.y = p.y; hover.touch = e.pointerType === 'touch';
    $('#panel').classList.remove('open');
    $('#optionsBtn').setAttribute('aria-expanded', 'false');

    if (pointers.size === 2) {
      if (gesture && gesture.kind === 'paint') cancelStroke();
      gesture = startPinch();
      syncCursor(); req();
      return;
    }
    if (pointers.size > 2) return;
    if (e.button === 1 || e.button === 2 || spaceDown || pansOnly()) {
      gesture = { kind: 'pan', last: p };
      e.preventDefault();
      syncCursor();
      return;
    }
    if (e.button !== 0 || comparing) return;
    const ip = toImg(p.x, p.y);
    if (tool === 'sniper' && sn.mode === 'click') {
      // Touch aims first: the loupe follows the finger and the shot fires on release.
      if (e.pointerType === 'touch') gesture = { kind: 'aim' };
      else { gesture = { kind: 'idle' }; sniperClick(ip); }
      req();
      return;
    }
    beginStroke(ip);
    gesture = { kind: 'paint' };
  });

  view.addEventListener('pointermove', (e) => {
    const p = local(e);
    hover.on = true; hover.x = p.x; hover.y = p.y; hover.touch = e.pointerType === 'touch';
    if (pointers.has(e.pointerId)) pointers.set(e.pointerId, p);
    if (gesture) {
      if (gesture.kind === 'pan') {
        cam.x += p.x - gesture.last.x; cam.y += p.y - gesture.last.y; cam.fitted = false;
        gesture.last = p;
      } else if (gesture.kind === 'pinch' && pointers.size >= 2) {
        updatePinch(gesture);
      } else if (gesture.kind === 'paint' && stroke) {
        const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [];
        for (const ce of evs.length ? evs : [e]) {
          const q = local(ce);
          strokeTo(toImg(q.x, q.y));
        }
      }
    }
    req();
  });

  function endPointer(e, cancelled) {
    if (!pointers.has(e.pointerId)) return;
    pointers.delete(e.pointerId);
    if (gesture) {
      if (gesture.kind === 'paint') endStroke();
      else if (gesture.kind === 'aim' && !cancelled) sniperClick(toImg(hover.x, hover.y));
      if (gesture.kind === 'pinch' && pointers.size > 0) gesture = { kind: 'idle' };
    }
    if (pointers.size === 0) gesture = null;
    if (e.pointerType === 'touch') hover.on = false;
    syncCursor(); req();
  }
  view.addEventListener('pointerup', (e) => endPointer(e, false));
  view.addEventListener('pointercancel', (e) => endPointer(e, true));
  view.addEventListener('pointerleave', () => { if (!gesture) { hover.on = false; req(); } });
  view.addEventListener('contextmenu', (e) => e.preventDefault());

  view.addEventListener('wheel', (e) => {
    if (!W) return;
    e.preventDefault();
    const p = local(e);
    let dy = e.deltaY;
    if (e.deltaMode === 1) dy *= 16;
    else if (e.deltaMode === 2) dy *= ch;
    zoomAt(Math.exp(-dy * (e.ctrlKey ? 0.01 : 0.0018)), p.x, p.y);
  }, { passive: false });

  function syncCursor() {
    let c = 'none';
    if (!W) c = 'default';
    else if (gesture && gesture.kind === 'pan') c = 'grabbing';
    else if (spaceDown || pansOnly()) c = 'grab';
    view.style.cursor = c;
  }

  /* ------------------------------------------------------------------ open */

  async function decode(file) {
    if ('createImageBitmap' in window) {
      try { return await createImageBitmap(file, { imageOrientation: 'from-image' }); } catch { /* fall back */ }
    }
    const url = URL.createObjectURL(file);
    const im = new Image();
    im.decoding = 'async';
    im.src = url;
    try { await im.decode(); } catch (err) { URL.revokeObjectURL(url); throw err; }
    im._url = url;
    return im;
  }

  function extract(src, w, h) {
    const px = new Uint8ClampedArray(w * h * 4);
    const C = 2048, cv = document.createElement('canvas');
    cv.width = Math.min(w, C); cv.height = Math.min(h, C);
    const c = cv.getContext('2d', { willReadFrequently: true });
    for (let y = 0; y < h; y += C) {
      for (let x = 0; x < w; x += C) {
        const sw = Math.min(C, w - x), sh = Math.min(C, h - y);
        c.clearRect(0, 0, cv.width, cv.height);
        c.drawImage(src, x, y, sw, sh, 0, 0, sw, sh);
        const d = c.getImageData(0, 0, sw, sh).data;
        for (let r = 0; r < sh; r++) px.set(d.subarray(r * sw * 4, (r + 1) * sw * 4), ((y + r) * w + x) * 4);
      }
    }
    cv.width = cv.height = 0;
    return px;
  }

  function confirmReplace() {
    const d = $('#confirm');
    if (typeof d.showModal !== 'function') return Promise.resolve(true);
    return new Promise((res) => {
      d.returnValue = '';
      d.addEventListener('close', () => res(d.returnValue === 'ok'), { once: true });
      d.showModal();
    });
  }

  async function openFile(file) {
    if (!file || busy) return;
    if (unsaved && hist.undo.length && !(await confirmReplace())) return;
    setBusy('Opening photo');
    await frame();
    let src;
    try {
      src = await decode(file);
    } catch {
      setBusy(null);
      toast("This file couldn't be read as an image. Try a JPG, PNG or WebP.", true);
      return;
    }
    const w = src.naturalWidth || src.width, h = src.naturalHeight || src.height;
    try {
      if (!w || !h) throw new Error('empty');
      if (w * h > MAX_PX) {
        toast(`This photo is ${(w * h / 1e6).toFixed(1)} megapixels. Pluck handles up to 60 in the browser.`, true);
        return;
      }
      const px = extract(src, w, h);
      setImage(px, w, h, file.name.replace(/\.[^.]+$/, '') || 'photo');
    } catch (err) {
      console.error(err);
      toast('This photo could not be opened. Your browser may be out of memory, try a smaller one.', true);
    } finally {
      if (src.close) src.close();
      if (src._url) URL.revokeObjectURL(src._url);
      setBusy(null);
    }
  }

  function setImage(px, w, h, name) {
    W = w; H = h; orig = px;
    work = new Uint8ClampedArray(px);
    work32 = new Uint32Array(work.buffer);
    fileBase = name;
    buildTiles();
    hist.undo = []; hist.redo = []; hist.bytes = 0;
    lastFill = null; stroke = null; unsaved = false; comparing = false;
    auData = null; lastAuto = null;
    sn.color = null;
    syncSwatch(); syncHistory();
    $('#empty').hidden = true;
    $('#floatCtl').hidden = false;
    $('#exportBtn').disabled = false;
    $('#restoreAll').disabled = false;
    syncAutoBtn();
    $('#exportInfo').textContent = `Full resolution: ${w.toLocaleString()} × ${h.toLocaleString()} px.`;
    fit(); syncCursor();
  }

  // A plain object on a flat, slightly noisy background: enough to try every tool.
  function testImage() {
    const w = 1600, h = 1200, cv = document.createElement('canvas');
    cv.width = w; cv.height = h;
    const x = cv.getContext('2d');
    x.fillStyle = '#a3d8c9'; x.fillRect(0, 0, w, h);
    x.save(); x.translate(820, 955); x.scale(1, 0.16);
    const sh = x.createRadialGradient(0, 0, 0, 0, 0, 330);
    sh.addColorStop(0, 'rgba(24,70,58,.45)'); sh.addColorStop(1, 'rgba(24,70,58,0)');
    x.fillStyle = sh; x.beginPath(); x.arc(0, 0, 330, 0, Math.PI * 2); x.fill(); x.restore();
    const g = x.createRadialGradient(700, 470, 30, 800, 600, 330);
    g.addColorStop(0, '#ffc2a0'); g.addColorStop(0.5, '#f2643a'); g.addColorStop(1, '#9c2d16');
    x.fillStyle = g; x.beginPath(); x.arc(800, 600, 320, 0, Math.PI * 2); x.fill();
    x.strokeStyle = '#5a3a22'; x.lineWidth = 18; x.lineCap = 'round';
    x.beginPath(); x.moveTo(800, 300); x.quadraticCurveTo(805, 250, 830, 205); x.stroke();
    x.save(); x.translate(905, 250); x.rotate(-0.5);
    x.fillStyle = '#2f6b3a'; x.beginPath(); x.ellipse(0, 0, 95, 38, 0, 0, Math.PI * 2); x.fill();
    x.strokeStyle = '#4d8c55'; x.lineWidth = 4; x.beginPath(); x.moveTo(-85, 0); x.lineTo(85, 0); x.stroke();
    x.restore();
    const id = x.getImageData(0, 0, w, h), d = id.data;
    for (let i = 0; i < d.length; i += 4) {
      const n = (Math.random() - 0.5) * 7;
      d[i] += n; d[i + 1] += n; d[i + 2] += n;
    }
    cv.width = cv.height = 0;
    return id;
  }

  /* ------------------------------------------------------------------ PNG export */

  // Encoded straight from the RGBA buffer: no canvas round trip, so semi-transparent pixels
  // keep their exact color and there is no browser canvas size limit.
  const CRC = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    CRC[n] = c;
  }
  function crc32(...parts) {
    let c = -1;
    for (const p of parts) for (let i = 0; i < p.length; i++) c = CRC[(c ^ p[i]) & 255] ^ (c >>> 8);
    return ~c >>> 0;
  }
  const be32 = (n) => new Uint8Array([n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
  function pngChunk(type, data) {
    const t = new Uint8Array([...type].map((ch) => ch.charCodeAt(0)));
    return [be32(data.length), t, data, be32(crc32(t, data))];
  }

  async function encodePNG(src, SW, r, onProg) {
    const w = r.w, h = r.h, bpr = w * 4;
    const cs = new CompressionStream('deflate'), wr = cs.writable.getWriter();
    const zP = new Response(cs.readable).arrayBuffer();
    let prev = new Uint8Array(bpr), cur = new Uint8Array(bpr);
    const F1 = new Uint8Array(bpr), F2 = new Uint8Array(bpr), F4 = new Uint8Array(bpr);
    const per = Math.max(1, Math.floor(4194304 / (bpr + 1)));
    const buf = new Uint8Array(per * (bpr + 1));
    let o = 0, t0 = performance.now();
    for (let y = 0; y < h; y++) {
      const a = ((r.y + y) * SW + r.x) * 4;
      cur.set(src.subarray(a, a + bpr));
      // Fully transparent pixels carry no color; zeroing them compresses far better.
      for (let i = 3; i < bpr; i += 4) if (cur[i] === 0) cur[i - 3] = cur[i - 2] = cur[i - 1] = 0;
      let s0 = 0, s1 = 0, s2 = 0, s4 = 0;
      for (let i = 0; i < bpr; i++) {
        const x = cur[i], up = prev[i], left = i >= 4 ? cur[i - 4] : 0, ul = i >= 4 ? prev[i - 4] : 0;
        s0 += x < 128 ? x : 256 - x;
        let v = (x - left) & 255; F1[i] = v; s1 += v < 128 ? v : 256 - v;
        v = (x - up) & 255; F2[i] = v; s2 += v < 128 ? v : 256 - v;
        const p = left + up - ul, pa = Math.abs(p - left), pb = Math.abs(p - up), pc = Math.abs(p - ul);
        v = (x - (pa <= pb && pa <= pc ? left : pb <= pc ? up : ul)) & 255; F4[i] = v; s4 += v < 128 ? v : 256 - v;
      }
      let ft = 0, best = s0;
      if (s1 < best) { best = s1; ft = 1; }
      if (s2 < best) { best = s2; ft = 2; }
      if (s4 < best) ft = 4;
      buf[o++] = ft;
      buf.set(ft === 1 ? F1 : ft === 2 ? F2 : ft === 4 ? F4 : cur, o);
      o += bpr;
      const t = prev; prev = cur; cur = t;
      if (o === buf.length || y === h - 1) {
        await wr.write(buf.slice(0, o));
        o = 0;
        if (performance.now() - t0 > 120) { onProg(y / h); await yieldUI(); t0 = performance.now(); }
      }
    }
    await wr.close();
    const z = new Uint8Array(await zP);
    const ihdr = new Uint8Array(13), dv = new DataView(ihdr.buffer);
    dv.setUint32(0, w); dv.setUint32(4, h);
    ihdr[8] = 8; ihdr[9] = 6;
    return new Blob([
      new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]),
      ...pngChunk('IHDR', ihdr),
      ...pngChunk('sRGB', new Uint8Array([0])),
      ...pngChunk('IDAT', z),
      ...pngChunk('IEND', new Uint8Array(0)),
    ], { type: 'image/png' });
  }

  function canvasPNG(r) {
    return new Promise((res, rej) => {
      const c = document.createElement('canvas');
      c.width = r.w; c.height = r.h;
      const x = c.getContext('2d');
      for (let y = 0; y < r.h; y += 256) {
        const hh = Math.min(256, r.h - y), id = new ImageData(r.w, hh);
        for (let k = 0; k < hh; k++) {
          const a = ((r.y + y + k) * W + r.x) * 4;
          id.data.set(work.subarray(a, a + r.w * 4), k * r.w * 4);
        }
        x.putImageData(id, 0, y);
      }
      c.toBlob((b) => (b ? res(b) : rej(new Error('toBlob failed'))), 'image/png');
    });
  }

  function alphaBounds() {
    let x0 = W, y0 = -1, x1 = -1, y1 = -1;
    for (let y = 0; y < H; y++) {
      const row = y * W * 4;
      let first = -1, last = -1;
      for (let x = 0; x < W; x++) if (work[row + x * 4 + 3]) { first = x; break; }
      if (first < 0) continue;
      for (let x = W - 1; x >= first; x--) if (work[row + x * 4 + 3]) { last = x; break; }
      if (y0 < 0) y0 = y;
      y1 = y;
      if (first < x0) x0 = first;
      if (last > x1) x1 = last;
    }
    return y0 < 0 ? null : { x: x0, y: y0, w: x1 - x0 + 1, h: y1 - y0 + 1 };
  }

  async function doExport() {
    if (!W || busy || stroke) return;
    const r = $('#trim').checked ? alphaBounds() : { x: 0, y: 0, w: W, h: H };
    if (!r) { toast('Everything is erased. Restore something before downloading.', true); return; }
    setBusy('Preparing PNG');
    await frame();
    try {
      const blob = typeof CompressionStream === 'function'
        ? await encodePNG(work, W, r, (p) => { $('#busyText').textContent = `Preparing PNG ${Math.round(p * 100)}%`; })
        : await canvasPNG(r);
      const url = URL.createObjectURL(blob), a = document.createElement('a');
      a.href = url; a.download = `${fileBase}-pluck.png`;
      document.body.append(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 60000);
      unsaved = false;
      toast(`Downloaded ${r.w.toLocaleString()} × ${r.h.toLocaleString()} PNG (${(blob.size / 1048576).toFixed(1)} MB)`);
    } catch (err) {
      console.error(err);
      toast("The PNG couldn't be created. Your browser may be out of memory.", true);
    } finally {
      setBusy(null);
    }
  }

  /* ------------------------------------------------------------------ UI */

  function setBusy(text) {
    busy = !!text;
    $('#busy').hidden = !text;
    if (text) $('#busyText').textContent = text;
    document.body.classList.toggle('is-busy', busy);
    req();
  }

  let toastT = 0;
  function toast(msg, err) {
    const t = $('#toast');
    t.textContent = msg;
    t.classList.toggle('err', !!err);
    t.classList.add('show');
    clearTimeout(toastT);
    toastT = setTimeout(() => t.classList.remove('show'), err ? 5200 : 2800);
  }

  const TOOLS = {
    erase: ['Eraser', 'Paint over anything to remove it.'],
    restore: ['Restore', 'Paint to bring the original pixels back.'],
    sniper: ['Sniper', ''],
    auto: ['Auto', 'Finds the subject for you and removes the background, or the subject itself, with edges fitted to your photo.'],
    hand: ['Move', 'Drag to move around. Scroll or pinch to zoom.'],
  };
  function setTool(t) {
    if (stroke) return;
    tool = t;
    $$('.tool[data-tool]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.tool === t)));
    refreshPanel(); syncCursor(); req();
  }
  function refreshPanel() {
    const keys = [tool, `${tool}-${sn.mode}`];
    $$('#panel [data-show]').forEach((s) => { s.hidden = !s.dataset.show.split(' ').some((k) => keys.includes(k)); });
    $$('#panel [data-mode]').forEach((s) => { s.hidden = s.dataset.mode !== sn.mode; });
    $('#toolName').textContent = TOOLS[tool][0];
    $('#toolHint').textContent = tool === 'sniper'
      ? (sn.mode === 'click'
        ? 'Click a color. Matching pixels disappear and the edges are cleaned of its tint.'
        : 'Brush along an edge. Only the sampled color is erased, everything else stays.')
      : TOOLS[tool][1];
  }
  function syncSwatch() {
    const sw = $('#swatch'), c = sn.color;
    sw.style.background = c ? hex(c) : '';
    $('#swatchHex').textContent = c ? hex(c) : 'Click the photo to pick one';
    $('#swatchHex').title = c ? `rgb(${c.join(', ')})` : '';
    $('#eraseColorBtn').disabled = !c || !W;
    if (c) $('#pickColor').value = hex(c);
  }

  // Size uses a log scale so 1 px and 1000 px are both reachable with fine control.
  const sizeFromSlider = (v) => Math.max(1, Math.round(Math.exp(v / 1000 * Math.log(1000))));
  const sliderFromSize = (s) => Math.round(Math.log(s) / Math.log(1000) * 1000);
  const ranges = {};
  function bindRange(id, get, set, fmt, toSlider = (v) => v, fromSlider = (v) => v) {
    const el = $('#' + id), out = $('#' + id + 'Out');
    const paint = () => {
      el.style.setProperty('--p', ((el.value - el.min) / (el.max - el.min) * 100) + '%');
      out.textContent = fmt(get());
    };
    const sync = () => { el.value = toSlider(get()); paint(); };
    el.addEventListener('input', () => { set(fromSlider(+el.value)); paint(); });
    ranges[id] = { sync };
    sync();
  }
  bindRange('size', () => brush.size, (v) => { brush.size = v; req(); }, (v) => `${v} px`, sliderFromSize, sizeFromSlider);
  bindRange('hard', () => brush.hardness, (v) => { brush.hardness = v; }, (v) => `${v}%`);
  bindRange('str', () => brush.strength, (v) => { brush.strength = v; }, (v) => `${v}%`);
  bindRange('tol', () => sn.tol, (v) => { sn.tol = v; retune(); }, (v) => (v === 0 ? 'Exact color' : String(v)));
  bindRange('soft', () => sn.soft, (v) => { sn.soft = v; retune(); }, (v) => (v === 0 ? 'Hard' : String(v)));

  function setSize(v) { brush.size = clamp(Math.round(v), 1, 1000); ranges.size.sync(); req(); }

  const bindRadios = (name, fn) => $$(`input[name="${name}"]`).forEach((r) => r.addEventListener('change', () => r.checked && fn(r.value)));
  const setRadio = (name, v) => { const r = $(`input[name="${name}"][value="${v}"]`); if (r) r.checked = true; };
  bindRadios('snmode', (v) => { sn.mode = v; refreshPanel(); req(); });
  bindRadios('reach', (v) => { sn.reach = v; retune(); });
  bindRadios('sample', (v) => { sn.sample = +v; });
  bindRadios('sampling', (v) => { sn.sampling = v; });
  bindRadios('bg', (v) => { bgMode = v; req(); });
  bindRadios('theme', (v) => applyTheme(v));
  $('#clean').addEventListener('change', (e) => { sn.clean = e.target.checked; retune(); });

  $('#pickColor').addEventListener('input', (e) => {
    const v = e.target.value;
    sn.color = [1, 3, 5].map((i) => parseInt(v.slice(i, i + 2), 16));
    syncSwatch();
  });
  $('#eraseColorBtn').addEventListener('click', () => { if (W && sn.color) fire(null, null, sn.color, 'global'); });
  $('#restoreAll').addEventListener('click', restoreAll);
  bindRange('cut', () => au.cutoff, (v) => { au.cutoff = v; retuneAuto(); }, (v) => String(v));
  bindRange('auSoft', () => au.soft, (v) => { au.soft = v; retuneAuto(); }, (v) => (v === 0 ? 'Hard' : String(v)));
  bindRadios('auremove', (v) => { au.remove = v; syncAutoBtn(); retuneAuto(); });
  $('#auFit').addEventListener('change', (e) => { au.fit = e.target.checked; retuneAuto(); });
  $('#auClean').addEventListener('change', (e) => { au.clean = e.target.checked; retuneAuto(); });
  $('#autoBtn').addEventListener('click', runAuto);

  $$('.tool[data-tool]').forEach((b) => b.addEventListener('click', () => {
    const panel = $('#panel');
    if (tool === b.dataset.tool && matchMedia('(max-width: 760px)').matches) {
      const open = panel.classList.toggle('open');
      $('#optionsBtn').setAttribute('aria-expanded', String(open));
    }
    setTool(b.dataset.tool);
  }));
  $('#optionsBtn').addEventListener('click', () => {
    const open = $('#panel').classList.toggle('open');
    $('#optionsBtn').setAttribute('aria-expanded', String(open));
  });

  $('#undoBtn').addEventListener('click', undo);
  $('#redoBtn').addEventListener('click', redo);
  const fileInput = $('#fileInput');
  const pickFile = () => { if (!busy) fileInput.click(); };
  $('#openBtn').addEventListener('click', pickFile);
  $('#emptyOpen').addEventListener('click', pickFile);
  fileInput.addEventListener('change', () => { const f = fileInput.files[0]; fileInput.value = ''; openFile(f); });
  $('#sampleBtn').addEventListener('click', () => {
    const id = testImage();
    setImage(id.data, id.width, id.height, 'test-image');
    if (tool !== 'sniper') setTool('sniper');
    toast('Try clicking the green background with the Sniper.');
  });
  $('#exportBtn').addEventListener('click', doExport);
  $('#zoomIn').addEventListener('click', () => zoomAt(1.25, cw / 2, ch / 2));
  $('#zoomOut').addEventListener('click', () => zoomAt(0.8, cw / 2, ch / 2));
  $('#zoomLbl').addEventListener('click', () => (Math.abs(cam.s - 1) < 1e-3 ? fit() : zoomTo(1, cw / 2, ch / 2)));

  function setCompare(on) {
    if (!W || on === comparing || (on && stroke)) return;
    comparing = on;
    $('#compareBtn').setAttribute('aria-pressed', String(on));
    markAll();
  }
  const cmp = $('#compareBtn');
  cmp.addEventListener('pointerdown', (e) => { if (e.button === 0) { cmp.setPointerCapture(e.pointerId); setCompare(true); } });
  ['pointerup', 'pointercancel', 'lostpointercapture'].forEach((ev) => cmp.addEventListener(ev, () => setCompare(false)));
  cmp.addEventListener('click', (e) => { if (e.detail === 0) setCompare(!comparing); });
  cmp.addEventListener('contextmenu', (e) => e.preventDefault());

  /* theme */
  function applyTheme(t) {
    document.documentElement.dataset.theme = t;
    store.set('pluck.theme', t);
    setRadio('theme', t);
    readColors();
  }
  function readColors() {
    const cs = getComputedStyle(document.documentElement);
    colors.accent = cs.getPropertyValue('--accent').trim() || colors.accent;
    colors.checkA = cs.getPropertyValue('--check-a').trim() || colors.checkA;
    colors.checkB = cs.getPropertyValue('--check-b').trim() || colors.checkB;
    makeChecker(); req();
  }
  setRadio('theme', document.documentElement.dataset.theme || 'dark');

  /* keyboard */
  addEventListener('keydown', (e) => {
    if (!$('#guide').hidden) { guideKey(e); return; }
    if ($('#confirm').open) return;
    const t = e.target;
    const typing = (t.tagName === 'INPUT' && !['range', 'checkbox', 'radio', 'color'].includes(t.type)) || t.tagName === 'TEXTAREA';
    const mod = e.ctrlKey || e.metaKey, k = e.key.toLowerCase();
    if (mod && !typing) {
      if (k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); }
      else if (k === 'y') { e.preventDefault(); redo(); }
      else if (k === 'o') { e.preventDefault(); pickFile(); }
      else if (k === 's') { e.preventDefault(); doExport(); }
      return;
    }
    if (typing || mod || e.altKey) return;
    if (e.key === ' ') {
      if (t.tagName === 'BUTTON' || (t.tagName === 'INPUT' && t.type !== 'range')) return;
      e.preventDefault();
      if (!spaceDown) { spaceDown = true; syncCursor(); req(); }
      return;
    }
    const inRange = t.tagName === 'INPUT' && t.type === 'range';
    switch (k) {
      case 'e': setTool('erase'); break;
      case 'r': setTool('restore'); break;
      case 's': setTool('sniper'); break;
      case 'a': setTool('auto'); break;
      case 'h': setTool('hand'); break;
      case '[': setSize(brush.size / 1.15); break;
      case ']': setSize(Math.max(brush.size + 1, brush.size * 1.15)); break;
      case '0': if (!inRange) fit(); break;
      case '1': if (!inRange) zoomTo(1, cw / 2, ch / 2); break;
      case '=': case '+': zoomAt(1.25, cw / 2, ch / 2); break;
      case '-': zoomAt(0.8, cw / 2, ch / 2); break;
      case '\\': setCompare(true); break;
      default: return;
    }
  });
  addEventListener('keyup', (e) => {
    if (e.key === ' ' && spaceDown) { spaceDown = false; syncCursor(); req(); }
    if (e.key === '\\') setCompare(false);
  });
  addEventListener('blur', () => { spaceDown = false; setCompare(false); syncCursor(); });

  /* drop and paste */
  const hasFiles = (e) => Array.from((e.dataTransfer && e.dataTransfer.types) || []).includes('Files');
  let dragDepth = 0;
  addEventListener('dragenter', (e) => { if (hasFiles(e)) { e.preventDefault(); dragDepth++; wrap.classList.add('dragging'); } });
  addEventListener('dragover', (e) => { if (hasFiles(e)) e.preventDefault(); });
  addEventListener('dragleave', (e) => { if (hasFiles(e) && --dragDepth <= 0) { dragDepth = 0; wrap.classList.remove('dragging'); } });
  addEventListener('drop', (e) => {
    if (!hasFiles(e)) return;
    e.preventDefault();
    dragDepth = 0; wrap.classList.remove('dragging');
    const files = Array.from(e.dataTransfer.files);
    openFile(files.find((f) => f.type.startsWith('image/')) || files[0]);
  });
  addEventListener('paste', (e) => {
    const item = Array.from((e.clipboardData && e.clipboardData.items) || []).find((i) => i.type.startsWith('image/'));
    if (!item) return;
    e.preventDefault();
    const f = item.getAsFile();
    if (f) openFile(new File([f], 'pasted-image', { type: f.type }));
  });

  addEventListener('beforeunload', (e) => {
    if (unsaved && hist.undo.length) { e.preventDefault(); e.returnValue = ''; }
  });

  /* ------------------------------------------------------------------ first-run guide */

  const STEPS = [
    { el: '#openBtn', t: 'Start with any photo', b: 'Open one here, drop it anywhere on the page, or paste it. It stays on your device the whole time.' },
    { el: '#toolErase', t: 'Erase by hand', b: 'Paint over whatever you want gone. Change the brush size with [ and ].' },
    { el: '#toolRestore', t: 'Restore is the opposite', b: 'Paint over an area to bring the original pixels back. Nothing you erase is ever lost.' },
    { el: '#toolAuto', t: 'Auto finds the subject', b: 'One click removes the background, or the subject if that is what has to go. The outline is fitted to real edges in your photo, and every slider after that tunes the result live.' },
    { el: '#toolSniper', t: 'Sniper takes out one color', b: 'Click a color and every connected pixel of it disappears. Tolerance sets how close a shade must be, and edge pixels are cleaned of that color so hair and soft edges look natural.' },
    { el: '#panel', t: 'Settings for each tool', b: 'Size, hardness, tolerance and the rest live here. After a Sniper click, moving a slider re-runs that click so you can tune it live.' },
    { el: '#optionsBtn', t: 'Settings for each tool', b: 'Tap here for size, hardness and tolerance. After a Sniper tap, moving a slider re-runs it so you can tune it live. Use two fingers to move and zoom.' },
    { el: '#undoBtn', t: 'Undo and redo', b: 'Step back or forward any time. Ctrl+Z and Ctrl+Shift+Z work too.' },
    { el: '#compareBtn', t: 'Check your work', b: 'Press and hold to see the original photo.' },
    { el: '#exportBtn', t: 'Download at full size', b: 'You get a transparent PNG at the exact resolution of your photo. No account, no watermark, no limits.' },
  ];
  let gi = 0, guideReturn = null;
  const visible = (el) => el && el.getClientRects().length > 0 && el.getBoundingClientRect().width > 0;
  const shownSteps = () => STEPS.filter((s) => visible($(s.el)));

  function startGuide(tries = 0) {
    if (!shownSteps().length) {
      if (tries < 20) setTimeout(() => startGuide(tries + 1), 150);
      return;
    }
    guideReturn = document.activeElement;
    gi = 0;
    $('#guide').hidden = false;
    showStep();
  }
  function endGuide() {
    $('#guide').hidden = true;
    store.set('pluck.guided', '1');
    if (guideReturn && guideReturn.focus) guideReturn.focus();
  }
  function showStep() {
    const list = shownSteps();
    if (!list.length) { endGuide(); return; }
    gi = clamp(gi, 0, list.length - 1);
    const st = list[gi], r = $(st.el).getBoundingClientRect();
    const pad = 6, spot = $('#spot'), pop = $('#pop');
    spot.style.left = `${r.left - pad}px`; spot.style.top = `${r.top - pad}px`;
    spot.style.width = `${r.width + pad * 2}px`; spot.style.height = `${r.height + pad * 2}px`;
    $('#gStep').textContent = `${gi + 1} of ${list.length}`;
    $('#gTitle').textContent = st.t;
    $('#gBody').textContent = st.b;
    $('#gBack').disabled = gi === 0;
    $('#gNext').textContent = gi === list.length - 1 ? 'Start editing' : 'Next';
    const pw = pop.offsetWidth, ph = pop.offsetHeight, vw = innerWidth, vh = innerHeight, m = 16;
    let left, top;
    if (r.right + pad + 14 + pw < vw - m && r.height > vh * 0.5) {
      left = r.right + pad + 14; top = clamp(r.top, m, vh - ph - m);
    } else if (r.left - pad - 14 - pw > m && r.height > vh * 0.5) {
      left = r.left - pad - 14 - pw; top = clamp(r.top, m, vh - ph - m);
    } else {
      left = clamp(r.left + r.width / 2 - pw / 2, m, vw - pw - m);
      top = r.bottom + pad + 14 + ph < vh - m ? r.bottom + pad + 14 : r.top - pad - 14 - ph;
      if (r.right + pad + 14 + pw < vw - m && top < m) { left = r.right + pad + 14; top = clamp(r.top, m, vh - ph - m); }
      top = clamp(top, m, vh - ph - m);
    }
    pop.style.left = `${left}px`; pop.style.top = `${top}px`;
    $('#gNext').focus();
  }
  function guideKey(e) {
    if (e.key === 'Escape') { e.preventDefault(); endGuide(); }
    else if (e.key === 'ArrowRight') { e.preventDefault(); $('#gNext').click(); }
    else if (e.key === 'ArrowLeft') { e.preventDefault(); if (gi > 0) { gi--; showStep(); } }
    else if (e.key === 'Tab') {
      const f = ['#gSkip', '#gBack', '#gNext'].map($).filter((b) => !b.disabled);
      const i = f.indexOf(document.activeElement);
      e.preventDefault();
      f[(i + (e.shiftKey ? -1 : 1) + f.length) % f.length].focus();
    }
  }
  $('#gNext').addEventListener('click', () => { if (gi >= shownSteps().length - 1) endGuide(); else { gi++; showStep(); } });
  $('#gBack').addEventListener('click', () => { if (gi > 0) { gi--; showStep(); } });
  $('#gSkip').addEventListener('click', endGuide);
  $('#helpBtn').addEventListener('click', () => startGuide());
  addEventListener('resize', () => { if (!$('#guide').hidden) showStep(); });

  /* ------------------------------------------------------------------ init */

  new ResizeObserver(resize).observe(wrap);
  resize();
  readColors();
  refreshPanel();
  syncHistory();
  syncCursor();
  if (!store.get('pluck.guided')) {
    const go = () => setTimeout(() => startGuide(), 60);
    if (document.readyState === 'complete') go(); else addEventListener('load', go, { once: true });
  }
})();
