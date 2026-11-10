'use strict';
/* =========================================================
   Module 10 — ANOVA Lab
   Plain JavaScript, no dependencies.
   ========================================================= */

/* =========================================================
   Maths
   ========================================================= */
function erf(x) {
  const s = x < 0 ? -1 : 1; x = Math.abs(x);
  const t = 1 / (1 + 0.3275911 * x);
  const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
  return s * y;
}
const Phi = z => 0.5 * (1 + erf(z / Math.SQRT2));
const phi = z => Math.exp(-0.5 * z * z) / Math.sqrt(2 * Math.PI);

function lgamma(x) {
  const c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
  let y = x, t = x + 5.5;
  t -= (x + 0.5) * Math.log(t);
  let s = 1.000000000190015;
  for (let j = 0; j < 6; j++) s += c[j] / ++y;
  return -t + Math.log(2.5066282746310005 * s / x);
}
function betacf(a, b, x) {
  const FPMIN = 1e-300, EPS = 3e-13;
  const qab = a + b, qap = a + 1, qam = a - 1;
  let c = 1, d = 1 - qab * x / qap;
  if (Math.abs(d) < FPMIN) d = FPMIN;
  d = 1 / d;
  let h = d;
  for (let m = 1; m <= 400; m++) {
    const m2 = 2 * m;
    let aa = m * (b - m) * x / ((qam + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
    c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
    d = 1 / d; h *= d * c;
    aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2));
    d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
    c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
    d = 1 / d;
    const del = d * c; h *= del;
    if (Math.abs(del - 1) < EPS) break;
  }
  return h;
}
// Regularised incomplete beta function I_x(a, b)
function ibeta(a, b, x) {
  if (x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? bt * betacf(a, b, x) / a : 1 - bt * betacf(b, a, 1 - x) / b;
}

// F distribution
const fcdf = (F, d1, d2) => (F <= 0 ? 0 : ibeta(d1 / 2, d2 / 2, d1 * F / (d1 * F + d2)));
const fsf = (F, d1, d2) => (F <= 0 ? 1 : ibeta(d2 / 2, d1 / 2, d2 / (d1 * F + d2)));   // upper tail = p-value
function fpdf(x, d1, d2) {
  if (x <= 0) return 0;
  const ln = 0.5 * (d1 * Math.log(d1 * x) + d2 * Math.log(d2) - (d1 + d2) * Math.log(d1 * x + d2))
    - Math.log(x) - (lgamma(d1 / 2) + lgamma(d2 / 2) - lgamma((d1 + d2) / 2));
  return Math.exp(ln);
}
const memo = {};
function bisect(fn, lo, hi, n = 70) {
  for (let i = 0; i < n; i++) { const mid = (lo + hi) / 2; if (fn(mid)) hi = mid; else lo = mid; }
  return (lo + hi) / 2;
}
function fcrit(alpha, d1, d2) {
  const key = `f${alpha}|${d1}|${d2}`;
  if (memo[key] == null) {
    let hi = 4;
    while (fsf(hi, d1, d2) > alpha && hi < 1e7) hi *= 2;
    memo[key] = bisect(x => fsf(x, d1, d2) <= alpha, 0, hi);
  }
  return memo[key];
}

// Student t (two-sided critical value), used in the false-alarm simulation
const tsf2 = (t, v) => ibeta(v / 2, 0.5, v / (v + t * t));          // P(|T| > t)
function tcrit2(alpha, v) {
  const key = `t${alpha}|${v}`;
  if (memo[key] == null) memo[key] = bisect(x => tsf2(x, v) <= alpha, 0, 1000);
  return memo[key];
}

// Studentized range distribution (for Tukey HSD)
function prange(w, k) {                       // P(range of k standard normals <= w)
  if (w <= 0) return 0;
  const n = 160, a = -8, b = 8, h = (b - a) / n;
  let s = 0;
  for (let i = 0; i <= n; i++) {
    const z = a + i * h;
    const wt = i === 0 || i === n ? 1 : i % 2 ? 4 : 2;
    s += wt * phi(z) * Math.pow(Phi(z) - Phi(z - w), k - 1);
  }
  return Math.min(1, k * s * h / 3);
}
function ptukey(q, k, df) {
  if (q <= 0) return 0;
  const lnC = Math.log(2) + (df / 2) * Math.log(df / 2) - lgamma(df / 2);
  const dens = s => (s <= 0 ? 0 : Math.exp(lnC + (df - 1) * Math.log(s) - df * s * s / 2));
  const lo = Math.max(0, 1 - 7 / Math.sqrt(2 * df)), hi = 1 + 8 / Math.sqrt(2 * df);
  const n = 200, h = (hi - lo) / n;
  let tot = 0;
  for (let i = 0; i <= n; i++) {
    const s = lo + i * h;
    const wt = i === 0 || i === n ? 1 : i % 2 ? 4 : 2;
    const d = dens(s);
    if (d > 1e-14) tot += wt * d * prange(q * s, k);
  }
  return Math.min(1, tot * h / 3);
}
function qtukey(alpha, k, df) {               // upper-alpha critical value
  const key = `q${alpha}|${k}|${df}`;
  if (memo[key] == null) memo[key] = bisect(x => ptukey(x, k, df) >= 1 - alpha, 0, 60, 36);
  return memo[key];
}

// Random numbers
function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
function randn(r = Math.random) {
  let u = 0;
  while (u === 0) u = r();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * r());
}

// Descriptive helpers and one-way ANOVA
const sum = a => a.reduce((s, v) => s + v, 0);
const mean = a => sum(a) / a.length;
const ssq = (a, m = mean(a)) => sum(a.map(v => (v - m) ** 2));
function anova(groups) {
  const k = groups.length, ns = groups.map(g => g.length), N = sum(ns);
  const means = groups.map(mean), grand = sum(groups.map(sum)) / N;
  const parts = means.map((m, i) => ns[i] * (m - grand) ** 2);
  const within = groups.map((g, i) => ssq(g, means[i]));
  const ssb = sum(parts), ssw = sum(within), sst = ssb + ssw;
  const dfb = k - 1, dfw = N - k, msb = ssb / dfb, msw = ssw / dfw;
  const F = msb / msw;
  return {
    k, ns, N, means, grand, parts, within, ssb, ssw, sst, dfb, dfw, msb, msw, F,
    p: isFinite(F) ? fsf(F, dfb, dfw) : 0,
    eta: sst > 0 ? ssb / sst : 0,
    sds: groups.map((g, i) => (ns[i] > 1 ? Math.sqrt(within[i] / (ns[i] - 1)) : 0)),
  };
}

/* @@DOM@@ ================================================
   Formatting & DOM helpers
   ========================================================= */
const minus = s => String(s).replace(/-/g, '−');
const f = (v, d = 2) => minus((Math.abs(v) < 0.5 * 10 ** -d ? 0 : v).toFixed(d));
const fs = (v, d = 2) => (v > 0 ? '+' : '') + f(v, d);
const fp = p => (p < 0.0001 ? '< 0.0001' : p.toFixed(4));
const fn = (v, d = 4) => minus(String(Number(v.toFixed(d))));
const pct = (v, d = 1) => `${(v * 100).toFixed(d)}%`;
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const num = s => parseFloat(String(s).trim().replace(',', '.').replace('−', '-'));
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

/* =========================================================
   Persistence & score
   ========================================================= */
const KEY = 'm10-anova-lab-v1';
let store = {};
try { store = JSON.parse(localStorage.getItem(KEY)) || {}; } catch (e) { store = {}; }
store.quiz = store.quiz || {};
store.visited = store.visited || [];
function save() { try { localStorage.setItem(KEY, JSON.stringify(store)); } catch (e) { /* storage unavailable */ } }

const Score = {
  parts: {},
  set(id, now, max) {
    this.parts[id] = [now, max];
    let a = 0, b = 0;
    Object.values(this.parts).forEach(([x, y]) => { a += x; b += y; });
    $('#scoreNow').textContent = a;
    $('#scoreMax').textContent = b;
  },
};

/* =========================================================
   SVG plotting
   ========================================================= */
// Plots are drawn in a narrower coordinate box on phones so labels stay readable
const isNarrow = svg => (svg.clientWidth || (svg.parentNode && svg.parentNode.clientWidth) || 640) < 430;
const RENDERS = [];
class Plot {
  constructor(svg, o) {
    Object.assign(this, { w: isNarrow(svg) ? 400 : 640, h: 250, padT: 24, padB: 46, padL: 14, padR: 14, xmin: 0, xmax: 1, ymin: 0, ymax: 1 }, o);
    this.svg = svg;
    this.parts = [];
  }
  X(v) { return this.padL + (v - this.xmin) / (this.xmax - this.xmin) * (this.w - this.padL - this.padR); }
  Y(v) { return this.h - this.padB - (v - this.ymin) / (this.ymax - this.ymin) * (this.h - this.padB - this.padT); }
  get base() { return this.Y(this.ymin); }
  add(s) { this.parts.push(s); return this; }
  pts(fn, a, b, n = 160) {
    const out = [];
    for (let i = 0; i <= n; i++) {
      const x = a + (b - a) * i / n;
      out.push(`${this.X(x).toFixed(1)},${this.Y(Math.min(fn(x), this.ymax)).toFixed(1)}`);
    }
    return out;
  }
  curve(fn, cls = 'curve', a = this.xmin, b = this.xmax) {
    return this.add(`<path class="${cls}" d="M${this.pts(fn, a, b, 240).join('L')}"/>`);
  }
  area(fn, a, b, cls) {
    a = Math.max(a, this.xmin); b = Math.min(b, this.xmax);
    if (b <= a) return this;
    return this.add(`<path class="${cls}" d="M${this.X(a).toFixed(1)},${this.base}L${this.pts(fn, a, b, 90).join('L')}L${this.X(b).toFixed(1)},${this.base}Z"/>`);
  }
  vline(v, cls, top = this.padT) {
    const x = this.X(v).toFixed(1);
    return this.add(`<line class="${cls}" x1="${x}" x2="${x}" y1="${this.base}" y2="${top}"/>`);
  }
  hline(v, cls) {
    const y = this.Y(v).toFixed(1);
    return this.add(`<line class="${cls}" x1="${this.padL}" x2="${this.w - this.padR}" y1="${y}" y2="${y}"/>`);
  }
  text(v, y, str, cls = '', anchor = 'middle') {
    return this.add(`<text class="${cls}" x="${this.X(v).toFixed(1)}" y="${y}" text-anchor="${anchor}">${str}</text>`);
  }
  xaxis(ticks, fmt = v => minus(v)) {
    this.add(`<line class="axis" x1="${this.padL}" x2="${this.w - this.padR}" y1="${this.base}" y2="${this.base}"/>`);
    ticks.forEach(t => {
      const x = this.X(t).toFixed(1);
      this.add(`<line class="tick" x1="${x}" x2="${x}" y1="${this.base}" y2="${this.base + 5}"/>`);
      this.add(`<text x="${x}" y="${this.base + 18}" text-anchor="middle">${fmt(t)}</text>`);
    });
    return this;
  }
  yaxis(ticks, fmt = v => minus(v)) {
    ticks.forEach(t => {
      const y = this.Y(t).toFixed(1);
      this.add(`<line class="grid" x1="${this.padL}" x2="${this.w - this.padR}" y1="${y}" y2="${y}"/>`);
      this.add(`<text x="${this.padL - 6}" y="${+y + 4}" text-anchor="end">${fmt(t)}</text>`);
    });
    return this;
  }
  render() {
    this.svg.setAttribute('viewBox', `0 0 ${this.w} ${this.h}`);
    this.svg.innerHTML = this.parts.join('');
  }
}

function niceTicks(a, b, max = 8) {
  const steps = [0.1, 0.2, 0.5, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000];
  const step = steps.find(s => (b - a) / s <= max) || 2000;
  const out = [];
  for (let t = Math.ceil(a / step - 1e-9) * step; t <= b + 1e-9; t += step) out.push(Number(t.toFixed(4)));
  return out;
}

// Horizontal dot plot, one row per group
function drawDots(svg, groups, o) {
  o = Object.assign({ w: isNarrow(svg) ? 400 : 640, rowH: 56, padT: 10, padB: 34, padL: isNarrow(svg) ? 100 : 112, padR: 18, r: 6.5 }, o);
  const h = o.padT + o.rowH * groups.length + o.padB;
  const p = new Plot(svg, { w: o.w, h, padT: o.padT, padB: o.padB, padL: o.padL, padR: o.padR, xmin: o.xmin, xmax: o.xmax });
  const base = h - o.padB;
  const front = [];
  if (o.grand != null) p.add(`<line class="grand-line" x1="${p.X(o.grand).toFixed(1)}" x2="${p.X(o.grand).toFixed(1)}" y1="${o.padT}" y2="${base}"/>`);
  groups.forEach((g, i) => {
    const top = o.padT + o.rowH * i, cy = top + o.rowH / 2, m = mean(g.values);
    if (i) p.add(`<line class="row-line" x1="0" x2="${o.w}" y1="${top}" y2="${top}"/>`);
    p.add(`<text class="lbl" x="6" y="${cy - 3}">${esc(g.name)}</text>`);
    p.add(`<text x="6" y="${cy + 14}">x̄ = ${fn(m, 2)}</text>`);
    const mx = p.X(clamp(m, o.xmin, o.xmax)).toFixed(1);
    p.add(`<line class="mean-line" x1="${mx}" x2="${mx}" y1="${(cy - o.rowH * 0.36).toFixed(1)}" y2="${(cy + o.rowH * 0.36).toFixed(1)}"/>`);
    // stack dots that share (almost) the same x position
    const xs = g.values.map(v => p.X(clamp(v, o.xmin, o.xmax)));
    const bins = xs.map(x => Math.round(x / (o.r * 1.7)));
    const count = {}; bins.forEach(b => { count[b] = (count[b] || 0) + 1; });
    const step = Math.min(o.r * 1.9, (o.rowH - 2 * o.r - 6) / Math.max(1, Math.max(...Object.values(count)) - 1));
    const used = {};
    xs.forEach((x, j) => {
      const b = bins[j], c = used[b] = (used[b] || 0) + 1;
      const y = cy + (count[b] - 1) / 2 * step - (c - 1) * step;
      const sel = o.sel && o.sel[0] === i && o.sel[1] === j;
      const pick = o.pick ? ` pick" data-g="${i}" data-j="${j}" tabindex="0" role="button" aria-label="${esc(g.name)}, value ${g.values[j]}` : '';
      p.add(`<circle class="dotc ${g.cls}${sel ? ' sel' : ''}${pick}" cx="${x.toFixed(1)}" cy="${y.toFixed(1)}" r="${o.r}"/>`);
    });
    if (o.sel && o.sel[0] === i && o.grand != null) {
      const x = g.values[o.sel[1]], ya = top + 7, yb = top + o.rowH - 6;
      const X = v => p.X(v).toFixed(1);
      front.push(`<line class="dev-between" x1="${X(o.grand)}" x2="${X(m)}" y1="${ya}" y2="${ya}"/>`);
      front.push(`<line class="dev-within" x1="${X(m)}" x2="${X(x)}" y1="${ya + 7}" y2="${ya + 7}"/>`);
      front.push(`<line class="dev-total" x1="${X(o.grand)}" x2="${X(x)}" y1="${yb}" y2="${yb}"/>`);
    }
  });
  front.forEach(s => p.add(s));
  p.xaxis(o.ticks || niceTicks(o.xmin, o.xmax));
  if (o.title) p.add(`<text x="${(o.padL + o.w - o.padR) / 2}" y="${h - 2}" text-anchor="middle">${o.title}</text>`);
  p.render();
}

// F curve with right-tail rejection region, p-value area and observed F
function drawF(svg, { d1, d2, alpha, F, xmax, h = 250 }) {
  const crit = fcrit(alpha, d1, d2);
  xmax = xmax || clamp(Math.ceil(Math.max(crit * 1.45, (F || 0) * 1.15)), 6, 40);
  const pdf = x => fpdf(x, d1, d2);
  let peak = 0;
  for (let x = 0.05; x <= xmax; x += xmax / 300) peak = Math.max(peak, pdf(x));
  const p = new Plot(svg, { xmin: 0, xmax, ymax: Math.min(peak, 1.25) * 1.14, h, padB: 54 });
  p.area(pdf, crit, xmax, 'area-rej');
  if (F != null) p.area(pdf, Math.min(F, xmax), xmax, 'area-pv');
  p.curve(pdf, 'curve', 0.002, xmax).xaxis(niceTicks(0, xmax));
  p.vline(crit, 'vline-crit', p.Y(p.ymax * 0.62));
  p.text(clamp(crit, xmax * 0.09, xmax * 0.9), p.base + 38, `F-crit = ${f(crit)}`, 'lbl-rej');
  p.text(Math.min((crit + xmax) / 2, xmax * 0.93), p.Y(p.ymax * 0.3), 'Reject H₀', 'lbl-rej');
  if (F != null) {
    p.vline(Math.min(F, xmax), 'vline-z', p.padT + 6);
    p.text(clamp(F, xmax * 0.08, xmax * 0.9), p.padT - 4, `F = ${f(F)}${F > xmax ? ' →' : ''}`, 'lbl-blue');
  }
  p.render();
  return crit;
}

/* =========================================================
   Small UI helpers
   ========================================================= */
function seg(el, initial, onChange) {
  const btns = $$('button', el);
  const set = v => btns.forEach(b => {
    b.classList.toggle('on', b.dataset.v === v);
    b.setAttribute('aria-pressed', b.dataset.v === v);
  });
  btns.forEach(b => b.addEventListener('click', () => { set(b.dataset.v); onChange(b.dataset.v); }));
  set(initial);
  return set;
}
function bar(el, frac) { el.style.width = `${clamp(frac * 100, 0.8, 100)}%`; }

/* =========================================================
   The caching example (used all over the page)
   ========================================================= */
const CACHE = [
  { name: 'A: No cache', short: 'A', label: 'no cache', cls: 'gA', values: [48, 52, 50, 55, 45] },
  { name: 'B: Redis', short: 'B', label: 'Redis', cls: 'gB', values: [38, 42, 40, 44, 36] },
  { name: 'C: In-memory', short: 'C', label: 'in-memory', cls: 'gC', values: [42, 46, 44, 40, 48] },
];
const CA = anova(CACHE.map(g => g.values));
const GCLS = ['gA', 'gB', 'gC', 'gD', 'gE', 'gF', 'gG', 'gH'];

/* ---------- Hero ---------- */
drawDots($('#heroPlot'), CACHE, { w: 430, xmin: 33, xmax: 58, ticks: [35, 40, 45, 50, 55], rowH: 62, r: 7.5, padL: 104, title: 'Response time (ms)', padB: 48 });

/* ---------- Gut guess ---------- */
(function guess() {
  const note = $('#guessNote');
  const paint = () => {
    $$('#guess [data-guess]').forEach(b => b.classList.toggle('selected', b.dataset.guess === store.guess));
    if (store.guess) {
      note.hidden = false;
      note.textContent = `Locked in: “${store.guess === 'real' ? 'at least one is really different' : 'just noise'}”. We'll test it properly in the worked example.`;
    }
  };
  $$('#guess [data-guess]').forEach(b => b.addEventListener('click', () => {
    store.guess = b.dataset.guess; save(); paint(); renderExample();
  }));
  paint();
})();

/* =========================================================
   False-alarm lab
   ========================================================= */
(function fwLab() {
  const st = { k: 3, alpha: '0.05' };
  const kEl = $('#fw-k');
  function render() {
    const a = +st.alpha, m = st.k * (st.k - 1) / 2, risk = 1 - (1 - a) ** m;
    $('#fw-k-o').textContent = st.k;
    $('#fw-m').textContent = m;
    $('#fw-a').textContent = pct(a, 0);
    $('#fw-r').textContent = pct(risk);
    $('#fw-out').textContent = `k = ${st.k} groups → m = ${st.k}·${st.k - 1}/2 = ${m} tests → 1 − ${(1 - a).toFixed(2)}^${m} = ${risk.toFixed(4)}`;
    const p = new Plot($('#fwPlot'), { xmin: 0, xmax: 45, ymin: 0, ymax: 1, padL: 46, padB: 50, padT: 16, h: 260 });
    p.yaxis([0, 0.25, 0.5, 0.75, 1], v => `${v * 100}%`);
    p.xaxis([0, 5, 10, 15, 20, 25, 30, 35, 40, 45]);
    p.add(`<text x="${(p.padL + p.w - p.padR) / 2}" y="${p.h - 6}" text-anchor="middle">number of pairwise tests m</text>`);
    p.hline(a, 'vline-crit');
    p.text(44.6, p.Y(a) - 6, `α = ${st.alpha}`, 'lbl-rej', 'end');
    p.curve(x => 1 - (1 - a) ** x, 'curve');
    p.vline(m, 'vline-z', p.Y(risk));
    p.add(`<circle class="mark" cx="${p.X(m).toFixed(1)}" cy="${p.Y(risk).toFixed(1)}" r="7"/>`);
    p.text(clamp(m, 5, 40), p.Y(risk) - 14, `${pct(risk)} with ${m} test${m > 1 ? 's' : ''}`, 'lbl-blue');
    p.render();
    $('#fwBars').hidden = true;
    $('#fwStats').textContent = '';
  }
  kEl.addEventListener('input', () => { st.k = +kEl.value; render(); });
  seg($('#fw-alpha'), st.alpha, v => { st.alpha = v; render(); });
  RENDERS.push(render);

  $('#fwRun').addEventListener('click', () => {
    const k = st.k, a = +st.alpha, n = 5, runs = 2000;
    const tc = tcrit2(a, 2 * n - 2), fc = fcrit(a, k - 1, k * (n - 1));
    let anyT = 0, anova = 0;
    for (let r = 0; r < runs; r++) {
      const m = [], ss = [];
      for (let i = 0; i < k; i++) {
        const g = Array.from({ length: n }, () => randn());
        m.push(mean(g)); ss.push(ssq(g, m[i]));
      }
      let hit = false;
      for (let i = 0; i < k && !hit; i++) for (let j = i + 1; j < k; j++) {
        const sp2 = (ss[i] + ss[j]) / (2 * n - 2);
        if (Math.abs(m[i] - m[j]) / Math.sqrt(sp2 * 2 / n) > tc) { hit = true; break; }
      }
      if (hit) anyT++;
      const gm = mean(m), ssb = n * sum(m.map(v => (v - gm) ** 2));
      if ((ssb / (k - 1)) / (sum(ss) / (k * (n - 1))) > fc) anova++;
    }
    $('#fwBars').hidden = false;
    bar($('#fwBarT'), anyT / runs); bar($('#fwBarF'), anova / runs);
    $('#fwValT').textContent = pct(anyT / runs);
    $('#fwValF').textContent = pct(anova / runs);
    $('#fwStats').textContent = `${runs.toLocaleString('en')} experiments, k = ${k}, target α = ${pct(a, 0)}`;
  });
  render();
})();

/* =========================================================
   Signal vs noise lab
   ========================================================= */
(function snLab() {
  const st = { d: 10, s: 4, n: 5, wobble: false, z: null };
  const draw = r => [0, 1, 2].map(() => Array.from({ length: 20 }, () => randn(r)));
  st.z = draw(mulberry32(11));
  const el = { d: $('#sn-d'), s: $('#sn-s'), n: $('#sn-n'), w: $('#sn-wobble') };
  function render() {
    $('#sn-d-o').textContent = fn(st.d, 1);
    $('#sn-s-o').textContent = fn(st.s, 1);
    $('#sn-n-o').textContent = st.n;
    const mus = [50 - st.d, 50, 50 + st.d];
    const groups = mus.map((mu, i) => {
      let z = st.z[i].slice(0, st.n);
      if (!st.wobble) {                       // exact sample means and spread
        const m = mean(z), sd = Math.sqrt(ssq(z, m) / (z.length - 1));
        z = z.map(v => (v - m) / sd);
      }
      return { name: `Group ${'ABC'[i]}`, cls: GCLS[i], values: z.map(v => mu + st.s * v) };
    });
    const A = anova(groups.map(g => g.values));
    const crit = fcrit(0.05, A.dfb, A.dfw);
    drawDots($('#snPlot'), groups, { xmin: 0, xmax: 100, ticks: niceTicks(0, 100, 10), grand: A.grand, r: 5.5, rowH: 60 });
    const top = Math.max(A.msb, A.msw);
    bar($('#snBarB'), A.msb / top); bar($('#snBarW'), A.msw / top);
    $('#snValB').textContent = f(A.msb);
    $('#snValW').textContent = f(A.msw);
    $('#sn-F').textContent = f(A.F);
    $('#sn-crit').textContent = f(crit);
    $('#sn-p').textContent = fp(A.p);
    $('#sn-eta').textContent = f(A.eta);
    const v = $('#sn-verdict'), rej = A.F > crit;
    v.className = `verdict-banner ${rej ? 'rej' : 'keep'}`;
    v.textContent = rej
      ? `F = ${f(A.F)} > ${f(crit)} → reject H₀: the means differ more than noise predicts`
      : `F = ${f(A.F)} ≤ ${f(crit)} → fail to reject H₀: the differences are within the noise`;
  }
  const sync = () => { el.d.value = st.d; el.s.value = st.s; el.n.value = st.n; el.w.checked = st.wobble; };
  el.d.addEventListener('input', () => { st.d = +el.d.value; render(); });
  el.s.addEventListener('input', () => { st.s = +el.s.value; render(); });
  el.n.addEventListener('input', () => { st.n = +el.n.value; render(); });
  el.w.addEventListener('change', () => { st.wobble = el.w.checked; render(); });
  $('#sn-new').addEventListener('click', () => { st.z = draw(Math.random); render(); });
  $$('#snLab [data-preset]').forEach(b => b.addEventListener('click', () => {
    const k = b.dataset.preset;
    if (k === 'small') Object.assign(st, { d: 10, s: 3, wobble: false });
    if (k === 'large') Object.assign(st, { d: 10, s: 13, wobble: false });
    if (k === 'null') Object.assign(st, { d: 0, s: 6, wobble: true });
    sync(); render();
  }));
  RENDERS.push(render);
  render();
})();

/* =========================================================
   F distribution lab + critical value table
   ========================================================= */
(function fLab() {
  const st = { k: 5, n: 5, F: 1.5, alpha: '0.05' };
  const el = { k: $('#fl-k'), n: $('#fl-n'), F: $('#fl-F') };
  const DF1 = [1, 2, 3, 4, 5], DF2 = [6, 9, 12, 15, 20, 30, 60];
  function table(d1, d2) {
    const a = +st.alpha;
    $('#fTable').innerHTML = `<thead><tr><th>df₂ \\ df₁</th>${DF1.map(c => `<th>${c}</th>`).join('')}</tr></thead><tbody>` +
      DF2.map(r => `<tr${r === d2 ? ' class="hl-row"' : ''}><td>${r}</td>${DF1.map(c =>
        `<td${r === d2 && c === d1 ? ' class="hl"' : ''}>${fcrit(a, c, r).toFixed(2)}</td>`).join('')}</tr>`).join('') + '</tbody>';
  }
  function render() {
    const d1 = st.k - 1, d2 = st.k * (st.n - 1), a = +st.alpha;
    const crit = fcrit(a, d1, d2);
    const xmax = clamp(Math.ceil(crit * 1.45), 6, 40);
    el.F.max = xmax;
    st.F = Math.min(st.F, xmax);
    el.k.value = st.k; el.n.value = st.n; el.F.value = st.F;
    $('#fl-k-o').textContent = st.k;
    $('#fl-n-o').textContent = `${st.n}  (N = ${st.k * st.n})`;
    $('#fl-F-o').textContent = f(st.F);
    drawF($('#flPlot'), { d1, d2, alpha: a, F: st.F, xmax });
    const p = fsf(st.F, d1, d2);
    $('#fl-df').textContent = `(${d1}, ${d2})`;
    $('#fl-crit').textContent = f(crit);
    $('#fl-p').textContent = fp(p);
    const v = $('#fl-verdict'), rej = st.F > crit;
    v.className = `verdict-banner ${rej ? 'rej' : 'keep'}`;
    v.textContent = rej
      ? `F = ${f(st.F)} > ${f(crit)} and p = ${fp(p)} ≤ ${st.alpha} → reject H₀`
      : `F = ${f(st.F)} ≤ ${f(crit)} and p = ${fp(p)} > ${st.alpha} → fail to reject H₀`;
    table(d1, d2);
  }
  el.k.addEventListener('input', () => { st.k = +el.k.value; render(); });
  el.n.addEventListener('input', () => { st.n = +el.n.value; render(); });
  el.F.addEventListener('input', () => { st.F = +el.F.value; render(); });
  const setAlpha = seg($('#fl-alpha'), st.alpha, v => { st.alpha = v; render(); });
  $('#fl-slide').addEventListener('click', () => { Object.assign(st, { k: 5, n: 5, F: 1.5, alpha: '0.05' }); setAlpha('0.05'); render(); });
  $('#fl-cache').addEventListener('click', () => { Object.assign(st, { k: 3, n: 5, F: 5.6, alpha: '0.05' }); setAlpha('0.05'); render(); });
  RENDERS.push(render);
  render();
})();

/* =========================================================
   Worked example
   ========================================================= */
const exState = { shown: store.ex || 0, sel: [0, 3] };

function exStepsHTML() {
  const A = CA, g = CACHE, n = 5;
  const crit = fcrit(0.05, A.dfb, A.dfw);
  const dev = v => (v === 0 ? '0' : fs(v, 0));
  const guessNote = store.guess
    ? `<p class="callout">Your gut guess was “${store.guess === 'real' ? 'at least one is really different' : 'just noise'}” — ${store.guess === 'real' ? 'the test agrees with you.' : 'the test disagrees: a gap this large is very unlikely to be noise alone.'}</p>` : '';
  return [
    ['Group means and grand mean',
      g.map((x, i) => `<p class="formula">x̄<sub>${x.short}</sub> = (${x.values.join(' + ')}) / ${n} = ${fn(A.means[i], 2)}</p>`).join('') +
      `<p class="formula">x̿ = (${g.map(x => sum(x.values)).join(' + ')}) / ${A.N} = ${f(A.grand)} ms</p>`],
    ['Between-group sum of squares',
      `<p class="formula">SSB = Σ n<sub>i</sub> (x̄<sub>i</sub> − x̿)²</p>
       <div class="table-wrap"><table class="crit-table anova-table compact-table">
       <thead><tr><th>Group</th><th>n<sub>i</sub></th><th>x̄<sub>i</sub> − x̿</th><th>(x̄<sub>i</sub> − x̿)²</th><th>n<sub>i</sub>(x̄<sub>i</sub> − x̿)²</th></tr></thead><tbody>` +
      g.map((x, i) => `<tr><td>${x.short}</td><td>${n}</td><td>${f(A.means[i] - A.grand)}</td><td>${f((A.means[i] - A.grand) ** 2)}</td><td>${f(A.parts[i])}</td></tr>`).join('') +
      `<tr class="sum-row"><td>Sum</td><td></td><td></td><td></td><td>${f(A.ssb)}</td></tr></tbody></table></div>
       <p class="formula">MSB = ${f(A.ssb)} / ${A.dfb} = ${f(A.msb)}</p>`],
    ['Within-group sum of squares',
      `<p class="formula">SSW = Σ Σ (x<sub>ij</sub> − x̄<sub>i</sub>)²</p>
       <div class="table-wrap"><table class="crit-table anova-table compact-table">
       <thead><tr><th>Group</th><th>Deviations from own mean</th><th>Squared, summed</th></tr></thead><tbody>` +
      g.map((x, i) => `<tr><td>${x.short}</td><td>${x.values.map(v => dev(v - A.means[i])).join(', ')}</td><td>${fn(A.within[i], 2)}</td></tr>`).join('') +
      `<tr class="sum-row"><td>Sum</td><td></td><td>${f(A.ssw)}</td></tr></tbody></table></div>
       <p class="formula">MSW = ${f(A.ssw)} / ${A.dfw} = ${f(A.msw)}</p>`],
    ['Complete the ANOVA table',
      `<div class="table-wrap"><table class="crit-table anova-table compact-table">
       <thead><tr><th>Source</th><th>SS</th><th>df</th><th>MS</th><th>F</th></tr></thead><tbody>
       <tr><td>Between (strategy)</td><td>${f(A.ssb)}</td><td>${A.dfb}</td><td>${f(A.msb)}</td><td><b>${f(A.F)}</b></td></tr>
       <tr><td>Within (error)</td><td>${f(A.ssw)}</td><td>${A.dfw}</td><td>${f(A.msw)}</td><td></td></tr>
       <tr class="sum-row"><td>Total</td><td>${f(A.sst)}</td><td>${A.N - 1}</td><td></td><td></td></tr></tbody></table></div>
       <p class="formula">F = ${f(A.msb)} / ${f(A.msw)} = ${f(A.F)}</p>`],
    ['Decision',
      `<svg id="exF" class="plot" role="img" aria-label="F distribution with 2 and 12 degrees of freedom, critical value 3.89 and observed F 11.01"></svg>
       <div class="two-col verdicts">
         <div class="panel"><p class="panel-title">Critical value</p><p>F(${A.dfb}, ${A.dfw}) at α = 0.05 is ${f(crit)}.</p><p><b>${f(A.F)} &gt; ${f(crit)} → reject</b></p></div>
         <div class="panel"><p class="panel-title">p-value</p><p>P(F &gt; ${f(A.F)}) ≈ ${A.p.toFixed(4)}</p><p><b>${A.p.toFixed(4)} ≤ 0.05 → reject</b></p></div>
       </div>
       <p class="verdict-banner rej">Decision: Reject H₀</p>`],
    ['Interpret the result',
      `<div class="two-col">
         <div class="panel"><p class="panel-title">Statistical interpretation</p><p>At α = 0.05, at least one caching strategy has a different mean response time (F(${A.dfb}, ${A.dfw}) = ${f(A.F)}, p ≈ ${A.p.toFixed(3)}).</p></div>
         <div class="panel accent"><p class="panel-title">Engineering interpretation</p><p>The caching choice matters for latency. Next question: which strategy is actually faster?</p></div>
       </div>${guessNote}
       <p class="takeaway">Significant F → “which groups?” → post hoc test</p>`],
  ];
}

function renderExample() {
  const steps = exStepsHTML();
  exState.shown = clamp(exState.shown, 0, steps.length);
  $('#exSteps').innerHTML = steps.map(([title, body], i) =>
    `<li class="ex-step"${i < exState.shown ? '' : ' hidden'}><b>${i + 1}</b><div><h4>Step ${i + 1}: ${title}</h4>${body}</div></li>`).join('');
  if (exState.shown >= 5) drawF($('#exF'), { d1: CA.dfb, d2: CA.dfw, alpha: 0.05, F: CA.F, h: 230 });
  const next = $('#exNext');
  next.hidden = exState.shown >= steps.length;
  next.textContent = `Show step ${exState.shown + 1}`;
  $('#exAll').hidden = exState.shown >= steps.length;
  $('#exHide').hidden = exState.shown === 0;
  store.ex = exState.shown; save();
}

function renderExPlot() {
  const [gi, j] = exState.sel, g = CACHE[gi], x = g.values[j], m = CA.means[gi], G = CA.grand;
  drawDots($('#exPlot'), CACHE, { xmin: 33, xmax: 58, ticks: [35, 40, 45, 50, 55], grand: G, sel: exState.sel, pick: true, rowH: 66, r: 7.5, title: 'Response time (ms)', padB: 46 });
  $('#exDecomp').innerHTML =
    `${g.short}, x = ${x}:&nbsp; <span class="t-total">x − x̿ = ${fs(x - G)}</span> &nbsp;=&nbsp; ` +
    `<span class="t-between">(x̄<sub>${g.short}</sub> − x̿) ${fs(m - G)}</span> &nbsp;+&nbsp; ` +
    `<span class="t-within">(x − x̄<sub>${g.short}</sub>) ${fs(x - m)}</span>`;
}

(function example() {
  const runs = CACHE[0].values.map((_, i) => `<th>Run ${i + 1}</th>`).join('');
  $('#exData').innerHTML = `<thead><tr><th>Strategy</th>${runs}<th>Mean x̄<sub>i</sub></th></tr></thead><tbody>` +
    CACHE.map((g, i) => `<tr><td><i class="chip ${g.cls}"></i>${g.name}</td>${g.values.map(v => `<td>${v}</td>`).join('')}<td><b>${fn(CA.means[i], 2)}</b></td></tr>`).join('') + '</tbody>';
  const plot = $('#exPlot');
  const pick = t => {
    const c = t.closest('.pick');
    if (!c) return;
    exState.sel = [+c.dataset.g, +c.dataset.j];
    renderExPlot();
    const again = $(`.pick[data-g="${exState.sel[0]}"][data-j="${exState.sel[1]}"]`, plot);
    if (again && document.activeElement !== again && c.matches(':focus')) again.focus();
  };
  plot.addEventListener('click', e => pick(e.target));
  plot.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); pick(e.target); } });
  $('#exNext').addEventListener('click', () => { exState.shown++; renderExample(); });
  $('#exAll').addEventListener('click', () => { exState.shown = 99; renderExample(); });
  $('#exHide').addEventListener('click', () => { exState.shown = 0; renderExample(); });
  RENDERS.push(renderExPlot, renderExample);
  renderExPlot();
  renderExample();
})();

/* =========================================================
   Tukey HSD
   ========================================================= */
(function tukey() {
  const st = { alpha: '0.05' };
  const pairs = [[0, 1], [0, 2], [2, 1]];
  function render() {
    const a = +st.alpha, n = 5;
    const q = qtukey(a, CA.k, CA.dfw), hsd = q * Math.sqrt(CA.msw / n);
    $('#tk-line').textContent = `HSD = q · √(MSW / n) = ${f(q)} · √(${f(CA.msw)} / ${n}) = ${f(hsd)} ms`;
    const top = Math.max(12, hsd * 1.15);
    const read = [];
    $('#tk-pairs').innerHTML = pairs.map(([i, j]) => {
      const d = Math.abs(CA.means[i] - CA.means[j]), diff = d > hsd;
      const [slow, fast] = CA.means[i] > CA.means[j] ? [CACHE[i], CACHE[j]] : [CACHE[j], CACHE[i]];
      read.push(diff ? `${fast.label} (${fast.short}) is faster than ${slow.label} (${slow.short})`
        : `${CACHE[i].short} and ${CACHE[j].short} are not clearly different`);
      return `<div class="pair">
        <span class="pair-name">${CACHE[i].short} vs ${CACHE[j].short}</span>
        <div class="pair-track"><i class="${diff ? 'diff' : 'same'}" style="width:${(d / top * 100).toFixed(1)}%"></i><em style="left:${(hsd / top * 100).toFixed(1)}%"></em></div>
        <span class="pair-val">|diff| = ${fn(d, 2)} ms</span>
        <span class="tag ${diff ? 'bad' : 'good'}">${diff ? 'different' : 'not different'}</span>
      </div>`;
    }).join('') + `<div class="pair pair-axis"><span class="pair-name"></span><div class="pair-track bare"><em class="lbl" style="left:${(hsd / top * 100).toFixed(1)}%">HSD = ${f(hsd)}</em></div><span class="pair-val"></span><span class="tag ghost">different</span></div>`;
    const s = read.join('; ');
    $('#tk-read').textContent = s.charAt(0).toUpperCase() + s.slice(1) + '.';
  }
  seg($('#tk-alpha'), st.alpha, v => { st.alpha = v; render(); });
  render();
})();

/* =========================================================
   Two-way model, interaction lab, df table
   ========================================================= */
(function model() {
  const T = {
    mu: ['μ — grand mean', 'The overall average response time across every cache and every load level.'],
    a: ['αᵢ — effect of factor A', 'How much caching strategy i shifts the mean up or down. This is the main effect of caching.'],
    b: ['βⱼ — effect of factor B', 'How much load level j shifts the mean up or down. This is the main effect of load.'],
    ab: ['(αβ)ᵢⱼ — interaction effect', 'The extra shift for the specific combination of cache i and load j, beyond the two main effects added together. If every interaction term is zero, the lines in the interaction plot are parallel.'],
    e: ['εᵢⱼₖ — random error', 'Run-to-run noise of observation k in that cell. Its variance is estimated by MSE, the denominator of every F in the two-way table.'],
  };
  const show = k => {
    $$('#model button').forEach(b => b.classList.toggle('on', b.dataset.t === k));
    $('#modelExplain').innerHTML = `<p class="panel-title">${T[k][0]}</p><p>${T[k][1]}</p>`;
  };
  $$('#model button').forEach(b => b.addEventListener('click', () => show(b.dataset.t)));
  show('ab');
})();

(function ixLab() {
  const st = { L: 8, I: 0 };
  const low = [50, 40, 44], names = ['A: No cache', 'B: Redis', 'C: In-memory'];
  const el = { l: $('#ix-l'), i: $('#ix-i') };
  function render() {
    el.l.value = st.L; el.i.value = st.I;
    $('#ix-l-o').textContent = `${fs(st.L, 0)} ms`;
    $('#ix-i-o').textContent = fs(st.I, 1);
    const pen = [st.L, st.L + st.I, st.L - st.I], high = low.map((v, i) => v + pen[i]);
    const p = new Plot($('#ixPlot'), { xmin: -0.35, xmax: 2.35, ymin: 30, ymax: 75, padL: 44, padB: 34, padT: 26, h: 300 });
    p.yaxis([30, 40, 50, 60, 70]);
    p.add(`<text x="${p.padL - 34}" y="14">Mean response time (ms)</text>`);
    names.forEach((nm, i) => p.text(i, p.base + 20, nm, 'lbl'));
    const line = (ys, cls) => {
      p.add(`<polyline class="${cls}" points="${ys.map((y, i) => `${p.X(i).toFixed(1)},${p.Y(y).toFixed(1)}`).join(' ')}"/>`);
      ys.forEach((y, i) => p.add(`<circle class="${cls}-dot" cx="${p.X(i).toFixed(1)}" cy="${p.Y(y).toFixed(1)}" r="6"/>`));
    };
    low.forEach((y, i) => p.add(`<line class="ix-gap" x1="${p.X(i).toFixed(1)}" x2="${p.X(i).toFixed(1)}" y1="${p.Y(y).toFixed(1)}" y2="${p.Y(high[i]).toFixed(1)}"/>`));
    line(low, 'ix-low'); line(high, 'ix-high');
    p.render();
    $('#ix-table').innerHTML = `<thead><tr><th>Mean (ms)</th><th>A</th><th>B</th><th>C</th></tr></thead><tbody>
      <tr><td>Low load</td>${low.map(v => `<td>${fn(v, 1)}</td>`).join('')}</tr>
      <tr><td>High load</td>${high.map(v => `<td>${fn(v, 1)}</td>`).join('')}</tr>
      <tr class="sum-row"><td>High − Low</td>${pen.map(v => `<td>${fs(v, 1).replace('.0', '')}</td>`).join('')}</tr></tbody>`;
    const v = $('#ix-verdict');
    if (st.I === 0) {
      v.className = 'verdict-banner keep';
      v.textContent = st.L === 0
        ? 'The two lines coincide: load has no effect, and there is no interaction.'
        : `Parallel lines → no interaction. High load adds ${st.L} ms for every cache, and the ranking stays the same.`;
    } else {
      const flip = high[2] < high[1];
      v.className = 'verdict-banner rej';
      v.textContent = `Lines are not parallel → interaction. High load changes the mean by ${fs(pen[0], 1)} ms (A), ${fs(pen[1], 1)} ms (B) and ${fs(pen[2], 1)} ms (C)` +
        (flip ? ', and the fastest cache flips from Redis to in-memory.' : ', but Redis stays the fastest.');
    }
  }
  el.l.addEventListener('input', () => { st.L = +el.l.value; render(); });
  el.i.addEventListener('input', () => { st.I = +el.i.value; render(); });
  const PRE = { none: { L: 8, I: 0 }, some: { L: 8, I: -5 }, flip: { L: 8, I: 5 } };
  $$('#ixLab [data-ix]').forEach(b => b.addEventListener('click', () => { Object.assign(st, PRE[b.dataset.ix]); render(); }));
  RENDERS.push(render);
  render();
})();

(function twoWayDf() {
  const el = { a: $('#tw-a'), b: $('#tw-b'), n: $('#tw-n') };
  function render() {
    const a = +el.a.value, b = +el.b.value, n = +el.n.value;
    $('#tw-a-o').textContent = a; $('#tw-b-o').textContent = b; $('#tw-n-o').textContent = n;
    const rows = [
      ['Factor A', 'a − 1', a - 1, 'MSA / MSE'],
      ['Factor B', 'b − 1', b - 1, 'MSB / MSE'],
      ['Interaction A × B', '(a − 1)(b − 1)', (a - 1) * (b - 1), 'MSAB / MSE'],
      ['Error', 'ab(n − 1)', a * b * (n - 1), ''],
      ['Total', 'abn − 1', a * b * n - 1, ''],
    ];
    $('#tw-table').innerHTML = '<thead><tr><th>Source</th><th>df formula</th><th>df</th><th>F test</th></tr></thead><tbody>' +
      rows.map((r, i) => `<tr${i === 4 ? ' class="sum-row"' : ''}><td>${r[0]}</td><td>${r[1]}</td><td><b>${r[2]}</b></td><td>${r[3]}</td></tr>`).join('') +
      `</tbody><tfoot><tr><td colspan="4">${a} × ${b} cells, ${n} observations each → ${a * b * n} observations in total</td></tr></tfoot>`;
  }
  Object.values(el).forEach(e => e.addEventListener('input', render));
  render();
})();

/* =========================================================
   Multiple-choice quizzes
   ========================================================= */
const QUIZZES = {
  quizH1: {
    options: ['Correct', 'Wrong'],
    items: [
      { q: '“At least one caching strategy has a different mean response time.”', a: 0, why: 'That is exactly what H₁ says.' },
      { q: '“All three strategies have different mean response times.”', a: 1, why: 'H₁ only says at least one mean differs. Two of them could still be equal.' },
      { q: '“Redis is the fastest strategy.”', a: 1, why: 'ANOVA tells you whether there is a difference, not where it is. That needs a post hoc test.' },
      { q: '“H₀: μA = μB = μC is rejected at α = 0.05.”', a: 0, why: 'A significant F means exactly this.' },
      { q: '“The sample means 50, 40 and 44 are not equal, so H₀ must be false.”', a: 1, why: 'Sample means always differ a little. The question is whether they differ more than noise predicts.' },
      { q: '“The three groups have different variances.”', a: 1, why: 'ANOVA is a test about means. It only uses variances to measure signal and noise.' },
    ],
  },
  quizF: {
    options: ['Evidence against H₀', 'No evidence', 'Impossible'],
    items: [
      { q: 'F = 0.92', a: 1, why: 'F ≈ 1: the group means differ about as much as noise predicts.' },
      { q: 'F = 14.0, with F-crit = 4.26', a: 0, why: 'The signal is 14 times the noise and far beyond the critical value.' },
      { q: 'F = −2.3', a: 2, why: 'F is a ratio of two variances, and variances are never negative.' },
      { q: 'F = 3.10, with F-crit = 3.89', a: 1, why: 'Bigger than 1, but still below the critical value → fail to reject H₀.' },
      { q: 'F = 11.01, with p ≈ 0.002', a: 0, why: 'p is far below 0.05, so a ratio this large is very unlikely under H₀.' },
      { q: 'F = 1.08', a: 1, why: 'Almost exactly what we expect when all population means are equal.' },
    ],
  },
  quizDf: {
    items: [
      { q: 'k = 3 groups with 5 runs each. The F statistic has df …', options: ['(2, 12)', '(3, 15)', '(2, 14)'], a: 0, why: 'k − 1 = 2 and N − k = 15 − 3 = 12.' },
      { q: '5 groups, N = 25 observations in total.', options: ['(5, 25)', '(4, 20)', '(4, 24)'], a: 1, why: 'k − 1 = 4 and N − k = 25 − 5 = 20.' },
      { q: '4 teaching methods with 6 students each.', options: ['(4, 24)', '(3, 23)', '(3, 20)'], a: 2, why: 'k − 1 = 3 and N − k = 24 − 4 = 20.' },
      { q: 'Three groups of sizes 4, 5 and 6.', options: ['(2, 12)', '(2, 14)', '(3, 12)'], a: 0, why: 'N = 15, so df = (3 − 1, 15 − 3) = (2, 12). Unequal group sizes are fine.' },
      { q: 'SSB = 56 with k = 3 groups. MSB = ?', options: ['18.67', '28', '56'], a: 1, why: 'MSB = SSB / (k − 1) = 56 / 2 = 28.' },
      { q: 'SSW = 18 with N = 12 and k = 3. MSW = ?', options: ['1.5', '6', '2'], a: 2, why: 'MSW = SSW / (N − k) = 18 / 9 = 2.' },
    ],
  },
  quizMethod: {
    options: ['One-way ANOVA', "Welch's ANOVA", 'Kruskal–Wallis', 'Repeated-measures'],
    items: [
      { q: 'Three independent groups, s = 3.8, 3.2 and 3.2, dot plots roughly bell-shaped.', a: 0, why: 'Largest s / smallest s = 1.19 < 2 and no sign of non-normality: the ordinary F test is fine.' },
      { q: 'The group standard deviations are 2, 5 and 11 ms.', a: 1, why: '11 / 2 = 5.5, far above 2. Welch\'s ANOVA does not assume equal variances.' },
      { q: 'Response times are strongly right-skewed with a few huge outliers.', a: 2, why: 'Normality fails badly. Use the rank-based Kruskal–Wallis test (or log-transform first).' },
      { q: 'The same 10 users try all three app designs.', a: 3, why: 'The groups are not independent, because every user appears in each group.' },
      { q: '8 runs per group, mild skew, largest s / smallest s = 1.4.', a: 0, why: 'ANOVA is fairly robust to mild non-normality when group sizes are equal.' },
    ],
  },
  quizInteraction: {
    options: ['Interaction', 'No interaction'],
    items: [
      { q: 'Under high load, every cache is exactly 8 ms slower.', a: 1, why: 'The load effect is the same for every cache, so the lines are parallel.' },
      { q: 'Redis is fastest at low load, but in-memory is fastest at high load.', a: 0, why: 'The best cache depends on the load level. That is what interaction means.' },
      { q: 'High load adds 15 ms without a cache, but only 3 ms with Redis.', a: 0, why: 'The size of the load effect depends on the cache, so the lines are not parallel.' },
      { q: 'The lines in the interaction plot are parallel.', a: 1, why: 'Parallel lines mean the two factors simply add up.' },
      { q: 'Output row “Caching × Load”: F = 0.94, p = 0.41.', a: 1, why: 'p > 0.05: no significant interaction, so the main effects can be read on their own.' },
    ],
  },
  quizMyth: {
    options: ['True', 'False'],
    items: [
      { q: '“A significant F means all groups differ.”', a: 1, why: 'No — it means at least one differs.' },
      { q: '“Just run t tests on every pair.”', a: 1, why: 'No — false alarms add up. Use ANOVA, then a post hoc test.' },
      { q: '“ANOVA tests whether the variances differ.”', a: 1, why: 'No — it tests means, using variances.' },
      { q: '“Reject in both tails of the F distribution.”', a: 1, why: 'No — only a large F is evidence against H₀, so the rejection region is the right tail.' },
      { q: '“In two-way ANOVA you can skip the interaction row.”', a: 1, why: 'No — check the interaction before the main effects.' },
      { q: '“If H₀ is true, we expect F to be close to 1.”', a: 0, why: 'Both mean squares then estimate the same noise variance.' },
      { q: '“Post hoc tests should only follow a significant F.”', a: 0, why: 'Without a significant F there is no evidence of any difference to locate.' },
      { q: '“η² = 0.65 means the groups explain 65% of the variation in the response.”', a: 0, why: 'η² = SSB / SST, the explained share of the total variation.' },
      { q: '“A larger spread inside the groups makes F larger.”', a: 1, why: 'More noise means a larger MSW, the denominator, so F gets smaller.' },
    ],
  },
};

function buildQuiz(id) {
  const el = document.getElementById(id), cfg = QUIZZES[id];
  const answers = store.quiz[id] = store.quiz[id] || {};
  el.innerHTML = `<div class="quiz-head"><span>${el.dataset.title}</span><span class="q-score"></span></div>` +
    cfg.items.map((it, i) => `
      <div class="q-item" data-i="${i}">
        <div class="q-row">
          <div class="q-text">${it.q}</div>
          <div class="q-opts">${(it.options || cfg.options).map((o, k) => `<button data-k="${k}">${o}</button>`).join('')}</div>
        </div>
        <p class="q-explain" hidden></p>
      </div>`).join('');

  const paintItem = i => {
    const row = $(`.q-item[data-i="${i}"]`, el), it = cfg.items[i], pick = answers[i];
    const btns = $$('.q-opts button', row), ex = $('.q-explain', row);
    if (pick == null) { btns.forEach(b => { b.disabled = false; b.className = ''; }); ex.hidden = true; return; }
    btns.forEach(b => {
      const k = +b.dataset.k;
      b.disabled = true;
      b.className = k === it.a ? 'right' : k === pick ? 'wrong' : '';
    });
    ex.hidden = false;
    ex.innerHTML = (pick === it.a ? '<b class="ok">Correct.</b> ' : '<b class="no">Not quite.</b> ') + it.why;
  };
  const paintScore = () => {
    const done = Object.keys(answers).length;
    const right = Object.entries(answers).filter(([i, k]) => cfg.items[i].a === k).length;
    $('.q-score', el).innerHTML = `${right}/${cfg.items.length} correct` +
      (done ? ` · <button class="link-btn" style="margin:0">retry</button>` : '');
    const r = $('.q-score button', el);
    if (r) r.addEventListener('click', () => {
      Object.keys(answers).forEach(k => delete answers[k]);
      save(); cfg.items.forEach((_, i) => paintItem(i)); paintScore();
    });
    Score.set(id, right, cfg.items.length);
  };

  el.addEventListener('click', e => {
    const b = e.target.closest('.q-opts button');
    if (!b || b.disabled) return;
    const i = +b.closest('.q-item').dataset.i;
    answers[i] = +b.dataset.k;
    save(); paintItem(i); paintScore();
  });
  cfg.items.forEach((_, i) => paintItem(i));
  paintScore();
}
Object.keys(QUIZZES).forEach(buildQuiz);

/* =========================================================
   In-class challenge
   ========================================================= */
const CHALLENGE = [
  { name: 'D1', values: [20, 22, 19, 23] },
  { name: 'D2', values: [25, 27, 26, 26] },
  { name: 'D3', values: [21, 24, 22, 21] },
];
(function challenge() {
  const A = anova(CHALLENGE.map(g => g.values));
  const crit = fcrit(0.05, A.dfb, A.dfw);
  const form = $('#chForm');
  const near = (v, t, tol) => isFinite(v) && Math.abs(v - t) <= tol;
  const checks = {
    m1: v => near(v, A.means[0], 0.011), m2: v => near(v, A.means[1], 0.011), m3: v => near(v, A.means[2], 0.011),
    grand: v => near(v, A.grand, 0.011),
    ssb: v => near(v, A.ssb, 0.06), msb: v => near(v, A.msb, 0.06),
    ssw: v => near(v, A.ssw, 0.06), msw: v => near(v, A.msw, 0.06),
    F: v => near(v, A.F, 0.06),
    crit: v => near(v, crit, 0.03),
    eta: v => near(v > 1 ? v / 100 : v, A.eta, 0.006),
  };
  const total = 10;
  Score.set('challenge', 0, total);
  form.addEventListener('submit', e => {
    e.preventDefault();
    let right = 0;
    const mark = (label, ok) => { label.classList.toggle('ok', ok); label.classList.toggle('no', !ok); if (ok) right++; };
    mark(form.m1.closest('label'), ['m1', 'm2', 'm3'].every(k => checks[k](num(form[k].value))));
    ['grand', 'ssb', 'msb', 'ssw', 'msw', 'F', 'crit', 'eta'].forEach(k => mark(form[k].closest('label'), checks[k](num(form[k].value))));
    mark(form.dec.closest('label'), form.dec.value === 'r');
    Score.set('challenge', right, total);
    const fb = $('#chFb');
    fb.className = `tr-fb ${right === total ? 'ok' : 'no'}`;
    fb.textContent = right === total ? 'All 10 correct. Well done!' : `${right}/${total} correct. Fix the orange fields, or open the solution.`;
  });
  $('#chSolve').addEventListener('click', () => {
    const s = $('#chSolution');
    s.hidden = !s.hidden;
    if (s.hidden) return;
    const q = qtukey(0.05, A.k, A.dfw), hsd = q * Math.sqrt(A.msw / 4);
    const dev = v => (v === 0 ? '0' : fs(v, 0));
    s.innerHTML = `<p class="panel-title">Solution</p><ol>
      <li><b>Means:</b> x̄₁ = ${fn(A.means[0])}, x̄₂ = ${fn(A.means[1])}, x̄₃ = ${fn(A.means[2])}; grand mean x̿ = (84 + 104 + 88) / 12 = ${fn(A.grand)}.</li>
      <li><b>SSB</b> = 4·(21 − 23)² + 4·(26 − 23)² + 4·(22 − 23)² = 16 + 36 + 4 = ${fn(A.ssb)}; MSB = ${fn(A.ssb)} / 2 = ${fn(A.msb)}.</li>
      <li><b>SSW:</b> deviations ${CHALLENGE.map((g, i) => `${g.name}: ${g.values.map(v => dev(v - A.means[i])).join(', ')} → ${fn(A.within[i])}`).join('; ')}. SSW = ${fn(A.ssw)}; MSW = ${fn(A.ssw)} / 9 = ${fn(A.msw)}.</li>
      <li><b>F</b> = ${fn(A.msb)} / ${fn(A.msw)} = ${f(A.F, 1)}; F-crit = F(2, 9) at α = 0.05 = ${f(crit)}.</li>
      <li><b>Decision:</b> ${f(A.F, 1)} &gt; ${f(crit)} → reject H₀ (p ≈ ${A.p.toFixed(4)}). At least one design has a different mean completion time.</li>
      <li><b>Effect size:</b> η² = ${fn(A.ssb)} / ${fn(A.sst)} ≈ ${f(A.eta)}: the design explains about ${Math.round(A.eta * 100)}% of the variation.</li>
      <li><b>Bonus, Tukey:</b> HSD = ${f(q)}·√(${fn(A.msw)} / 4) = ${f(hsd)} s. D2 vs D1 (5 s) and D2 vs D3 (4 s) differ; D3 vs D1 (1 s) does not. D2 is the slow design.</li>
    </ol>`;
  });
})();

/* =========================================================
   One-way ANOVA calculator
   ========================================================= */
(function calculator() {
  const fromSet = set => set.map(g => ({ name: g.name, text: g.values.join(', ') }));
  const st = { alpha: '0.05', groups: Array.isArray(store.calc) && store.calc.length >= 2 ? store.calc : fromSet(CACHE) };
  const box = $('#calcGroups'), out = $('#calcOut');
  const parse = t => t.split(/[\s,;]+/).filter(Boolean).map(Number);

  function rows() {
    box.innerHTML = st.groups.map((g, i) => `
      <div class="g-row" data-i="${i}">
        <i class="chip big ${GCLS[i]}"></i>
        <input class="g-name" value="${esc(g.name)}" aria-label="Name of group ${i + 1}">
        <input class="g-vals" value="${esc(g.text)}" inputmode="decimal" aria-label="Values of group ${i + 1}" placeholder="e.g. 12, 15, 11, 14">
        <button class="icon-del" aria-label="Remove group ${i + 1}" ${st.groups.length <= 2 ? 'disabled' : ''}>×</button>
      </div>`).join('');
    $('#calcAdd').disabled = st.groups.length >= 8;
  }

  function compute() {
    store.calc = st.groups; save();
    const data = st.groups.map(g => parse(g.text));
    const bad = data.findIndex(d => d.some(v => !isFinite(v)));
    if (bad >= 0) return void (out.innerHTML = `<p class="callout warn">Group ${bad + 1} contains something that is not a number.</p>`);
    if (data.some(d => d.length < 1)) return void (out.innerHTML = '<p class="callout warn">Every group needs at least one value.</p>');
    const A = anova(data), a = +st.alpha;
    if (A.dfw < 1) return void (out.innerHTML = '<p class="callout warn">Not enough data: at least one group needs two or more values.</p>');
    if (A.ssw === 0) return void (out.innerHTML = '<p class="callout warn">There is no variation inside the groups (MSW = 0), so F cannot be computed.</p>');
    const names = st.groups.map((g, i) => g.name.trim() || `Group ${i + 1}`);
    const crit = fcrit(a, A.dfb, A.dfw), rej = A.F > crit;
    const sdOk = A.sds.filter(s => s > 0);
    const ratio = sdOk.length === A.k ? Math.max(...sdOk) / Math.min(...sdOk) : null;

    let post = '<li><b>Post hoc:</b> F is not significant, so there is no difference to locate and no post hoc test is needed.</li>';
    if (rej) {
      const q = qtukey(a, A.k, A.dfw), pr = [];
      for (let i = 0; i < A.k; i++) for (let j = i + 1; j < A.k; j++) {
        const d = Math.abs(A.means[i] - A.means[j]);
        const h = q * Math.sqrt(A.msw / 2 * (1 / A.ns[i] + 1 / A.ns[j]));
        pr.push(`<tr><td>${esc(names[i])} vs ${esc(names[j])}</td><td>${f(d)}</td><td>${f(h)}</td><td><span class="tag ${d > h ? 'bad' : 'good'}">${d > h ? 'different' : 'not different'}</span></td></tr>`);
      }
      post = `<li><b>Post hoc (Tukey HSD, q = ${f(q)}):</b>
        <div class="table-wrap"><table class="crit-table anova-table compact-table"><thead><tr><th>Pair</th><th>|diff|</th><th>HSD</th><th>Verdict</th></tr></thead><tbody>${pr.join('')}</tbody></table></div></li>`;
    }

    out.innerHTML = `
      <div class="calc-out">
        <div>
          <div class="table-wrap"><table class="crit-table anova-table compact-table">
            <thead><tr><th>Group</th><th>n</th><th>Mean</th><th>s</th></tr></thead>
            <tbody>${names.map((nm, i) => `<tr><td><i class="chip ${GCLS[i]}"></i>${esc(nm)}</td><td>${A.ns[i]}</td><td>${f(A.means[i])}</td><td>${A.ns[i] > 1 ? f(A.sds[i]) : '–'}</td></tr>`).join('')}
            <tr class="sum-row"><td>All data</td><td>${A.N}</td><td>${f(A.grand)}</td><td></td></tr></tbody></table></div>
          <div class="table-wrap"><table class="crit-table anova-table compact-table">
            <thead><tr><th>Source</th><th>SS</th><th>df</th><th>MS</th><th>F</th><th>p</th></tr></thead>
            <tbody><tr><td>Between</td><td>${f(A.ssb)}</td><td>${A.dfb}</td><td>${f(A.msb)}</td><td><b>${f(A.F)}</b></td><td>${fp(A.p)}</td></tr>
            <tr><td>Within</td><td>${f(A.ssw)}</td><td>${A.dfw}</td><td>${f(A.msw)}</td><td></td><td></td></tr>
            <tr class="sum-row"><td>Total</td><td>${f(A.sst)}</td><td>${A.N - 1}</td><td></td><td></td><td></td></tr></tbody></table></div>
        </div>
        <div>
          <svg id="calcDots" class="plot" role="img" aria-label="Dot plot of the entered groups"></svg>
          <svg id="calcF" class="plot" role="img" aria-label="F distribution with the observed F"></svg>
        </div>
      </div>
      <p class="verdict-banner ${rej ? 'rej' : 'keep'}">${rej ? 'Reject H₀' : 'Fail to reject H₀'} at α = ${st.alpha}</p>
      <ol class="report">
        <li><b>Hypotheses:</b> H₀: all ${A.k} population means are equal. H₁: at least one mean differs.</li>
        <li><b>Test statistic:</b> F(${A.dfb}, ${A.dfw}) = ${f(A.msb)} / ${f(A.msw)} = ${f(A.F)}.</li>
        <li><b>Decision:</b> F-crit = ${f(crit)} and p = ${fp(A.p)}. Since ${f(A.F)} ${rej ? '>' : '≤'} ${f(crit)}, ${rej ? 'reject H₀: at least one group mean is different.' : 'fail to reject H₀: there is not enough evidence that the means differ.'}</li>
        <li><b>Effect size:</b> η² = ${f(A.ssb)} / ${f(A.sst)} = ${f(A.eta)}, so the groups explain about ${Math.round(A.eta * 100)}% of the variation (${A.eta >= 0.14 ? 'large' : A.eta >= 0.06 ? 'medium' : 'small'}).</li>
        <li><b>Equal-variance check:</b> ${ratio == null ? 'not available (a group has a single value or no spread).' : `largest s / smallest s = ${f(ratio)} ${ratio < 2 ? '< 2 ✓' : '≥ 2 <span class="warn">— the rule of thumb flags unequal spread. Read the result with care, or use Welch\'s ANOVA.</span>'}`}</li>
        ${post}
      </ol>`;
    const all = data.flat(), lo = Math.min(...all), hi = Math.max(...all), pad = (hi - lo || 1) * 0.12;
    drawDots($('#calcDots'), names.map((nm, i) => ({ name: nm.length > 13 ? `${nm.slice(0, 12)}…` : nm, cls: GCLS[i], values: data[i] })),
      { xmin: lo - pad, xmax: hi + pad, grand: A.grand, rowH: A.k > 4 ? 40 : 50, r: 5.5 });
    drawF($('#calcF'), { d1: A.dfb, d2: A.dfw, alpha: a, F: A.F, h: 220 });
  }

  let timer;
  box.addEventListener('input', e => {
    const row = e.target.closest('.g-row');
    if (!row) return;
    const g = st.groups[+row.dataset.i];
    if (e.target.classList.contains('g-name')) g.name = e.target.value; else g.text = e.target.value;
    clearTimeout(timer); timer = setTimeout(compute, 180);
  });
  box.addEventListener('click', e => {
    const b = e.target.closest('.icon-del');
    if (!b || b.disabled) return;
    st.groups.splice(+b.closest('.g-row').dataset.i, 1);
    rows(); compute();
  });
  $('#calcAdd').addEventListener('click', () => {
    st.groups.push({ name: `Group ${'ABCDEFGH'[st.groups.length]}`, text: '' });
    rows(); compute();
    $$('.g-vals', box).pop().focus();
  });
  $('#calcChallenge').addEventListener('click', () => { st.groups = fromSet(CHALLENGE); rows(); compute(); });
  $('#calcReset').addEventListener('click', () => { st.groups = fromSet(CACHE); rows(); compute(); });
  seg($('#calcAlpha'), st.alpha, v => { st.alpha = v; compute(); });
  RENDERS.push(compute);
  rows(); compute();
})();

/* =========================================================
   Exit ticket
   ========================================================= */
(function exitTicket() {
  const ta = $('#exitText');
  ta.value = store.exit || '';
  ta.addEventListener('input', () => { store.exit = ta.value; save(); });
  $('#exitShow').addEventListener('click', () => { $('#exitModel').hidden = false; });
})();

/* =========================================================
   Navigation, progress, theme
   ========================================================= */
(function nav() {
  const links = $$('#toc a');
  const targets = links.map(a => document.querySelector(a.getAttribute('href'))).filter(Boolean);
  const mark = id => {
    links.forEach(a => {
      const on = a.getAttribute('href') === `#${id}`;
      a.classList.toggle('active', on);
      if (store.visited.includes(a.getAttribute('href').slice(1))) a.classList.add('visited');
    });
    if (!store.visited.includes(id)) { store.visited.push(id); save(); }
  };
  links.forEach(a => { if (store.visited.includes(a.getAttribute('href').slice(1))) a.classList.add('visited'); });

  if ('IntersectionObserver' in window) {
    const io = new IntersectionObserver(entries => {
      entries.filter(e => e.isIntersecting).forEach(e => mark(e.target.id));
    }, { rootMargin: '-30% 0px -60% 0px' });
    targets.forEach(t => io.observe(t));
  }

  const bar = $('#readBar');
  const onScroll = () => {
    const h = document.documentElement;
    bar.style.width = `${(h.scrollTop / Math.max(1, h.scrollHeight - h.clientHeight)) * 100}%`;
  };
  addEventListener('scroll', onScroll, { passive: true });
  onScroll();

  const menu = $('#menuBtn');
  const setOpen = o => { document.body.classList.toggle('nav-open', o); menu.setAttribute('aria-expanded', o); };
  menu.addEventListener('click', () => setOpen(!document.body.classList.contains('nav-open')));
  $('#scrim').addEventListener('click', () => setOpen(false));
  links.forEach(a => a.addEventListener('click', () => setOpen(false)));

  $('#resetBtn').addEventListener('click', () => {
    if (!confirm('Clear all your answers and progress on this page?')) return;
    try { localStorage.removeItem(KEY); } catch (e) { /* ignore */ }
    location.reload();
  });
})();

// Redraw the plots when the layout switches between phone and desktop width
(function redrawOnResize() {
  let was = innerWidth < 700, timer;
  addEventListener('resize', () => {
    clearTimeout(timer);
    timer = setTimeout(() => {
      const now = innerWidth < 700;
      if (now !== was) { was = now; RENDERS.forEach(r => r()); }
    }, 150);
  });
})();

(function theme() {
  const root = document.documentElement;
  if (store.theme) root.dataset.theme = store.theme;
  $('#themeBtn').addEventListener('click', () => {
    const dark = root.dataset.theme ? root.dataset.theme === 'dark' : matchMedia('(prefers-color-scheme: dark)').matches;
    root.dataset.theme = dark ? 'light' : 'dark';
    store.theme = root.dataset.theme; save();
  });
})();
