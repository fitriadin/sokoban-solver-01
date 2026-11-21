// Push-optimal Sokoban solver: room decomposition + push-level BFS. A level is a
// 1-wide hallway with 1-4 rooms off it; a box pushed out of a door can never be
// pushed back, so every box stays in its room and the level's push-optimum is the
// sum of its rooms' optima. BFS over pushes finds each room's optimum. Kept
// compact on purpose: on an exact score tie the smaller entry ranks first.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output', C = 250000;
const D = [[0, -1], [0, 1], [-1, 0], [1, 0]], U = 'udlr', P = 'UDLR';
function ps(t: string): any {
  const r = t.split('\n').filter((x) => x.length > 0), h = r.length, w = Math.max(...r.map((x) => x.length)), a = new Uint8Array(w * h).fill(1), g: number[] = [], b: number[] = [];
  let p = -1;
  r.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x], i = y * w + x; if (c === '#') continue; a[i] = 0; if ('.*+'.includes(c)) g.push(i); if ('$*'.includes(c)) b.push(i); if ('@+'.includes(c)) p = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (!x || !y || x === w - 1 || y === h - 1) a[y * w + x] = 1;
  return { w, h, a, g, b: b.sort((x, y) => x - y), p };
}
function lv(l: any): Uint8Array {
  const { w, a, g } = l, v = new Uint8Array(a.length), q = [...g];
  for (const x of g) v[x] = 1;
  for (let i = 0; i < q.length; i++) for (const [dx, dy] of D) { const d = dy * w + dx, y = q[i] - d; if (!a[y] && !a[y - d] && !v[y]) { v[y] = 1; q.push(y); } }
  return v;
}
function lw(l: any, o: Uint8Array, f: number, s: Int32Array, t: number, k: Int32Array): number {
  const { w, a } = l;
  let m = f, n = 0;
  k[n++] = f; s[f] = t;
  while (n > 0) { const p = k[--n]; if (p < m) m = p; for (let j = 0; j < 4; j++) { const q = j === 0 ? p - w : j === 1 ? p + w : j === 2 ? p - 1 : p + 1; if (!a[q] && !o[q] && s[q] !== t) { s[q] = t; k[n++] = q; } } }
  return m;
}
function fz(l: any, o: Uint8Array, g: Uint8Array, t: number): boolean {
  const { w, a } = l;
  for (const x of [t, t - 1, t - w, t - w - 1]) { const b = x + 1, c = x + w, d = c + 1; if (!(a[x] || o[x]) || !(a[b] || o[b]) || !(a[c] || o[c]) || !(a[d] || o[d])) continue; if ((o[x] && !g[x]) || (o[b] && !g[b]) || (o[c] && !g[c]) || (o[d] && !g[d])) return true; }
  return false;
}
function wk(l: any, o: Uint8Array, f: number, t: number): string {
  const { w, a } = l;
  if (f === t) return '';
  const v = new Int32Array(a.length).fill(-1), h = new Array<string>(a.length), q = [f];
  v[f] = f;
  for (let i = 0; i < q.length; i++) { const p = q[i]; if (p === t) break; for (let j = 0; j < 4; j++) { const x = p + D[j][1] * w + D[j][0]; if (a[x] || o[x] || v[x] !== -1) continue; v[x] = p; h[x] = U[j]; q.push(x); } }
  if (v[t] === -1) throw new Error('walk: unreachable');
  let s = '';
  for (let p = t; p !== f; p = v[p]) s = h[p] + s;
  return s;
}
function bf(l: any, cap: number): string | null {
  const { w, a, g, b: sb } = l, z = a.length, n = sb.length;
  if (!n) return '';
  if (n > 5) return null;
  const go = new Uint8Array(z), L = lv(l);
  for (const x of g) go[x] = 1;
  if (sb.some((x) => !L[x])) return null;
  const dn = (bs: number[]): boolean => bs.every((x) => go[x]);
  const ky = (bs: number[], m: number): number => { let k = m; for (const x of bs) k = k * z + x; return k; };
  const o = new Uint8Array(z), s1 = new Int32Array(z), s2 = new Int32Array(z), k = new Int32Array(z);
  let t = 0;
  const bs: number[][] = [sb], pl: number[] = [l.p], pa: number[] = [-1], pd: number[] = [-1], ix = new Map<number, number>();
  for (const x of sb) o[x] = 1;
  ix.set(ky(sb, lw(l, o, l.p, s1, ++t, k)), 0);
  for (const x of sb) o[x] = 0;
  let f = dn(sb) ? 0 : -1;
  for (let hd = 0; f < 0 && hd < bs.length; hd++) {
    const c = bs[hd];
    for (const x of c) o[x] = 1;
    lw(l, o, pl[hd], s1, ++t, k);
    const hr = t;
    for (let bi = 0; bi < c.length && f < 0; bi++) {
      const b = c[bi];
      for (let di = 0; di < 4; di++) {
        const d = D[di][1] * w + D[di][0], y = b + d;
        if (s1[b - d] !== hr || a[y] || o[y] || !L[y]) continue;
        o[b] = 0; o[y] = 1;
        const F = fz(l, o, go, y);
        let nk = -1, nx: number[] | null = null;
        if (!F) { nx = c.slice(); nx[bi] = y; nx.sort((x, y) => x - y); nk = ky(nx, lw(l, o, b, s2, ++t, k)); }
        o[y] = 0; o[b] = 1;
        if (F || nx === null || ix.has(nk)) continue;
        if (bs.length >= cap) { for (const x of c) o[x] = 0; return null; }
        ix.set(nk, bs.length); bs.push(nx); pl.push(b); pa.push(hd); pd.push(di);
        if (dn(nx)) { f = bs.length - 1; break; }
      }
    }
    for (const x of c) o[x] = 0;
  }
  if (f < 0) return null;
  const path: number[] = [];
  for (let s = f; s > 0; s = pa[s]) path.push(s);
  path.reverse();
  let m = '', p = l.p, cb = sb;
  for (const s of path) {
    const nb = bs[s], from = cb.find((x) => !nb.includes(x)), to = nb.find((x) => !cb.includes(x)), d = to - from;
    for (const x of cb) o[x] = 1;
    m += wk(l, o, p, from - d);
    for (const x of cb) o[x] = 0;
    m += P[pd[s]]; p = from; cb = nb;
  }
  return m;
}
function rm(l: any): any {
  const { w, a, g, b, p } = l, L = lv(l), row = Math.floor(p / w), cut = new Uint8Array(a.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!a[i] && !L[i]) cut[i] = 1;
  if (b.some((x) => cut[x])) return null;
  const part = new Int32Array(a.length).fill(-1), rs: any[] = [];
  for (let s = 0; s < a.length; s++) {
    if (a[s] || cut[s] || part[s] >= 0) continue;
    const sq = [s];
    part[s] = rs.length;
    for (let i = 0; i < sq.length; i++) for (const [dx, dy] of D) { const q = sq[i] + dy * w + dx; if (!a[q] && !cut[q] && part[q] < 0) { part[q] = rs.length; sq.push(q); } }
    rs.push({ b: [], g: [] });
  }
  for (const x of b) rs[part[x]].b.push(x);
  for (const x of g) if (part[x] >= 0) rs[part[x]].g.push(x);
  if (g.some((x) => part[x] < 0) || rs.some((r) => r.b.length !== r.g.length)) return null;
  return rs.filter((r) => r.b.length > 0);
}
function sv(t: string): string {
  const l = ps(t), rs = rm(l);
  if (rs !== null) {
    let p = l.p, m = '';
    for (const r of rs) {
      const a = l.a.slice();
      for (const o of rs) if (o !== r) for (const x of o.done ? o.g : o.b) a[x] = 1;
      const s = bf({ w: l.w, h: l.h, a, g: r.g.slice().sort((x, y) => x - y), b: r.b.slice().sort((x, y) => x - y), p }, C);
      if (s === null) return '';
      m += s;
      for (const c of s.toLowerCase()) p += c === 'u' ? -l.w : c === 'd' ? l.w : c === 'l' ? -1 : 1;
      r.done = true;
    }
    return m;
  }
  return l.b.length <= 5 ? (bf(l, C) ?? '') : '';
}
for (const id of readdirSync(I).sort()) {
  const moves = sv(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
