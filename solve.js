// Fast drop-in for makefun-diff 1.0.0: run({ old, new }) returns the same patch string, byte for byte,
// computed with integer line ids and typed-array Myers search instead of linked path objects.

const KEEP = 0;
const DEL = 1;
const INS = 2;
const CONTEXT = 3;

// Cut a text into lines after every "\n"; a trailing fragment without "\n" is a line too.
function splitLines(text) {
  const lines = [];
  const len = text.length;
  let start = 0;
  while (start < len) {
    const nl = text.indexOf('\n', start);
    if (nl === -1) {
      lines.push(text.slice(start));
      break;
    }
    lines.push(text.slice(start, nl + 1));
    start = nl + 1;
  }
  return lines;
}

// Give every distinct line (newline included in identity) a small integer id, shared by both texts.
function internLines(aLines, bLines) {
  const map = new Map();
  const aIds = new Int32Array(aLines.length);
  const bIds = new Int32Array(bLines.length);
  let next = 0;
  for (let i = 0; i < aLines.length; i++) {
    const line = aLines[i];
    let id = map.get(line);
    if (id === undefined) {
      id = next++;
      map.set(line, id);
    }
    aIds[i] = id;
  }
  for (let i = 0; i < bLines.length; i++) {
    const line = bLines[i];
    let id = map.get(line);
    if (id === undefined) {
      id = next++;
      map.set(line, id);
    }
    bIds[i] = id;
  }
  return [aIds, bIds];
}

// Myers greedy search over the middle slices A and B (integer ids).
// Returns merged runs [[kind, count], ...] with the reference choices:
// furthest into the old text wins, deletion wins ties, no edge pruning,
// a move past either end is not a candidate, snakes run as far as lines match.
// Positions here are counts of lines consumed (x old, y new, diagonal k = x - y).
function middleRuns(A, B) {
  const N = A.length;
  const M = B.length;
  if (N === 0) return M > 0 ? [[INS, M]] : [];
  if (M === 0) return [[DEL, N]];

  // d = 0: the snake from the origin along diagonal 0.
  let x0 = 0;
  while (x0 < N && x0 < M && A[x0] === B[x0]) x0++;
  if (x0 >= N && x0 >= M) return x0 > 0 ? [[KEEP, x0]] : [];

  const maxEdit = N + M;
  const offset = maxEdit + 1;
  const V = new Int32Array(2 * maxEdit + 3).fill(-1);
  V[offset] = x0;
  // Per diagonal, the longest stretch [snakeLo, snakeHi) already verified line-equal on it.
  // A later landing inside the stretch jumps straight to its end instead of rescanning.
  const snakeLo = new Int32Array(2 * maxEdit + 3);
  const snakeHi = new Int32Array(2 * maxEdit + 3);
  snakeHi[offset] = x0;
  // One flat history buffer: level d starts at histOff[d] and holds, per diagonal,
  // (landingX + 1) * 2 + (deletion ? 0 : 1); 0 means no path.
  let histBuf = new Int32Array(1 << 16);
  const histOff = new Int32Array(maxEdit + 2);
  let histUsed = 0;
  let D = -1;

  outer: for (let d = 1; d <= maxEdit; d++) {
    histOff[d] = histUsed;
    if (histUsed + d + 1 > histBuf.length) {
      const bigger = new Int32Array(Math.max(histBuf.length * 2, histUsed + d + 1));
      bigger.set(histBuf);
      histBuf = bigger;
    }
    let hIdx = histUsed;
    histUsed += d + 1;
    let idx = offset - d;
    for (let k = -d; k <= d; k += 2, idx += 2, hIdx++) {
      const vDel = V[idx - 1];
      const vIns = V[idx + 1];
      const delX = vDel >= 0 && vDel < N ? vDel + 1 : -1;
      const insX = vIns >= 0 && vIns - (k + 1) < M ? vIns : -1;
      if (delX < 0 && insX < 0) {
        V[idx] = -1;
        continue;
      }
      let landing;
      let isDel;
      if (delX >= insX) {
        landing = delX;
        isDel = true;
      } else {
        landing = insX;
        isDel = false;
      }
      let x = landing;
      let y = x - k;
      const hi = snakeHi[idx];
      if (x >= snakeLo[idx] && x < hi) {
        y += hi - x;
        x = hi;
      }
      while (x < N && y < M && A[x] === B[y]) {
        x++;
        y++;
      }
      if (x > landing) {
        const lo = snakeLo[idx];
        if (landing <= hi && x >= lo) {
          if (landing < lo) snakeLo[idx] = landing;
          if (x > hi) snakeHi[idx] = x;
        } else if (x - landing > hi - lo) {
          snakeLo[idx] = landing;
          snakeHi[idx] = x;
        }
      }
      V[idx] = x;
      histBuf[hIdx] = (landing + 1) * 2 + (isDel ? 0 : 1);
      if (x >= N && y >= M) {
        D = d;
        break outer;
      }
    }
  }
  if (D < 0) throw new Error('diff search ended without reaching both ends');

  // Walk the recorded landings back from (N, M) to the origin, collecting runs in reverse.
  const rev = [];
  let cx = N;
  let ck = N - M;
  for (let d = D; d >= 1; d--) {
    const val = histBuf[histOff[d] + ((ck + d) >> 1)];
    const landing = (val >> 1) - 1;
    const isDel = (val & 1) === 0;
    const snake = cx - landing;
    if (snake > 0) rev.push([KEEP, snake]);
    if (isDel) {
      rev.push([DEL, 1]);
      cx = landing - 1;
      ck -= 1;
    } else {
      rev.push([INS, 1]);
      cx = landing;
      ck += 1;
    }
  }
  if (cx > 0) rev.push([KEEP, cx]);
  rev.reverse();

  const runs = [];
  for (const [kind, count] of rev) {
    const last = runs[runs.length - 1];
    if (last !== undefined && last[0] === kind) last[1] += count;
    else runs.push([kind, count]);
  }
  return runs;
}

function writtenLine(op, line) {
  return line.charCodeAt(line.length - 1) === 10 ? op + line : op + line + '\n%\n';
}

export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  const aLines = splitLines(input.old);
  const bLines = splitLines(input.new);
  const n = aLines.length;
  const m = bLines.length;
  const [aIds, bIds] = internLines(aLines, bLines);

  let prefix = 0;
  while (prefix < n && prefix < m && aIds[prefix] === bIds[prefix]) prefix++;
  let suffix = 0;
  while (suffix < n - prefix && suffix < m - prefix && aIds[n - 1 - suffix] === bIds[m - 1 - suffix]) suffix++;

  const runs = [];
  const pushRun = (kind, count) => {
    if (count <= 0) return;
    const last = runs[runs.length - 1];
    if (last !== undefined && last[0] === kind) last[1] += count;
    else runs.push([kind, count]);
  };
  pushRun(KEEP, prefix);
  for (const [kind, count] of middleRuns(aIds.subarray(prefix, n - suffix), bIds.subarray(prefix, m - suffix))) {
    pushRun(kind, count);
  }
  pushRun(KEEP, suffix);

  // Group the edit runs into change stretches between kept lines.
  const co = [];
  const cp = [];
  const cd = [];
  const ci = [];
  let o = 0;
  let p = 0;
  let deleted = 0;
  let inserted = 0;
  for (const [kind, count] of runs) {
    if (kind === KEEP) {
      o += count;
      p += count;
      continue;
    }
    let last = co.length - 1;
    if (last < 0 || co[last] + cd[last] !== o || cp[last] + ci[last] !== p) {
      co.push(o);
      cp.push(p);
      cd.push(0);
      ci.push(0);
      last++;
    }
    if (kind === DEL) {
      cd[last] += count;
      o += count;
      deleted += count;
    } else {
      ci[last] += count;
      p += count;
      inserted += count;
    }
  }

  // Hunks: change stretches at most 2 * CONTEXT kept lines apart share one.
  const hunks = [];
  for (let i = 0; i < co.length; i++) {
    const h = hunks[hunks.length - 1];
    if (h !== undefined) {
      const prev = h[h.length - 1];
      if (co[i] - (co[prev] + cd[prev]) <= 2 * CONTEXT) {
        h.push(i);
        continue;
      }
    }
    hunks.push([i]);
  }

  const out = [`makefun-diff/1 old=${n} new=${m} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`];
  for (const h of hunks) {
    const first = h[0];
    const last = h[h.length - 1];
    const oldStart = Math.max(0, co[first] - CONTEXT);
    const newStart = cp[first] - (co[first] - oldStart);
    const after = Math.min(CONTEXT, n - (co[last] + cd[last]));
    const oldEnd = co[last] + cd[last] + after;
    const newEnd = cp[last] + ci[last] + after;
    out.push(`@ ${oldStart + 1} ${oldEnd - oldStart} ${newStart + 1} ${newEnd - newStart}\n`);
    let at = oldStart;
    for (const c of h) {
      while (at < co[c]) {
        out.push(writtenLine('=', aLines[at]));
        at++;
      }
      for (let i = 0; i < cd[c]; i++) out.push(writtenLine('-', aLines[co[c] + i]));
      for (let i = 0; i < ci[c]; i++) out.push(writtenLine('+', bLines[cp[c] + i]));
      at = co[c] + cd[c];
    }
    while (at < oldEnd) {
      out.push(writtenLine('=', aLines[at]));
      at++;
    }
  }
  return out.join('');
}
