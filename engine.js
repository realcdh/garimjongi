/* 가림종이 — 탐지 엔진 (브라우저에서 도는 쪽)
 *
 * 이 파일은 네트워크를 쓰지 않는다. fetch도, XHR도, WebSocket도 없다.
 * 사전과 정규식은 lexicon.js, 모델 가중치는 model.js에 들어 있고 둘 다 <script>로 먼저 읽힌다.
 *
 * 파이썬 기준 구현(분석/pii_core.py)과 같은 자질을 같은 순서로 뽑는다.
 * 두 구현이 같은 문서에서 같은 구간을 내놓는지는 분석/04_eval.py가 확인한다.
 */
(function (root, factory) {
  const mod = factory(
    typeof GARIM_LEX !== 'undefined' ? GARIM_LEX : require('./lexicon.js'),
    typeof GARIM_MODEL !== 'undefined' ? GARIM_MODEL : require('./model.js')
  );
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.Garim = mod;
})(typeof self !== 'undefined' ? self : this, function (LEX, MODEL) {
  'use strict';

  const SUR = new Set(LEX.SURNAMES);
  const SUR2 = new Set(LEX.SURNAMES2);
  const GIVEN = new Set(LEX.GIVEN_SYLL);
  const COMMON = new Set(LEX.COMMON_WORDS);
  const JOSA_CH = new Set(LEX.JOSA_CHARS);
  const WORD_TAIL = new Set(LEX.WORD_TAIL || []);
  const { TITLES, PERSON_JOSA, PREV_CUES, ORG_SUFFIX } = LEX;

  const isHangul = (ch) => ch >= '가' && ch <= '힣';

  /* ── 층1: 형식이 정해진 식별자 ─────────────────────────────────── */

  function digitsOf(s) { return s.replace(/\D/g, ''); }

  function rrnValid(s) {
    const d = digitsOf(s);
    if (d.length !== 13) return false;
    const mm = +d.slice(2, 4), dd = +d.slice(4, 6);
    if (!(mm >= 1 && mm <= 12 && dd >= 1 && dd <= 31)) return false;
    if (d[6] === '0') return false;
    // 2020-10-05 이후 부여분은 뒷자리가 난수라 체크섬이 성립하지 않는다.
    // 형식이 맞으면 통과시킨다 — 놓치는 쪽보다 더 가리는 쪽이 안전한 오류다.
    return true;
  }
  function brnValid(s) {
    const d = digitsOf(s);
    if (d.length !== 10) return false;
    const w = [1, 3, 7, 1, 3, 7, 1, 3, 5];
    let sum = 0;
    for (let i = 0; i < 9; i++) sum += (+d[i]) * w[i];
    sum += Math.floor((+d[8]) * 5 / 10);
    return (10 - sum % 10) % 10 === +d[9];
  }
  function luhn(s) {
    const d = digitsOf(s);
    let sum = 0, alt = false;
    for (let i = d.length - 1; i >= 0; i--) {
      let x = +d[i];
      if (alt) { x *= 2; if (x > 9) x -= 9; }
      sum += x; alt = !alt;
    }
    return sum % 10 === 0;
  }
  const CHECKERS = {
    rrn: rrnValid,
    frn: (s) => digitsOf(s).length === 13,
    brn: brnValid,
    luhn: luhn
  };

  const RULES = LEX.RULE_SPECS.map(([kind, pattern, checker]) => ({
    kind, re: new RegExp(pattern, 'gu'), check: checker ? CHECKERS[checker] : null
  }));
  const PRIORITY = {};
  LEX.RULE_SPECS.forEach(([k], i) => { PRIORITY[k] = i; });

  function detectRules(text) {
    const hits = [];
    for (const r of RULES) {
      r.re.lastIndex = 0;
      let m;
      while ((m = r.re.exec(text)) !== null) {
        if (m[0].length === 0) { r.re.lastIndex++; continue; }
        if (r.check && !r.check(m[0])) continue;
        hits.push({ start: m.index, end: m.index + m[0].length, kind: r.kind, text: m[0] });
      }
    }
    hits.sort((a, b) => a.start - b.start
      || PRIORITY[a.kind] - PRIORITY[b.kind]
      || (b.end - b.start) - (a.end - a.start));
    const out = [];
    for (const h of hits) {
      if (out.length && h.start < out[out.length - 1].end) {
        const p = out[out.length - 1];
        const hk = [PRIORITY[h.kind], -(h.end - h.start)];
        const pk = [PRIORITY[p.kind], -(p.end - p.start)];
        if (hk[0] < pk[0] || (hk[0] === pk[0] && hk[1] < pk[1])) out[out.length - 1] = h;
        continue;
      }
      out.push(h);
    }
    return out;
  }

  /* ── 층2: 한국어 인명 ──────────────────────────────────────────── */

  function genCandidates(text) {
    const out = [];
    const n = text.length;
    let i = 0;
    while (i < n) {
      const ch = text[i];
      if (!isHangul(ch)) { i++; continue; }
      const starts = [];
      if (SUR2.has(text.slice(i, i + 2))) starts.push(2);
      if (SUR.has(ch)) starts.push(1);
      if (!starts.length) { while (i < n && isHangul(text[i])) i++; continue; }
      for (const slen of starts) {
        for (const total of [slen + 1, slen + 2, slen + 3]) {
          const seg = text.slice(i, i + total);
          if (seg.length < total) continue;
          let ok = true;
          for (const c of seg) if (!isHangul(c)) { ok = false; break; }
          if (!ok) continue;
          out.push({ start: i, end: i + total, text: seg, slen });
        }
      }
      while (i < n && isHangul(text[i])) i++;
    }
    return out;
  }

  function startsWithAny(s, arr) {
    for (const a of arr) if (s.startsWith(a)) return true;
    return false;
  }

  function features(text, c) {
    const s = c.start, e = c.end, seg = c.text, slen = c.slen, L = seg.length;
    const given = seg.slice(slen);
    const nxt = text.slice(e, e + 6);
    const prev = text.slice(Math.max(0, s - 8), s);
    const f = new Array(LEX.FEATURE_NAMES.length).fill(0);
    f[0] = L === 2 ? 1 : 0;
    f[1] = L === 3 ? 1 : 0;
    f[2] = L >= 4 ? 1 : 0;
    f[3] = SUR.has(seg[0]) ? 1 : 0;
    f[4] = slen === 2 ? 1 : 0;
    if (given.length) {
      let hit = 0;
      for (const ch of given) if (GIVEN.has(ch)) hit++;
      f[5] = hit / given.length;
    }
    f[6] = startsWithAny(nxt.replace(/^[ ·,]+/, ''), TITLES) ? 1 : 0;
    f[7] = startsWithAny(nxt, PERSON_JOSA) ? 1 : 0;
    const prevTrim = prev.replace(/[ :：·,]+$/, '');
    f[8] = PREV_CUES.some((p) => prevTrim.endsWith(p)) ? 1 : 0;
    f[9] = COMMON.has(seg) ? 1 : 0;
    f[10] = (e >= text.length || !isHangul(text[e])) ? 1 : 0;
    f[11] = (s === 0 || !isHangul(text[s - 1])) ? 1 : 0;
    f[12] = startsWithAny(nxt, ORG_SUFFIX) ? 1 : 0;
    f[13] = (prev.endsWith('(') || prev.endsWith('[') || prev.endsWith('<')) ? 1 : 0;
    f[14] = prev.endsWith(' ') ? 1 : 0;
    f[15] = (nxt.length >= 2 && JOSA_CH.has(nxt[0]) && !isHangul(nxt[1])) ? 1 : 0;
    f[16] = (L >= 3 && JOSA_CH.has(seg[seg.length - 1])) ? 1 : 0;
    f[17] = (L >= 3 && COMMON.has(seg.slice(0, -1))) ? 1 : 0;
    f[18] = WORD_TAIL.has(seg[seg.length - 1]) ? 1 : 0;
    return f;
  }

  /* 모델 추론. 신경망이면 15→8 tanh 한 층, 선형이면 내적 한 번. */
  function score(f) {
    let z;
    if (MODEL.kind === 'logreg') {
      z = MODEL.b;
      for (let i = 0; i < f.length; i++) z += f[i] * MODEL.w[i];
    } else {
      const h = new Array(MODEL.b1.length);
      for (let j = 0; j < h.length; j++) {
        let a = MODEL.b1[j];
        for (let i = 0; i < f.length; i++) a += f[i] * MODEL.W1[i][j];
        h[j] = Math.tanh(a);
      }
      z = MODEL.b2;
      for (let j = 0; j < h.length; j++) z += h[j] * MODEL.W2[j];
    }
    return 1 / (1 + Math.exp(-z));
  }

  function decode(cands, scores, threshold) {
    const order = cands.map((_, i) => i).sort((a, b) => scores[b] - scores[a]);
    const taken = [], out = [];
    for (const i of order) {
      if (scores[i] < threshold) break;
      const s = cands[i].start, e = cands[i].end;
      let clash = false;
      for (const [ts, te] of taken) if (!(e <= ts || s >= te)) { clash = true; break; }
      if (clash) continue;
      taken.push([s, e]);
      out.push({ start: s, end: e, text: cands[i].text, kind: '이름', score: scores[i] });
    }
    out.sort((a, b) => a.start - b.start);
    return out;
  }

  /* 문서 안에서 한 번 확실히 사람이었으면, 같은 글자는 그 문서 내내 사람으로 본다.
   * 씨앗 조건: 점수가 PROP_SEED 이상 + 그 자리에 사람 단서(뒤 직함 또는 앞 호칭)가 있을 것.
   * 정본은 분석/pii_core.py의 propagate()이고, 두 구현이 같은지는 분석/04_eval.py가 확인한다. */
  const PROP_SEED = 0.7;
  const I_NEXT_TITLE = LEX.FEATURE_NAMES.indexOf('next_title');
  const I_PREV_CUE = LEX.FEATURE_NAMES.indexOf('prev_cue');

  function propagate(cands, feats, scores) {
    const best = new Map();
    for (let i = 0; i < cands.length; i++) {
      if (scores[i] < PROP_SEED) continue;
      if (!(feats[i][I_NEXT_TITLE] || feats[i][I_PREV_CUE])) continue;
      const t = cands[i].text;
      if (!best.has(t) || scores[i] > best.get(t)) best.set(t, scores[i]);
    }
    if (!best.size) return scores;
    return scores.map((s, i) => Math.max(s, best.get(cands[i].text) || 0));
  }

  function findNames(text, threshold, opts) {
    const th = threshold === undefined ? MODEL.threshold : threshold;
    const cands = genCandidates(text);
    if (!cands.length) return [];
    const feats = cands.map((c) => features(text, c));
    let scores = feats.map((f) => score(f));
    if (!opts || opts.propagate !== false) scores = propagate(cands, feats, scores);
    return decode(cands, scores, th);
  }

  /* ── 합치기 ──────────────────────────────────────────────────── */

  function detect(text, opts) {
    opts = opts || {};
    const rules = detectRules(text);
    const names = opts.names === false ? [] : findNames(text, opts.threshold);
    const all = rules.concat(names).sort((a, b) => a.start - b.start || b.end - a.end);
    const out = [];
    for (const h of all) {
      if (out.length && h.start < out[out.length - 1].end) continue;  // 층1이 이긴다
      out.push(h);
    }
    return out;
  }

  /* 같은 값은 같은 딱지를 받는다. 그래야 되돌리기가 성립한다. */
  function mask(text, hits, enabledKinds) {
    const map = new Map();     // 원본 문자열 -> 딱지
    const back = new Map();    // 딱지 -> 원본 문자열
    const counter = new Map();
    let outText = '', cur = 0;
    for (const h of hits) {
      if (enabledKinds && !enabledKinds.has(h.kind)) continue;
      let tag = map.get(h.text);
      if (!tag) {
        const n = (counter.get(h.kind) || 0) + 1;
        counter.set(h.kind, n);
        tag = '[' + h.kind + n + ']';
        map.set(h.text, tag);
        back.set(tag, h.text);
      }
      outText += text.slice(cur, h.start) + tag;
      cur = h.end;
    }
    outText += text.slice(cur);
    return { text: outText, back, used: [...back.entries()].map(([tag, v]) => ({ tag, value: v })) };
  }

  function unmask(text, back) {
    let out = text;
    // 긴 딱지부터 되돌려야 [이름1]과 [이름10]이 섞이지 않는다
    const tags = [...back.keys()].sort((a, b) => b.length - a.length);
    for (const t of tags) out = out.split(t).join(back.get(t));
    return out;
  }

  return {
    detect, detectRules, findNames, mask, unmask, features, genCandidates, propagate,
    model: MODEL, lex: LEX, version: '1.0'
  };
});
