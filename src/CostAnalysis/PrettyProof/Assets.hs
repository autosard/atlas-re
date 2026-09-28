{-# LANGUAGE QuasiQuotes #-}

-- | Static stylesheet and script of the proof viewer. The page itself only
-- carries the proof as JSON; @proof.js@ renders it.
--
-- Note: these are shakespeare text templates, so the sequences hash-brace,
-- at-brace and caret-brace must not occur in them.
module CostAnalysis.PrettyProof.Assets
  ( css
  , js
  ) where

import Data.Text.Lazy (Text)
import Text.Shakespeare.Text (lt)

css :: Text
css = [lt|:root {
  --bg: #F4F3EE;
  --panel: #FFFFFF;
  --panel-2: #F7F6F2;
  --line: #DDDAD0;
  --line-2: #EFEDE6;
  --ink: #1D1F23;
  --ink-2: #3D4047;
  --muted: #5E6168;
  --core: #B42318;
  --core-bg: #FDECEA;
  --core-row: #FDF3F1;
  --core-line: #E8B4AE;
  --good: #1F6B3A;
  --sel: #E6EDF7;
  --accent: #1F5FAD;
  --struct-bg: #EFEEE8; --struct: #3D4047;
  --sub-bg: #FFF1D6; --sub: #7A4B00;
  --call-bg: #E6EEF9; --call: #1B4F8F;
  --const-bg: #E7F2EA; --const: #245B33;
  --fn-bg: #1D1F23; --fn: #FFFFFF;
  --code-bg: #1D1F23; --code: #D5D7DC; --code-muted: #7D8189; --code-hl: #3A2A2A; --code-mark: #F08A7E;
  --sans: 'IBM Plex Sans', system-ui, -apple-system, 'Segoe UI', sans-serif;
  --mono: 'IBM Plex Mono', ui-monospace, 'SFMono-Regular', Menlo, Consolas, monospace;
  color-scheme: light;
}

@media (prefers-color-scheme: dark) {
  :root {
    --bg: #16181C;
    --panel: #1E2126;
    --panel-2: #23262C;
    --line: #33373E;
    --line-2: #2A2E34;
    --ink: #E6E7EA;
    --ink-2: #C9CCD2;
    --muted: #A3A7AF;
    --core: #FF8A7A;
    --core-bg: #3A1F1C;
    --core-row: #2B1D1C;
    --core-line: #6B2F29;
    --good: #7FD19B;
    --sel: #1F3047;
    --accent: #7FB0F0;
    --struct-bg: #2C2F35; --struct: #C9CCD2;
    --sub-bg: #3A2E14; --sub: #F2C77A;
    --call-bg: #1C2D44; --call: #9CC3F5;
    --const-bg: #1C3324; --const: #93D3A7;
    --fn-bg: #E6E7EA; --fn: #16181C;
    --code-bg: #0F1114; --code-hl: #3A2424;
    color-scheme: dark;
  }
}

* { box-sizing: border-box; }
html, body { margin: 0; height: 100%; }
body { background: var(--bg); color: var(--ink); font: 13px/1.45 var(--sans); }
code, .mono { font-family: var(--mono); font-size: 12px; }
button { font: inherit; color: inherit; }
button:focus-visible, input:focus-visible, summary:focus-visible { outline: 2px solid var(--accent); outline-offset: 1px; }
.muted { color: var(--muted); }
.small { font-size: 12px; }

#app { height: 100vh; display: grid; grid-template-rows: auto minmax(0, 1fr); grid-template-columns: minmax(0, 1fr); }

header#hdr { display: flex; align-items: center; gap: 14px; padding: 0 20px; min-height: 52px; flex-wrap: wrap;
  background: var(--panel); border-bottom: 1px solid var(--line); }
.brand { font-family: var(--mono); font-weight: 500; font-size: 16px; letter-spacing: 0.02em; }
.sep { color: var(--muted); }
.file { font-family: var(--mono); white-space: nowrap; }
.pill { padding: 3px 10px; border-radius: 999px; font-weight: 600; font-size: 12px; letter-spacing: 0.04em; }
.pill.bad { background: var(--core); color: var(--panel); }
.pill.good { background: var(--good); color: var(--panel); }
.legend { margin-left: auto; display: flex; gap: 14px; color: var(--muted); font-size: 12px; }
.legend span { display: flex; align-items: center; gap: 6px; }

.cols { display: flex; min-height: 0; min-width: 0; }
#left { width: 300px; flex-shrink: 0; overflow: auto; padding: 16px; border-right: 1px solid var(--line);
  display: flex; flex-direction: column; gap: 22px; }
#mid { flex: 1; min-width: 0; display: flex; flex-direction: column; }
#detail { width: 460px; flex-shrink: 0; overflow: auto; padding: 18px 20px; background: var(--panel);
  border-left: 1px solid var(--line); display: flex; flex-direction: column; gap: 18px; }

h2, h3 { margin: 0; font-size: 11px; font-weight: 600; letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); }
section { display: flex; flex-direction: column; gap: 8px; }
.sechead { display: flex; align-items: center; gap: 8px; }
.sechead .right { margin-left: auto; }
label { display: flex; align-items: center; gap: 6px; cursor: pointer; font-size: 12px; color: var(--ink-2); }

.card { display: flex; flex-direction: column; gap: 6px; width: 100%; text-align: left; cursor: pointer;
  background: var(--panel); border: 1px solid var(--line); border-radius: 8px; padding: 10px 12px; }
.card.bad { border-color: var(--core-line); }
.card.cur { box-shadow: inset 3px 0 0 var(--accent); }
.card-head { display: flex; align-items: center; gap: 8px; }
.fname { font-size: 13px; font-weight: 500; }
.status { margin-left: auto; font-size: 12px; color: var(--muted); }
.card.bad .status { color: var(--core); font-weight: 500; }
.card.ok .status { color: var(--good); }
.sig { color: var(--ink-2); overflow-wrap: anywhere; }
.kv { display: grid; grid-template-columns: 76px minmax(0, 1fr); gap: 2px 8px; font-size: 12px; }
.kv > span { color: var(--muted); }
.kv code { overflow-wrap: anywhere; }

details summary { cursor: pointer; color: var(--ink-2); font-size: 12px; }
.pots { display: flex; flex-direction: column; gap: 8px; margin-top: 8px; }
.pot-type { font-size: 12px; color: var(--muted); }
.pot-clause { display: block; padding-left: 10px; overflow-wrap: anywhere; }

.corelist { display: flex; flex-direction: column; gap: 2px; }
.coreitem { display: flex; align-items: center; gap: 8px; width: 100%; min-height: 32px; padding: 4px 8px; border: 0;
  border-radius: 6px; text-align: left; cursor: pointer; background: transparent; }
.coreitem:hover { background: var(--panel-2); }
.coreitem.cur { background: var(--sel); }
.coreitem .expr { flex: 1; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.coreitem .n { min-width: 30px; text-align: right; font-weight: 600; color: var(--core); font-size: 12px; }

#treebar { display: flex; align-items: center; gap: 10px; min-height: 48px; padding: 6px 16px; border-bottom: 1px solid var(--line); flex-wrap: wrap; }
#treebar .label { font-size: 11px; font-weight: 600; letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); }
.tabs { display: flex; gap: 6px; overflow-x: auto; max-width: 100%; }
.tab { padding: 4px 12px; min-height: 30px; border-radius: 6px; border: 1px solid var(--line); background: var(--panel);
  font-family: var(--mono); font-size: 12px; cursor: pointer; white-space: nowrap; }
.tab.cur { background: var(--ink); color: var(--bg); border-color: var(--ink); }
.toggles { margin-left: auto; display: flex; align-items: center; gap: 16px; }
.linkish { border: 0; background: none; color: var(--accent); cursor: pointer; font-size: 12px; padding: 4px 2px; }

#tree { flex: 1; overflow: auto; padding: 8px 12px 24px; }
.row { display: flex; align-items: center; gap: 2px; border-radius: 6px; width: max-content; min-width: 100%; }
.row.sel { background: var(--sel); box-shadow: inset 3px 0 0 var(--accent); }
.caret, .caret-sp { width: 24px; height: 24px; flex-shrink: 0; }
.caret { display: flex; align-items: center; justify-content: center; border: 0; background: none; cursor: pointer;
  border-radius: 4px; color: var(--muted); padding: 0; }
.caret:hover { background: var(--panel-2); }
.caret svg { transition: transform 120ms; }
.caret.open svg { transform: rotate(90deg); }
.main { flex: 1; min-width: 0; display: flex; align-items: center; gap: 10px; background: none; border: 0;
  text-align: left; padding: 5px 8px; cursor: pointer; border-radius: 6px; }
.row:not(.sel) .main:hover { background: var(--panel-2); }
.main .expr { font-size: 13px; white-space: nowrap; }
.main > * { flex-shrink: 0; }
.main > .grow { flex: 1 1 auto; min-width: 16px; }
.more { font-size: 12px; color: var(--muted); white-space: nowrap; }
.meta { display: flex; align-items: center; gap: 10px; position: sticky; right: 0; padding: 0 0 0 12px; background: var(--bg); }
.row.sel .meta { background: var(--sel); }
.row:not(.sel) .main:hover .meta { background: var(--panel-2); }
.qs, .pos { font-family: var(--mono); font-size: 12px; color: var(--muted); white-space: nowrap; }
.qs { min-width: 110px; text-align: right; }
.pos { min-width: 44px; text-align: right; }

.dot { width: 8px; height: 8px; border-radius: 50%; flex-shrink: 0; }
.dot.core { background: var(--core); }
.dot.path { border: 1.5px solid var(--core); }
.badge { flex-shrink: 0; min-width: 64px; text-align: center; padding: 1px 8px; border-radius: 999px;
  background: var(--core-bg); color: var(--core); font-size: 12px; font-weight: 600; white-space: nowrap; }
.badge.none { visibility: hidden; }

.chip { flex-shrink: 0; padding: 1px 7px; border-radius: 4px; font: 500 11px var(--mono); white-space: nowrap; }
.k-struct { background: var(--struct-bg); color: var(--struct); }
.k-sub { background: var(--sub-bg); color: var(--sub); }
.k-call { background: var(--call-bg); color: var(--call); }
.k-const { background: var(--const-bg); color: var(--const); }
.k-fn { background: var(--fn-bg); color: var(--fn); }
.jt { font: 11px var(--mono); color: var(--muted); }

.crumbs { font-family: var(--mono); font-size: 12px; color: var(--muted); overflow-wrap: anywhere; }
.dhead { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; }
.dexpr { font-size: 15px; font-weight: 500; overflow-wrap: anywhere; }
.judgement { font-family: var(--mono); font-size: 13px; color: var(--ink-2); overflow-wrap: anywhere; }
.q { font-family: var(--mono); text-decoration: underline dotted var(--muted); text-underline-offset: 3px; cursor: help; }
.vals { display: grid; grid-template-columns: auto minmax(0, 1fr); gap: 4px 8px; font-size: 12px; }
.vals code { overflow-wrap: anywhere; }

pre.src { margin: 0; background: var(--code-bg); color: var(--code); border-radius: 8px; padding: 8px 0;
  font: 12px/1.55 var(--mono); overflow-x: auto; }
pre.src .ln { display: block; white-space: pre; padding-right: 12px; }
pre.src .ln.hl { background: var(--code-hl); box-shadow: inset 3px 0 0 var(--code-mark); color: #FFFFFF; }
pre.src .no { display: inline-block; width: 44px; padding-right: 12px; text-align: right; color: var(--code-muted); user-select: none; }

table.cs { width: 100%; border-collapse: collapse; border: 1px solid var(--line); border-radius: 8px; overflow: hidden;
  font-family: var(--mono); font-size: 12px; }
table.cs th { background: var(--panel-2); color: var(--muted); font: 600 11px var(--sans); letter-spacing: 0.04em;
  text-align: left; padding: 6px 10px; }
table.cs td { padding: 4px 10px; border-top: 1px solid var(--line-2); vertical-align: top; overflow-wrap: anywhere; color: var(--muted); }
table.cs td:first-child { width: 40%; }
table.cs tr.core td { background: var(--core-row); color: var(--ink); }
table.cs tr.core td:first-child { box-shadow: inset 3px 0 0 var(--core); }
table.cs.plain td { color: var(--ink); }
table.cs.inst td:first-child { width: 64px; color: var(--muted); }
table.cs b { font-weight: 600; }
.empty { margin: 0; padding: 10px 12px; background: var(--panel-2); border-radius: 8px; color: var(--muted); }
.note { margin: 0; padding: 8px 12px; background: var(--call-bg); border-radius: 8px; font-size: 12px; color: var(--ink-2); }
.wchips { display: flex; gap: 8px; flex-wrap: wrap; }
.wchip { padding: 4px 10px; border-radius: 999px; background: var(--sub-bg); color: var(--sub); font-size: 12px; }
.wchip b { font-weight: 600; }
.monolist { margin: 8px 0 0; padding: 0; list-style: none; font-family: var(--mono); font-size: 12px; display: flex; flex-direction: column; gap: 2px; }

@media (max-width: 1100px) {
  #app { height: auto; }
  .cols { flex-direction: column; }
  #left, #detail { width: auto; border: 0; border-bottom: 1px solid var(--line); }
  #tree { max-height: 70vh; }
  .qs { display: none; }
}
|]

js :: Text
js = [lt|(function () {
  'use strict';
  var D = JSON.parse(document.getElementById('proof-data').textContent);
  var NL = String.fromCharCode(10);
  var unsat = D.result === 'unsat';
  var fns = D.functions;
  var byId = new Map();
  var CHEVRON = '<svg width="12" height="12" viewBox="0 0 12 12" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4.5 2.5 8 6l-3.5 3.5"/></svg>';

  function $(id) { return document.getElementById(id); }
  function esc(s) {
    return String(s == null ? '' : s).split('&').join('&amp;').split('<').join('&lt;')
      .split('>').join('&gt;').split('"').join('&quot;');
  }
  function preorder(n, f) { f(n); n.kids.forEach(function (k) { preorder(k, f); }); }

  function index(n, parent, fi) {
    n.parent = parent; n.fn = fi; byId.set(n.id, n);
    var size = 1, path = n.core > 0;
    n.kids.forEach(function (k) { index(k, n, fi); size += k.size; path = path || k.path; });
    n.size = size; n.path = path;
  }
  fns.forEach(function (f, i) { index(f.tree, null, i); });

  var coreNodes = [];
  fns.forEach(function (f) { preorder(f.tree, function (n) { if (n.core > 0) coreNodes.push(n); }); });

  var S = { fn: 0, sel: fns.length ? fns[0].tree.id : null, open: new Set(),
            onlyCore: false, foldLet: true, coreRows: false };
  if (unsat) {
    fns.forEach(function (f) {
      preorder(f.tree, function (n) {
        if (n.kids.some(function (k) { return k.path; })) S.open.add(n.id);
      });
    });
    if (coreNodes.length) { S.sel = coreNodes[0].id; S.fn = coreNodes[0].fn; }
  } else {
    fns.forEach(function (f) { S.open.add(f.tree.id); });
  }

  function kindClass(k) {
    if (k === 'fn') return 'k-fn';
    if (k === 'sub') return 'k-sub';
    if (k === 'app' || k === 'tick') return 'k-call';
    if (k === 'const') return 'k-const';
    return 'k-struct';
  }
  function chip(n) {
    return '<span class="chip ' + kindClass(n.kind) + '">' + esc(n.rule) + '</span>' +
      (n.jt ? '<span class="jt">' + esc(n.jt) + '</span>' : '');
  }
  function posText(n) { return n.pos ? n.pos[0] + ':' + n.pos[1] : ''; }
  function total(n) { return n.rows.length + n.hidden; }
  function nodeLabel(n) { return n.kind === 'fn' ? fns[n.fn].name : n.expr; }

  function qRef(id) {
    if (id == null) return '';
    var t = D.templates[String(id)];
    var title = t ? t.terms.map(function (term, i) {
      return t.vals ? term + ' : ' + t.vals[i] : term;
    }).join(NL) : '';
    return '<span class="q" title="' + esc(title) + '">Q' + id + '</span>';
  }
  function boundText(id) {
    var t = id == null ? null : D.templates[String(id)];
    if (!t || !t.vals) return null;
    var out = '';
    t.terms.forEach(function (term, i) {
      var v = t.vals[i];
      if (v === '0' || v === '?') return;
      var neg = v.charAt(0) === '−';
      var mag = neg ? v.slice(1) : v;
      var body = term === '1' ? mag : (mag === '1' ? term : mag + '·' + term);
      out += out ? (neg ? ' − ' : ' + ') + body : (neg ? '−' : '') + body;
    });
    return out || '0';
  }

  // Header ------------------------------------------------------------------

  function renderHeader() {
    var h = '<span class="brand">atlas</span>';
    if (D.file) h += '<span class="sep">/</span><span class="file" title="' + esc(D.file) + '">' + esc(D.file.split('/').slice(-2).join('/')) + '</span>';
    h += '<span class="pill ' + (unsat ? 'bad' : 'good') + '">' + (unsat ? 'UNSAT' : 'SAT') + '</span>';
    if (unsat) {
      h += '<span class="muted">Unsat core spans ' + coreNodes.length + ' rule' + (coreNodes.length === 1 ? '' : 's') + '</span>';
      h += '<span class="legend"><span><span class="dot core"></span>in core</span><span><span class="dot path"></span>on path to core</span></span>';
    } else if (D.objective) {
      h += '<span class="muted">objective <code>' + esc(D.objective) + '</code></span>';
    }
    $('hdr').innerHTML = h;
  }

  // Left column -------------------------------------------------------------

  function renderLeft() {
    var h = '<section><h2>Functions</h2>';
    fns.forEach(function (f, i) {
      var nCore = 0;
      preorder(f.tree, function (n) { if (n.core > 0) nCore++; });
      var status = unsat ? (nCore ? nCore + ' rule' + (nCore === 1 ? '' : 's') + ' in core' : 'not in core') : 'proved';
      h += '<button type="button" class="card' + (nCore ? ' bad' : (unsat ? '' : ' ok')) + (i === S.fn ? ' cur' : '') + '" data-fn="' + i + '">';
      h += '<span class="card-head"><code class="fname">' + esc(f.name) + '</code><span class="status">' + status + '</span></span>';
      if (f.args) {
        var pre = f.pre != null ? f.pre : 'Q' + f.from;
        var post = f.post != null ? f.post : 'Q' + f.to;
        h += '<code class="sig">(' + esc(f.args.join(', ')) + ') | ' + esc(pre) + ' → ' + esc(post) + '</code>';
      }
      if (f.cost != null || f.size) {
        h += '<span class="kv">';
        if (f.cost != null) h += '<span>amortised</span><code>' + esc(f.cost) + '</code>';
        if (f.size) h += '<span>size</span><code>' + esc(f.size) + '</code>';
        h += '</span>';
      }
      h += '</button>';
    });
    h += '</section>';

    if (D.potentials.length) {
      h += '<section><details><summary>Potential functions</summary><div class="pots">';
      D.potentials.forEach(function (p) {
        h += '<div><div class="pot-type">' + esc(p.type) + '</div>';
        p.clauses.forEach(function (c) {
          h += '<code class="pot-clause">𝜙(' + esc(c[0]) + ') = ' + esc(c[1]) + '</code>';
        });
        h += '</div>';
      });
      h += '</div></details></section>';
    }

    if (unsat && coreNodes.length) {
      h += '<section><div class="sechead"><h2>Unsat core</h2><span class="muted small">click to jump</span></div>';
      h += '<nav class="corelist" aria-label="Rules in the unsat core">';
      coreNodes.forEach(function (n) {
        h += '<button type="button" class="coreitem' + (n.id === S.sel ? ' cur' : '') + '" data-core="' + n.id + '">' +
          chip(n) + '<code class="expr">' + esc(nodeLabel(n)) + '</code>' +
          '<span class="pos">' + posText(n) + '</span><span class="n">' + n.core + '</span></button>';
      });
      h += '</nav></section>';
    }
    $('left').innerHTML = h;
  }

  // Tree --------------------------------------------------------------------

  function checkbox(key, label) {
    return '<label><input type="checkbox" data-key="' + key + '"' + (S[key] ? ' checked' : '') + '>' + label + '</label>';
  }

  function renderBar() {
    var h = '<span class="label">Derivation</span><div class="tabs" role="tablist">';
    fns.forEach(function (f, i) {
      h += '<button type="button" role="tab" aria-selected="' + (i === S.fn) + '" class="tab' + (i === S.fn ? ' cur' : '') + '" data-fn="' + i + '">' + esc(f.name) + '</button>';
    });
    h += '</div><div class="toggles">';
    if (unsat) h += checkbox('onlyCore', 'Only path to core');
    h += checkbox('foldLet', 'Fold let bindings');
    h += '<button type="button" class="linkish" data-act="expand">Expand all</button>';
    h += '<button type="button" class="linkish" data-act="collapse">Collapse all</button></div>';
    $('treebar').innerHTML = h;
  }

  function hasVisibleKids(n) {
    return n.kids.some(function (k) { return !S.onlyCore || k.path; });
  }

  function rowHtml(n, depth) {
    var open = S.open.has(n.id);
    var kids = hasVisibleKids(n);
    var sel = n.id === S.sel;
    var h = '<div class="row' + (sel ? ' sel' : '') + '" role="treeitem" aria-level="' + (depth + 1) + '"' +
      (kids ? ' aria-expanded="' + open + '"' : '') + ' aria-selected="' + sel + '" data-id="' + n.id +
      '" style="padding-left:' + (4 + depth * 16) + 'px">';
    h += kids
      ? '<button type="button" class="caret' + (open ? ' open' : '') + '" data-act="toggle" tabindex="-1" aria-label="' + (open ? 'Collapse' : 'Expand') + '">' + CHEVRON + '</button>'
      : '<span class="caret-sp"></span>';
    h += '<button type="button" class="main" data-act="select"' + (sel ? '' : ' tabindex="-1"') + '>';
    h += '<span class="dot' + (n.core > 0 ? ' core' : (unsat && n.path ? ' path' : '')) + '"></span>';
    h += chip(n) + '<code class="expr">' + esc(nodeLabel(n)) + '</code>';
    if (kids && !open) h += '<span class="more">' + (n.size - 1) + ' rules' + (unsat && !n.path ? ', none in core' : '') + '</span>';
    h += '<span class="grow"></span><span class="meta">';
    h += '<span class="qs">' + (n.qi != null ? 'Q' + n.qi + ' → Q' + n.qo : '') + '</span>';
    h += '<span class="pos">' + posText(n) + '</span>';
    if (unsat) h += '<span class="badge' + (n.core > 0 ? '' : ' none') + '">' + (n.core > 0 ? n.core + ' / ' + total(n) : '') + '</span>';
    return h + '</span></button></div>';
  }

  function renderTree() {
    var f = fns[S.fn];
    var out = [];
    function walk(n, depth) {
      if (S.onlyCore && !n.path) return;
      var hide = S.foldLet && n.kind === 'let';
      if (!hide) out.push(rowHtml(n, depth));
      if (!hide && !S.open.has(n.id)) return;
      n.kids.forEach(function (k) { walk(k, hide ? depth : depth + 1); });
    }
    if (f) walk(f.tree, 0);
    $('tree').innerHTML = out.length ? out.join('') : '<p class="empty">No rules to show.</p>';
  }

  // Detail ------------------------------------------------------------------

  function renderDetail() {
    var n = byId.get(S.sel);
    var el = $('detail');
    if (!n) { el.innerHTML = '<p class="empty">Select a rule in the derivation.</p>'; return; }
    var crumbs = [];
    for (var a = n.parent; a; a = a.parent) crumbs.unshift(nodeLabel(a));

    var h = '<div>' + (crumbs.length ? '<div class="crumbs">' + esc(crumbs.join('  ›  ')) + '</div>' : '');
    h += '<div class="dhead">' + chip(n) + '<code class="dexpr">' + esc(nodeLabel(n)) + '</code>' +
      (n.core > 0 ? '<span class="badge">' + n.core + ' / ' + total(n) + ' in core</span>' : '') + '</div>';
    if (n.qi != null) {
      h += '<div class="judgement">' + qRef(n.qi) + '  ⊢  ' + esc(n.expr) + '  |  ' + qRef(n.qo) + '</div>';
    }
    h += '</div>';

    var vals = '';
    [n.qi, n.qo].forEach(function (q, i) {
      if (q == null || (i === 1 && q === n.qi)) return;
      var b = boundText(q);
      if (b != null) vals += qRef(q) + '<code>= ' + esc(b) + '</code>';
    });
    if (vals) h += '<section><h3>Values</h3><div class="vals">' + vals + '</div></section>';

    var src = n.file && D.sources ? D.sources[n.file] : null;
    if (n.pos) {
      var line = n.pos[0];
      h += '<section><h3>Source · line ' + line + ', column ' + n.pos[1] + (n.derived ? ' (derived)' : '') + '</h3>';
      if (src) {
        var from = Math.max(1, line - 4), to = Math.min(src.length, line + 4);
        h += '<pre class="src">';
        for (var i = from; i <= to; i++) {
          h += '<span class="ln' + (i === line ? ' hl' : '') + '"><span class="no">' + i + '</span>' + esc(src[i - 1]) + '</span>';
        }
        h += '</pre>';
      } else {
        h += '<p class="empty">Source text is not embedded in this proof.</p>';
      }
      h += '</section>';
    }

    var rows = n.rows.filter(function (r) { return !S.coreRows || r[4]; });
    h += '<section><div class="sechead"><h3>Constraints</h3><span class="muted small">' + n.rows.length +
      (n.hidden ? ' + ' + n.hidden + ' k ≥ 0' : '') + '</span>';
    if (unsat) h += '<span class="right">' + checkbox('coreRows', 'Core rows only') + '</span>';
    h += '</div>';
    if (rows.length) {
      var shown = rows.slice(0, 500);
      h += '<table class="cs' + (unsat ? '' : ' plain') + '"><thead><tr><th>Term</th><th>Constraint</th></tr></thead><tbody>';
      shown.forEach(function (r) {
        h += '<tr' + (r[4] ? ' class="core"' : '') + '><td>' + esc(r[0]) + '</td><td>' + esc(r[1]) +
          (r[2] ? ' <b>' + esc(r[2]) + '</b> ' + esc(r[3]) : '') + '</td></tr>';
      });
      h += '</tbody></table>';
      if (rows.length > shown.length) h += '<p class="muted small">' + (rows.length - shown.length) + ' more rows not shown.</p>';
      var abbrev = rows.some(function (r) { return r[3].indexOf('[·]') >= 0 || r[3].indexOf('Σ') >= 0; });
      if (abbrev) h += '<p class="note">[·] stands for the row’s own term in the other template. Σ n k is a sum of n weakening variables; they are listed below.</p>';
    } else {
      h += '<p class="empty">' + (n.rows.length ? 'No core rows.' : 'This rule adds no constraints of its own.') + '</p>';
    }
    if (n.hidden) h += '<p class="muted small">' + n.hidden + ' side conditions k ≥ 0 on weakening variables are not listed.</p>';
    h += '</section>';

    var w = n.weak;
    if (w && (w.mono.length || w.ax.length)) {
      h += '<section><h3>Weakening variables</h3><div class="wchips">' +
        '<span class="wchip"><b>' + w.mono.length + '</b> mono comparisons</span>' +
        '<span class="wchip"><b>' + w.ax.length + '</b> axiom instances</span></div>';
      if (w.ax.length) {
        h += '<table class="cs plain inst"><thead><tr><th>Var</th><th>Instance</th></tr></thead><tbody>';
        w.ax.forEach(function (x) {
          h += '<tr><td>k' + x[0] + '</td><td>' + esc(x[1]) + ' <b>≤</b> ' + esc(x[2]) + '</td></tr>';
        });
        h += '</tbody></table>';
      }
      if (w.mono.length) {
        h += '<details><summary>Show mono comparisons</summary><ul class="monolist">';
        w.mono.slice(0, 500).forEach(function (x) {
          h += '<li><span class="muted">k' + x[0] + '</span>  ' + esc(x[1]) + ' ≤ ' + esc(x[2]) + '</li>';
        });
        if (w.mono.length > 500) h += '<li class="muted">' + (w.mono.length - 500) + ' more</li>';
        h += '</ul></details>';
      }
      h += '</section>';
    }
    el.innerHTML = h;
  }

  // Interaction -------------------------------------------------------------

  function focusSelected() {
    var b = $('tree').querySelector('.row.sel .main');
    if (b) { b.focus(); b.scrollIntoView({ block: 'nearest' }); }
  }

  function select(n, reveal) {
    var fnChanged = n.fn !== S.fn;
    S.sel = n.id;
    if (reveal) {
      S.fn = n.fn;
      for (var a = n.parent; a; a = a.parent) S.open.add(a.id);
    }
    if (fnChanged) renderBar();
    renderLeft();
    renderTree();
    renderDetail();
    if (reveal) {
      var r = $('tree').querySelector('.row.sel');
      if (r) r.scrollIntoView({ block: 'center' });
    }
  }

  function selectFn(i) {
    S.fn = i;
    S.sel = fns[i].tree.id;
    renderBar(); renderLeft(); renderTree(); renderDetail();
  }

  $('tree').addEventListener('click', function (e) {
    var b = e.target.closest('[data-act]');
    if (!b) return;
    var n = byId.get(Number(b.closest('.row').dataset.id));
    if (b.dataset.act === 'toggle') {
      if (S.open.has(n.id)) S.open.delete(n.id); else S.open.add(n.id);
      renderTree();
    } else {
      select(n, false);
    }
  });

  $('tree').addEventListener('keydown', function (e) {
    var rows = Array.prototype.slice.call($('tree').querySelectorAll('.row'));
    var idx = rows.findIndex(function (r) { return Number(r.dataset.id) === S.sel; });
    if (idx < 0) return;
    var n = byId.get(S.sel);
    var target = null;
    if (e.key === 'ArrowDown' && idx + 1 < rows.length) target = byId.get(Number(rows[idx + 1].dataset.id));
    else if (e.key === 'ArrowUp' && idx > 0) target = byId.get(Number(rows[idx - 1].dataset.id));
    else if (e.key === 'ArrowRight' && hasVisibleKids(n)) {
      if (!S.open.has(n.id)) { S.open.add(n.id); renderTree(); focusSelected(); e.preventDefault(); return; }
      if (idx + 1 < rows.length) target = byId.get(Number(rows[idx + 1].dataset.id));
    } else if (e.key === 'ArrowLeft') {
      if (S.open.has(n.id) && hasVisibleKids(n)) { S.open.delete(n.id); renderTree(); focusSelected(); e.preventDefault(); return; }
      target = n.parent;
    } else {
      return;
    }
    e.preventDefault();
    if (target) { select(target, false); focusSelected(); }
  });

  $('left').addEventListener('click', function (e) {
    var core = e.target.closest('[data-core]');
    if (core) { select(byId.get(Number(core.dataset.core)), true); return; }
    var card = e.target.closest('[data-fn]');
    if (card) selectFn(Number(card.dataset.fn));
  });

  $('treebar').addEventListener('click', function (e) {
    var tab = e.target.closest('[data-fn]');
    if (tab) { selectFn(Number(tab.dataset.fn)); return; }
    var act = e.target.closest('[data-act]');
    if (!act) return;
    var root = fns[S.fn].tree;
    if (act.dataset.act === 'expand') preorder(root, function (n) { if (n.kids.length) S.open.add(n.id); });
    else { preorder(root, function (n) { S.open.delete(n.id); }); S.open.add(root.id); }
    renderTree();
  });

  function onToggle(e) {
    var key = e.target.dataset && e.target.dataset.key;
    if (!key) return;
    S[key] = e.target.checked;
    if (key === 'coreRows') renderDetail(); else renderTree();
  }
  $('treebar').addEventListener('change', onToggle);
  $('detail').addEventListener('change', onToggle);

  renderHeader();
  renderLeft();
  renderBar();
  renderTree();
  renderDetail();
  var first = $('tree').querySelector('.row.sel');
  if (first) first.scrollIntoView({ block: 'center' });
})();
|]
