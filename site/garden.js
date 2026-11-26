// Renders garden.json as a grid of plants. No framework, no build step.
(async function () {
  const $ = (id) => document.getElementById(id);
  const esc = (s) => String(s ?? '').replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

  let g;
  try {
    // Local server: /garden.json beside the page. GitHub Pages (repo root):
    // the page is /site/, the data one level up.
    let res = await fetch('garden.json', { cache: 'no-store' });
    if (!res.ok) res = await fetch('../garden.json', { cache: 'no-store' });
    g = await res.json();
  } catch (e) {
    $('count').innerHTML = '<span class="error">Could not load garden.json. Run node scripts/garden.mjs.</span>';
    return;
  }

  const pct = g.total ? Math.round((g.proved / g.total) * 100) : 0;
  $('count').innerHTML = `<b>${g.proved}</b> of ${g.total} proved`;
  $('meta').textContent = `${g.toolchain.replace('leanprover/lean4:', 'Lean ')} · build ${g.build.ok ? 'ok' : 'failing'} · ${new Date(g.generatedAt).toLocaleString()}`;
  const bar = $('bar');
  bar.setAttribute('aria-valuemax', g.total);
  bar.setAttribute('aria-valuenow', g.proved);
  requestAnimationFrame(() => { bar.firstElementChild.style.width = Math.max(pct, g.proved ? 2 : 0) + '%'; });
  $('thm-count').textContent = `${pct}% in bloom`;
  if (g.repo) $('repo').href = g.repo;

  const prose = (s) => esc(s).replace(/`([^`]+)`/g, '<code>$1</code>');
  for (const p of g.plants) p.title = p.title.replace(/^Lemma:\s*/i, '');
  const titleOf = new Map(g.plants.map((p) => [p.id, p.title]));

  // A small Lean highlighter: comments, strings, keywords, tactics, numbers.
  const KEYWORDS = new Set('theorem lemma def abbrev instance structure inductive where namespace section end open import variable fun λ let have show from by at with match if then else do return calc private protected noncomputable universe Type Prop Sort'.split(' '));
  const TACTICS = new Set('intro intros exact apply refine rw rwa simp simp_all omega induction cases rcases obtain constructor rfl decide unfold assumption contradiction exfalso use exists left right specialize generalize subst trivial ring norm_num linarith nlinarith calc repeat first try all_goals any_goals case next split by_cases by_contra absurd congr ext funext show change conv injection nofun nomatch'.split(' '));
  function highlight(code) {
    const re = /(\/-[\s\S]*?-\/|--[^\n]*)|("(?:\\.|[^"\\])*")|\b(sorry)\b|([A-Za-z_][\w'.!?]*)|(\b\d+\b)/g;
    let out = '', last = 0, m;
    while ((m = re.exec(code))) {
      out += esc(code.slice(last, m.index));
      const [t, comment, str, sorry, word, num] = m;
      if (comment) out += `<span class="c">${esc(t)}</span>`;
      else if (str) out += `<span class="s">${esc(t)}</span>`;
      else if (sorry) out += `<span class="sorry">${esc(t)}</span>`;
      else if (word && KEYWORDS.has(word)) out += `<span class="k">${esc(t)}</span>`;
      else if (word && TACTICS.has(word)) out += `<span class="t">${esc(t)}</span>`;
      else if (num) out += `<span class="n">${esc(t)}</span>`;
      else out += esc(t);
      last = m.index + t.length;
    }
    return out + esc(code.slice(last));
  }

  // The Lean web editor, with this plant and everything it needs pasted in.
  const tryUrl = (p) => p.bundle ? 'https://live.lean-lang.org/#code=' + encodeURIComponent(p.bundle) : null;

  function trust(p) {
    if (p.status !== 'proved') return `<div class="trust growing-note">${esc(p.reason || 'Not proved yet')}</div>`;
    const axioms = [...new Set(p.decls.flatMap((d) => d.axioms || []))];
    return `<div class="trust"><span class="tick">✓</span> Checked by Lean · no <code>sorry</code> · ${
      axioms.length ? 'axioms: ' + axioms.map((a) => `<code>${esc(a)}</code>`).join(' ') : 'no axioms'}</div>`;
  }

  // Who grew it: the HiveOp agent named on the PR that removed the last sorry.
  function credit(p) {
    const v = p.provenance;
    if (p.status !== 'proved' || !v) return '';
    const who = v.agent ? `Proved by <b>${esc(v.agent)}</b>, a HiveOp agent` : 'Proved by a HiveOp agent';
    return `<div class="credit"><span aria-hidden="true">🌱</span> ${who} · <a href="${esc(v.url)}" target="_blank" rel="noopener">PR #${esc(v.pr)} ↗</a></div>`;
  }

  function card(p) {
    const proved = p.status === 'proved';
    const d = p.decls[0] || {};
    const needs = p.dependsOn?.length ? 'needs ' + p.dependsOn.map((id) => titleOf.get(id) || id).join(', ') : '';
    const code = p.decls.map((x) => x.code).filter(Boolean).join('\n\n');
    const sides = p.kind === 'theorem' ? p.decls.map((x) => `
      <div class="sides">
        <div class="side"><div class="label">In maths</div><p class="math">${prose(x.doc)}</p></div>
        <div class="side"><div class="label">In Lean</div><pre class="stmt">${highlight(x.statement)}</pre></div>
      </div>`).join('') : '';
    const url = tryUrl(p);
    return `<article class="card ${proved ? 'proved' : 'growing'}">
      <div class="card-top">
        <div class="pot" aria-hidden="true">${proved ? '✓' : '⏳'}</div>
        <div>
          <div class="title">${prose(p.title)}</div>
          <div class="status" title="${esc(p.reason || '')}">${proved ? 'Proved' : 'Growing'}</div>
        </div>
      </div>
      <p class="blurb">${prose(p.kind === 'lemma' ? (d.doc || p.blurb) : p.blurb)}</p>
      ${sides}
      ${trust(p)}
      ${credit(p)}
      ${code ? `<details class="proof"><summary>${proved ? 'Show the proof' : 'Show the open goal'}</summary><pre class="code">${highlight(code)}</pre></details>` : ''}
      <div class="foot">
        <span class="needs">${esc(needs)}</span>
        <span class="links">
          ${url ? `<a class="try" href="${esc(url)}" target="_blank" rel="noopener" title="Open in the Lean web editor, with everything it needs">Try it in Lean ↗</a>` : ''}
          <a class="file" href="${esc(p.url)}" target="_blank" rel="noopener">${esc(p.file.replace(/^ProofGarden\//, ''))} ↗</a>
        </span>
      </div>
    </article>`;
  }

  const order = (a, b) => (a.status === b.status ? 0 : a.status === 'proved' ? -1 : 1);
  $('theorems').innerHTML = g.plants.filter((p) => p.kind === 'theorem').sort(order).map(card).join('');
  $('lemmas').innerHTML = g.plants.filter((p) => p.kind === 'lemma').sort(order).map(card).join('');
})();
