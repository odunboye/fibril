/* Progressive enhancement: reading/search works offline, without a framework. */
(() => {
  'use strict';
  document.body.classList.add('js');
  const root = document.documentElement;
  const article = document.querySelector('article');
  const theme = document.querySelector('#theme');
  const menu = document.querySelector('#menu');
  const input = document.querySelector('#search');
  const results = document.querySelector('#search-results');
  const outline = document.querySelector('#outline-links');
  const base = new URL(document.body.dataset.root, location.href);
  const read = key => { try { return localStorage.getItem(key); } catch { return null; } };
  const save = (key, value) => { try { localStorage.setItem(key, value); } catch {} };
  const savedTheme = read('fibril-theme');
  if (['light', 'dark'].includes(savedTheme)) root.dataset.theme = savedTheme;
  let size = Number(read('fibril-font-size')) || 20;
  const applySize = () => root.style.setProperty('--reading-size', `${size}px`);
  applySize();
  theme.hidden = false;
  theme.addEventListener('click', () => {
    const dark = root.dataset.theme === 'dark' || (!root.dataset.theme && matchMedia('(prefers-color-scheme: dark)').matches);
    root.dataset.theme = dark ? 'light' : 'dark';
    save('fibril-theme', root.dataset.theme);
    theme.setAttribute('aria-label', `Switch to ${dark ? 'dark' : 'light'} theme`);
  });
  for (const [id, delta] of [['smaller', -1], ['larger', 1]]) {
    const button = document.getElementById(id);
    button.hidden = false;
    button.addEventListener('click', () => {
      size = Math.min(23, Math.max(15, size + delta));
      applySize(); save('fibril-font-size', String(size));
    });
  }
  menu.hidden = false;
  const closeMenu = () => { document.body.classList.remove('menu-open'); menu.setAttribute('aria-expanded', 'false'); };
  menu.addEventListener('click', () => {
    const open = document.body.classList.toggle('menu-open');
    menu.setAttribute('aria-expanded', String(open));
  });
  document.addEventListener('keydown', event => {
    if (event.key === 'Escape') { closeMenu(); menu.focus(); }
    if (event.key === '/' && !['INPUT', 'TEXTAREA'].includes(document.activeElement.tagName) && !event.ctrlKey && !event.metaKey && !event.altKey) {
      event.preventDefault(); document.body.classList.add('menu-open');
      menu.setAttribute('aria-expanded', 'true'); input.focus();
    }
  });
  document.querySelector('main').addEventListener('click', closeMenu);
  for (const heading of article.querySelectorAll('h2[id]')) {
    const link = document.createElement('a');
    link.href = `#${heading.id}`; link.textContent = heading.textContent;
    outline.append(link);
  }
  if (!outline.children.length) document.querySelector('.outline').hidden = true;
  const words = article.textContent.trim().split(/\s+/).length;
  document.querySelector('.reading-meta').textContent = `${Math.max(1, Math.ceil(words / 220))} min read · Implementation notebook`;
  for (const table of article.querySelectorAll('table')) {
    const wrapper = document.createElement('div');
    wrapper.className = 'table-scroll'; wrapper.tabIndex = 0;
    wrapper.setAttribute('role', 'region'); wrapper.setAttribute('aria-label', 'Scrollable reference table');
    table.before(wrapper); wrapper.append(table);
  }
  if (!document.body.classList.contains('source-page')) {
    for (const pre of article.querySelectorAll('pre')) {
      const code = pre.querySelector('code'); if (!code) continue;
      const button = document.createElement('button');
      button.className = 'copy-code'; button.textContent = 'Copy';
      button.setAttribute('aria-label', 'Copy code block');
      button.addEventListener('click', async () => {
        try { await navigator.clipboard.writeText(code.textContent); button.textContent = 'Copied!'; }
        catch { button.textContent = 'Select text to copy'; }
      });
      pre.prepend(button);
    }
  }
  const progress = document.querySelector('.progress');
  const updateProgress = () => {
    const distance = document.documentElement.scrollHeight - innerHeight;
    progress.style.width = `${distance > 0 ? Math.min(100, scrollY / distance * 100) : 100}%`;
  };
  addEventListener('scroll', updateProgress, {passive: true});
  addEventListener('resize', updateProgress); updateProgress();
  document.querySelector('#search-box').hidden = false;
  input.addEventListener('input', () => {
    results.replaceChildren();
    const query = input.value.trim().toLowerCase();
    if (query.length < 2) return;
    const terms = query.split(/\s+/);
    const matches = (window.FIBRIL_SEARCH || []).filter(page => terms.every(term => `${page.title} ${page.text}`.toLowerCase().includes(term)));
    const summary = document.createElement('p'); summary.textContent = `${matches.length} pages found`; results.append(summary);
    for (const page of matches.slice(0, 8)) {
      const link = document.createElement('a'); link.href = new URL(page.url, base).href;
      const title = document.createElement('strong'); title.textContent = page.title;
      const snippet = document.createElement('small');
      const position = Math.max(0, page.text.toLowerCase().indexOf(terms[0]) - 45);
      snippet.textContent = `${position ? '…' : ''}${page.text.slice(position, position + 150)}…`;
      link.append(title, snippet); results.append(link);
    }
  });
})();
