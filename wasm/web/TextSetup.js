/* One self-contained helper */
async function loadPane(pane) {
  try {
    const html = await (await fetch(pane.dataset.src)).text();
    const doc  = new DOMParser().parseFromString(html, 'text/html');
    pane.innerHTML = '';                  // clear any old stuff
    pane.append(...doc.body.children);    // keep body-only
    pane.dataset.loaded = 'true';
  } catch (e) {
    pane.textContent = 'Could not load: ' + e.message;
  }
}

document.addEventListener('DOMContentLoaded', () => {
  const img = document.getElementById("blockImgDiagram")
  /* 1. Pre-fill whatever tab is active on initial load */
  const first = document.querySelector('.tab-pane.active[data-src]');
  if (first) loadPane(first);

  /* 2. Lazy-load others the first time they’re shown */
  let panes = []
  
  document.querySelectorAll('button[data-bs-toggle="tab"]').forEach(btn => {
    const targetSelector = btn.getAttribute('data-bs-target');
    const id = targetSelector.slice(1);
    const pane = document.getElementById(id);
    btn.addEventListener('shown.bs.tab', () => {
      // Check if pane has data-src attribute
      if (pane && pane.hasAttribute('data-src') && !pane.dataset.loaded) {
        loadPane(pane);
      }
      panes.forEach((value) => {
        value.style.display = value == pane? 'flex': 'none'
      })
      img.style.display = id == 'about'? "block": "none";
  });
  panes.push(pane);
});
});
