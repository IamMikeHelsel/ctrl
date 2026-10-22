"use strict";
const search = document.querySelector("#search");
if (search) {
  const rows = [...document.querySelectorAll("#matrix-table tbody tr")];
  const cards = [...document.querySelectorAll("#source-cards details")];
  search.addEventListener("input", () => {
    const query = search.value.toLowerCase().trim();
    [...rows, ...cards].forEach(item => { item.hidden = !item.dataset.search.includes(query); });
    const count = rows.filter(row => !row.hidden).length;
    document.querySelector("#result-count").textContent = `${count} of ${rows.length} source records`;
  });
  function revealSource() {
    const id = location.hash.slice(1);
    const card = document.getElementById(id);
    if (card && card.matches("details")) {
      if (card.hidden) {
        search.value = "";
        search.dispatchEvent(new Event("input"));
      }
      card.open = true;
    }
  }
  addEventListener("hashchange", revealSource);
  revealSource();
}
