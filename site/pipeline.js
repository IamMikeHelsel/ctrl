const decisions = document.getElementById('decision');
const domains = document.getElementById('domain');
function filterQuestions() {
  let count = 0;
  document.querySelectorAll('#questions article').forEach(card => {
    card.hidden = !((decisions.value === 'all' || decisions.value === card.dataset.decision)
      && (domains.value === 'all' || domains.value === card.dataset.domain));
    if (!card.hidden) count += 1;
  });
  document.getElementById('count').textContent = `Showing ${count} question${count === 1 ? '' : 's'}`;
}
decisions.addEventListener('change', filterQuestions);
domains.addEventListener('change', filterQuestions);
