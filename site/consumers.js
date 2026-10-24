const field = document.getElementById('field');
const relationship = document.getElementById('relationship');
function filterConsumers() {
  let count = 0;
  document.querySelectorAll('#consumers article').forEach(card => {
    card.hidden = !((field.value === 'all' || field.value === card.dataset.field)
      && (relationship.value === 'all' || relationship.value === card.dataset.route));
    if (!card.hidden) count += 1;
  });
  document.getElementById('consumer-count').textContent = `Showing ${count} opportunit${count === 1 ? 'y' : 'ies'}`;
}
field.addEventListener('change', filterConsumers);
relationship.addEventListener('change', filterConsumers);
filterConsumers();
