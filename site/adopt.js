const form = document.querySelector('#benefit-form');
const result = document.querySelector('#benefit-output');
function updateBenefit() {
  const inputs = ['share', 'reduction', 'overhead'].map(id => document.getElementById(id));
  if (inputs.some(input => input.value === '' || !input.checkValidity())) {
    result.textContent = 'Enter values between 0 and 100.';
    return;
  }
  const [share, reduction, overhead] = inputs.map(input => Number(input.value) / 100);
  const saved = 100 * (share * reduction - overhead);
  result.textContent = saved >= 0
    ? `Illustrative: ${saved.toFixed(2)}% less total latency.`
    : `Illustrative: ${(-saved).toFixed(2)}% more total latency.`;
}
form.addEventListener('input', updateBenefit);
form.addEventListener('submit', event => event.preventDefault());
updateBenefit();
