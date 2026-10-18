"""Small symbolic worksheet. Run directly, or paste into a Jupyter cell."""
import sympy as sp

sp.init_printing()
t = sp.symbols('t', nonnegative=True)
omega = sp.symbols('omega', positive=True)
y = 1 - (1 + omega*t)*sp.exp(-omega*t)
equation = sp.Eq(sp.Function('y')(t), y)
try:
    from IPython.display import display
except ImportError:
    display = sp.pprint
display(equation)
display(sp.Eq(sp.Symbol('y_prime'), sp.diff(y, t)))
assert sp.simplify(sp.diff(y, t, 2) + 2*omega*sp.diff(y, t) + omega**2*y - omega**2) == 0
assert y.subs(t, 0) == 0
assert sp.diff(y, t).subs(t, 0) == 0
print('The differential equation and initial values match symbolically.')
print('LaTeX:', sp.latex(equation))
