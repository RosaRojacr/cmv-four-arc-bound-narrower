# cmv-four-arc-bound-narrower

A machine-checked improvement to a constant in Cañete–Miranda–Vittone,
*Some isoperimetric problems in planes with density*, J. Geom. Anal. **20**
(2010) 243–290.

CMV's Theorem 3.16 excludes four-arc isoperimetric candidates for the strip
density once $\lambda \ge 4/\pi \approx 1.2732395$, and their Remark 3.17
notes that this bound is not optimal, the true threshold is $1/k$ with
$k = \min g$, without computing $k$. This repository formalises that
constant in Lean 4: it constructs Morgan's arc function from scratch (Mathlib
has no such thing), derives $\mathrm{arc}'(x) = 2\sin(\theta(x))$, reduces the
minimisation of $g(x) = 2\,\mathrm{arc}(x) - \mathrm{arc}(2x)$ to a single
transcendental equation, proves the resulting critical point is the global
minimum, and certifies a rational bound on it. The closed form is
$k = 3\cos\theta^{*}$, where $\theta^{*}$ is the unique root of
$3\theta - 3\sin\theta\cos\theta = \pi$, and the certified threshold is
$\lambda \ge 1.2581858$ against a sharp value of $1.2581840883\ldots$. This
narrows the open interval of Conjecture 3.12 from $(1, 1.27324)$ to
$(1, 1.25819)$. It does not resolve the conjecture: the hard end of the
interval is untouched, and everything here works inside CMV's existing proof
strategy rather than replacing it.

For the full write-up, the mathematics stated in LaTeX alongside the Lean
declarations that verify it, plus plots and a discussion of the
agentic-formal-verification workflow this was a proof of concept for — see
[Narrowing the Range](Narrowing_the_Range_-_A_proof_of_concept_for_the_Agentic-Lean_approach.pdf).

## Building

Requires Lean 4 and Mathlib (`v4.33.0-rc2`).

```bash
lake exe cache get
lake build
```

## Files

| file | contents |
|---|---|
| `MorgansArcFunction.lean` | Morgan's arc function; the identity $\mathrm{arc}'(x) = 2\sin(\theta(x))$ |
| `GFunction.lean` | $g(x) = 2\,\mathrm{arc}(x) - \mathrm{arc}(2x)$; sign of $g'$ outside $(\pi/16, \pi/8)$ |
| `Minimiser.lean` | the equation $F$, its unique root $\theta^{*}$, and $g(x^{*}) = 3\cos\theta^{*}$ |
| `MinimumValue.lean` | $x^{*}$ is the global minimum, so the bound is sharp |
| `Certificate.lean` | rational certificate; $\pi/4 < g(x)$ for all $x > 0$ |