# Sharp Favard decay with uniform marginals

Sergiu Alexandru Bîsceanu

Divide the bottom edge of the unit square into $n$ equal intervals and join each to an interval of the same width on the top. How small can the area covered by the resulting parallelograms be? The minimum is of order $1/\log n$, both when the top intervals slide freely and when they permute the equal grid. Already at $n=2$ the minima differ. They are $1/\sqrt 2$ and $3/4$, respectively.

[Read the five-page paper](permutation-strips.pdf) · [LaTeX source](permutation-strips.tex) · [Lean certification of Theorem 1](PermutationStrips/Conjecture.lean#L340)

## What Lean proves

For the attained minima $\beta_n$ (sliding tops) and $\alpha_n$ (permuted tops), Lean proves the matching $1/\log n$ bounds and the two leading lower bounds
$$
\liminf_{n\to\infty}(\log n)\beta_n\ge 2,\qquad
\liminf_{n\to\infty}(\log n)\alpha_n\ge \pi^2/4.
$$
The formalization uses the Lebesgue area of the union of the actual strips. Its upper proof repeatedly chooses a shuffle whose area saving pays for its number of pieces, then transfers the result to the equal grid. [Theorem statements](PermutationStrips/Conjecture.lean#L338) · [Upper construction](PermutationStrips/FiniteUpper.lean) · [Leading lower bounds](PermutationStrips/Weighted.lean)

The paper also determines the sharp angular loss at each scale and constructs one compact set realizing the bounds at all scales. Theorem 2’s full proof is in the paper. Its Lean components include the [scale selection](PermutationStrips/Schedule.lean), [sampling estimate](PermutationStrips/Sampling.lean), [critical weight integral](PermutationStrips/Profile.lean), and [grid matching from uniform marginals](PermutationStrips/Matching.lean).

## Reproduce the check

With [elan](https://lean-lang.org/install/) installed, run these commands from the repository root.

```sh
lake exe cache get
lake build
```

The project pins Lean and mathlib to v4.24.0. The default build checks all public declarations in the project against the axiom allowlist of `propext`, `Classical.choice`, and `Quot.sound`. [Build entry and axiom check](PermutationStrips.lean)
