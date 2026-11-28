# Sharp Favard decay with uniform marginals

Sergiu Alexandru Bîsceanu

Divide the bottom edge of the unit square into $n$ equal intervals and join each to an interval of the same width on the top. How small can the area covered by the resulting parallelograms be? The minimum is of order $1/\log n$, both when the top intervals slide freely and when they permute the equal grid. Already at $n=2$ the minima differ. They are $1/\sqrt 2$ and $3/4$, respectively.

[Read the five-page paper](permutation-strips.pdf) · [LaTeX source](permutation-strips.tex) · [Lean proof of Theorem 1](PermutationStrips/Conjecture.lean#L340) · [Lean proof of Theorem 2](PermutationStrips/TheoremTwo.lean#L46)

## What Lean proves

For the attained minima $\beta_n$ (sliding tops) and $\alpha_n$ (permuted tops), Lean proves the matching $1/\log n$ bounds and the two leading lower bounds
$$
\liminf_{n\to\infty}(\log n)\beta_n\ge 2,\qquad
\liminf_{n\to\infty}(\log n)\alpha_n\ge \pi^2/4.
$$
The formalization uses the Lebesgue area of the union of the actual strips. Its upper proof repeatedly chooses a shuffle whose area saving pays for its number of pieces, then transfers the result to the equal grid. [Theorem statements](PermutationStrips/Conjecture.lean#L338) · [Upper construction](PermutationStrips/FiniteUpper.lean) · [Leading lower bounds](PermutationStrips/Weighted.lean)

For **Theorem 2**, Lean constructs one compact set for each admissible angular weight $b$. That same set works at every scale, has Euclidean Hausdorff length one and uniform coordinate marginals, and has zero projection length in every oblique direction. In every ball of radius $r$ centered on the set, for $0<r\le\operatorname{diam} S$, its length lies between $r/128$ and $2r$. [Theorem and all-scale bounds](PermutationStrips/TheoremTwo.lean) · [Euclidean measure and marginals](PermutationStrips/CompactAhlfors.lean#L114)

Lean proves the matching lower and upper bounds for the compact infimum and the equal-grid minimum. At the critical weight $b(r)=1/(1+\log(1/r))$, the minimum of the weighted projection supremum alone has order $(\log\log n)/\log n$. [Critical rate](PermutationStrips/TheoremTwo.lean#L104)

Lemma 3 selects $40k^3$ shuffle paths deterministically. At each mesh height it weights the next choice by the exponential of the accumulated excess. The mean section length then exceeds its target by at most $1/k$ at every mesh height, and rounding toward the center gives the angular bound at every interior height. [Exponential estimate](PermutationStrips/AngularBlockGame.lean#L73) · [Cubic path bound](PermutationStrips/AngularBlock.lean#L47) · [Geometric construction](PermutationStrips/AngularFiniteBlock.lean#L18)

## Reproduce the check

With [elan](https://lean-lang.org/install/) installed, run these commands from the repository root.

```sh
lake exe cache get
lake build
```

The project pins Lean and mathlib to v4.24.0. The default build checks all public declarations in the project against the axiom allowlist of `propext`, `Classical.choice`, and `Quot.sound`. [Build entry and axiom check](PermutationStrips.lean)
