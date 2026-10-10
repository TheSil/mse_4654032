# Sum of squares modulo n

For every integer **n ≥ 2**,

```math
\sum_{\ell=0}^{n-1}(\ell^2\bmod n)
=\frac{n(n-m)}{2}
-2n\sum_{\substack{\Delta<0\text{ a discriminant}\\\Delta\mid n}}
\frac{h(\Delta)}{w(\Delta)},
```

where $m^2$ is the largest square dividing $n$, and $h(\Delta)$ and $w(\Delta)$ are the class number and unit count of the quadratic order of discriminant $\Delta$.

- [Proof.lean](Proof.lean): complete Lean 4 proof, without `sorry` or custom axioms.
- [proof.pdf](proof.pdf): mathematical exposition.
- [proof.tex](proof.tex): LaTeX source.
- [formula.gp](formula.gp): PARI/GP implementation and comparison with the direct sum.

## Lean formalization

In the namespace `SquareResidue`, the final theorem covers every positive `n`:

```lean
theorem closed_formula (n : ℕ) [NeZero n] :
    ↑(residueSum n) =
      (↑n * (↑n - ↑(squarePart n)) / 2 -
        2 * ↑n * ∑ M ∈ discriminantDivisors n,
          classRatio (-(M : ℤ)) : ℝ)
```

Here `↑` denotes a cast, and `classRatio Δ` is `h(Δ) / w(Δ)`. The formula is evaluated in `ℝ`. The project uses Lean and Mathlib **4.34.0**.

From the repository directory, download Mathlib's precompiled files, then build the Lean proof:

```sh
lake exe cache get
lake build
```
