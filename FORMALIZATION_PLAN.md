# Formalization Plan: Induced Lorentzian Polynomials

This document outlines the step-by-step plan to formalize the results of the "Induced Lorentzian polynomials" paper in Lean 4. Since you are relatively new to Lean, we will break the project down into manageable, logical milestones.

## User Review Required
Before writing any code, please review the steps below. Once you approve, I will automatically copy this plan into a `FORMALIZATION_PLAN.md` file in your main folder so you have it as a permanent reference, and I will generate the boilerplate code in `IndLorPoly/Basic.lean`.

## Open Questions
> [!IMPORTANT]
> - Do you want to prove the Lorentzian properties entirely from scratch, or assume some definitions as `axiom`s first to focus on the combinatorial $\mathcal{S}$-matching part? (Mathlib doesn't yet have a comprehensive library for Lorentzian polynomials, so we will need to define what it means for a polynomial to be Lorentzian).
> - Would you prefer to model the bipartite graph $\Gamma_{\mathcal{S}}$ using matrices (easier for algebraic manipulation) or using actual graphs from `Mathlib.Combinatorics.SimpleGraph`?

## Proposed Changes

### 1. Setup Boilerplate (Basic.lean)
We will add standard Mathlib imports and set up the namespaces and basic variables (`m`, `n`, `S`) used throughout the paper.

#### [MODIFY] `IndLorPoly/Basic.lean`
We will set up the foundational definitions:
- Fix types for $m$ and $n$ (usually using `Fin m` and `Fin n`).
- Define the sequence $\mathcal{S}$ as a function from `Fin n` to `Finset (Fin m)`.

### 2. Milestone 1: Combinatorial Definitions (Matchings)
Before doing any polynomials, we define the combinatorics.
- **Transversals and Matchings**: Define a matching between a subset $T \subseteq [n]$ and $B \subseteq [m]$.
- **The $C_T(\mathcal{S})$ Function**: Define $C_T(\mathcal{S})$ as the cardinality of the set of such valid subsets $B$.
- **$\mathcal{S}$-matching**: Define the condition $\alpha \overset{\mathcal{S}}{\longleftrightarrow} \beta$ mathematically. This can be elegantly defined using matrices of weights $W \in \mathbb{Z}_{\ge 0}^{m \times n}$ where row sums are $\alpha$ and column sums are $\beta$.

### 3. Milestone 2: Algebraic Definitions (Polynomials)
- **Multivariate Polynomials**: Use `Mathlib.Algebra.MvPolynomial.Basic` to define polynomials over $\mathbb{R}$.
- **Generating Functions**: Define $f_{\mathcal{S}, r} = \sum_{T} C_T(\mathcal{S}) y^T$.
- **The Inducing Operator $\mathcal{I}_{\mathcal{S}}$**: Define this as a linear map from $\mathbb{R}[x_1, \dots, x_m] \to \mathbb{R}[y_1, \dots, y_n]$. This is tricky in Lean but manageable using `LinearMap`.

### 4. Milestone 3: Lorentzian and Volume Polynomials
- **Lorentzian Definition**: Translate the definition of Lorentzian polynomials from [BH20] into Lean.
- **Volume Polynomial Definition**: Translate the definition from [GHMSW2025].

### 5. Milestone 4: Proving the Theorems
- **Theorem 1.2 (Symbol of $\mathcal{I}_{\mathcal{S}}$)**: Prove that the symbol of the operator is a realizable volume polynomial.
- **Theorem 1.1**: Conclude that $f_{\mathcal{S},r}$ is Lorentzian.

## Verification Plan

### Automated Tests
- Lean provides continuous compilation. The ultimate verification is that all definitions type-check and the final `theorem` statements compile without using `sorry`.

### Manual Verification
- We will iteratively check the definitions by writing small `#eval` or `example` blocks to ensure the mathematical definitions behave as expected on small examples (e.g., $m=2$, $n=2$).
