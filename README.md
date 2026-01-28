# MA4N1 Final Submission
**Project** : All Norms on $\mathbb{R}\^n$ are Equivalent

**Group** : Norms (Ben Curtis, Daniel Gerhard, Will Myles)

## Overview

The goal of our project, as laid out in the outline, was to formalise a proof that all norms on $\mathbb{R}^n$ are equivalent. We also set out to do this with minimal reliance on mathlib, where possible using only definitions of and about normed, metric and topological spaces, not lemmas and theorems. Below is an outline of our finalised project, as well as detail of a few things we thought worthy of note about it.

## The Project

## Noteworthy Points

* Throughout the project, in any statements about an arbitrary norm on $\mathbb{R}^n$, we use `(N : Seminorm $\mathbb{R}$ (Rn n))` and wherever it is required, we manually add the assumption of positive definiteness `(∀ x : Rn n, N x = 0 ↔ x = 0)`. The purpose of this is to make distinguishable statements about arbitrary norms $N(\cdot)$ from the supremum norm specifically, which Lean automatically evaluates $\lVert \cdot \rVert$ as wherever it can. This approach also comes with the added benefit of increased generality of those results for which the assumption of positive definiteness is not necessary.

* In compactness results, we use the mathlib theorem `isCompact_iff_finite_subcover`. This serves only to rewrite propositions of the form `IsCompact K` in terms of existence of finite subcovers of all open covers of $K$. This is a standard definition for compactness and the one we all have prior familiarity with. Thus we claim that using `isCompact_iff_finite_subcover` is in accordance with our minimal-mathlib-dependence goal, as it is equivalent to taking a definition from mathlib rather than relying on a pre-formalised theorem.

* There are a couple of results taken from mathlib which we might have formalised ourselves given time, but have ended up leaving as imports. These are:
  * `isOpen_pi_iff`. Details of what this states and why it was tactically chosen to be left unformalised can be found in the preamble of the lemma in which it is used - `exists_nhd_fin_cover_prod`, in `Topology/ProductSpaces.lean`.
  * `IsCompact.tendsto_subseq`. This results states that in a first-countable space, every sequence in a compact set has a convergent subsquence who's limit belongs to the compact set. I.e. in a first-countable space, compactness $\Rightarrow$ sequential compactness. This again was left as a result we take from mathlib owing to time-constraints. It is only used once throughout the project - in `compact_implies_closed` - and notably, only for the standard topology on $\mathbb{R}$, not for first-countable spaces in full generality.

* Everything else taken from mathlib (those things not discussed here or in code comments), is a basic result, not relevant to the main goal of the project. For example, set-arithmetic results like `Set.mem_iUnion`, and basic analysis results like `exists_lt_of_lt_csSup`. Formalising all such results of this kind would be unfeasible and counterproductive to purpose of the project, so they are generally used without attention being drawn to their usage. Consider this bullet point an explanation of/justification for their usage.
