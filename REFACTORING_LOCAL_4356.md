# Instructions for refactoring Isabelle proofs

## Simple cosmetic issues

Actual Greek letters α, β, γ, ... are preferable to `alpha`, `beta`, `gamma`, excluding only those (notably λ) that are already reserved. In an ε-δ proof, ε is preferable to `eps` or `e`.

The syntax ¦x¦ is preferable to `abs x`. Ditto for `floor`, `ceiling`, etc.

The functions `of_nat`, `of_int`, etc., may need a type constraint, but type-constrained variants of some exist; `real N` is always better than `(of_nat N :: real)`; there's also `real_of_nat`, etc.

Implicit type coercions are occasionally desirable: `... / real N` can usually be abbreviated to `... / N` and similarly for `of_int N * π`. 

For line breaking in proofs and formulas, assume a limit of 80 characters. Line breaking should respect the structure of the expression. 

## Eliminating needless proofs

A typical development will have either (1) a headline result and corollaries (2) a library of useful results. All desirable results should be specified using `proposition` or `theorem` (the latter for the most important). Every other result should be specified as a `lemma`, and all unused lemmas should be deleted. 

Within an individual proof, facts that do not take part in the conclusion should be deleted. 

Any lemma or local fact that is simply an instance of an existing theorem should be deleted. 

Since deletion can reveal other unused material, this step should be iterated. 

## Eliminating the clutter of unnecessary assumption/fact labels

If the proof has `using` or `from` or even `metis` / `meson` that refers to the label of the previous proof, use `then` or `with` to eliminate the reference. And if it refers to several previous labels, try to rewrite the proof using either `moreover` / `ultimately` or `also` / `finally` to eliminate those references. 

Subscripting of facts is undesirable; e.g. replace `arith_simps(63)` by the original lemma name if it exists. 

Use `assms` and `that` whenever possible, assigning labels to individual assumptions only when necessary to avoid subscripting. 

Brief facts of no more than five symbols, e.g. `T ≠ 0` or `f x ∈ A` do not need labels and can instead be referenced using cartouches. 

After carrying out these steps, unused labels should be deleted. 

## Making proofs more concise

We want to make proofs smaller 
* by making them more direct
* eliminating needless repetition  
* shortening overly long calculations

If a proof proceeds by building up a long chain of facts with trivial proofs, consider shortening the chain by combining adjacent steps. Ditto for a long `also` / `finally` chain where the separate steps are trivial.

When the *statement* of a lemma or local fact is longer (as text) than the *proof* of that fact, that lemma is a strong candidate for elimination, especially if it is used only once or twice, by incorporating its short proof into subsequent proofs to reduce the repetition of formulas; however, not if the new proof becomes significantly more complicated. 

A theorem with long and complicated assumptions or conclusions is always undesirable, especially if those formulas are repeated elsewhere. Consider whether those formulas actually describe some abstract concept, which should be captured formally using a definition or locale.

Abbreviation via `abbreviation` / `let` is valuable for avoiding repetition, but never for large formulas or with repeated arguments in the defininens. 

In any proof of the form X=Y where X or Y (presumed to be complicated) are repeated, use the abbreviation facility `(is "?lhs = ?rhs")` in the theorem/fact header. 

