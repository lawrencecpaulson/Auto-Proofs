# Instructions for refactoring Isabelle proofs

## Eliminating needless proofs

A typical development will have either (1) a headline result and perhaps corollaries of that result or (2) a library of useful results. All such desirable results should be specified using `proposition` or `theorem` (the latter for the most important). Everything else should be specified as a `lemma`, and all unused lemmas should be deleted from the development. 

Within an individual proof, facts that do not take part in the conclusion should be deleted. 

## Eliminating the clutter of unnecessary assumption/fact labels

* If the proof has `using` or `from` or even `metis` / `meson` that refers to the label of the previous proof, use `then` or `with` to eliminate the reference. And if it refers to several previous labels, try to rewrite the proof using either `moreover` / `ultimately` or `also` / `finally` to eliminate those references. 
* Brief facts of no more than five symbols, e.g. `T ≠ 0` or `f x ∈ A` do not need labels and can instead be referenced using cartouches. 
* After carrying out these steps, unused labels should be deleted. 

## Making proofs more concise

We want to make proofs smaller, *never* by compressing them in some cryptic way, but by eliminating needless repetition and excessively elaborate calculations. 

One way to prove a desired result is by building up a long chain of simpler facts that lead to it. Similarly, an identity or inequality might be proved by long `also` / `finally` chain. Often these chains can be made shorter by combining adjacent steps. 

The Isar structured proof language calls for the repetition of formulas being proved, which often aids readability, but can have undesirable results, e.g. if a proof has been structured into too many pieces. A particular red flag is when the *statement* of a theorem or local fact is longer (as text) than the *proof* of that fact. Such a theorem is a strong candidate for elimination, especially if it is used only once or twice, by incorporating its short proof into the other proofs. 

The other cause of excessive repetition is when some concept involving several parameters subject to various conditions is repeatedly written out. Instead that concept should be captured formally using a definition or locale.

Abbreviation via `abbreviation` / `let` is valuable for avoiding repetition, but never for large formulas or with repeated arguments in the defininens. 
