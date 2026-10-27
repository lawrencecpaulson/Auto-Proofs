# Isabelle proof cleanup

When a proof or milestone is finished, inspect the affected development for
duplicated mathematical material before calling the cleanup complete. Look
for repeated groups of assumptions or conclusions, long formulas, and whole
or partial proof arguments. Include near duplicates with renamed variables,
different types, or a changed quantitative bound; an exact text search alone
will miss these.

Where it improves readability, name the shared mathematics with a definition,
predicate, locale, local context, or general lemma. Preserve useful theorem
statements and keep distinct estimates explicit. Prefer clarity over saving
lines, and check any refactoring with Isabelle.
