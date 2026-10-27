# Duplication cleanup (2026-10-27)

The repeated Taylor-index proofs for rational and real coefficients are now
one polymorphic `roth_taylor_index_box` in `Hasse_Support.thy`. The finite
permutation sum proof is likewise shared through `roth_permutes_sum` in
`Roth_Wronskian.thy`.

In `Auxiliary_Index_Transfer.thy`, one local context fixes the common
approximation and balance data for the abstract, uniform, and logarithmic
gap estimates. In `Auxiliary_Polynomial.thy`, a local context fixes the
monic/root/degree/dimension/epsilon/gap data for the two staged
construction results. The named theorems still export their original
premises and conclusions.

The later forms of Roth's lemma and compact-carrier wrappers mostly
specialize the preceding result. Further predicates there would make
these specializations harder to read without eliminating substantial
proof duplication.

The Roth session and document built successfully after these changes.
