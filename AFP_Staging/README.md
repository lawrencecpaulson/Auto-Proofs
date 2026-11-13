# Local AFP entry staging

Each directory here is intended to be a separately buildable AFP entry with
one eponymous session. The staged sessions are local dependencies for the four
main formalizations while submissions are reviewed. Build with Isabelle2026
and the matching AFP checkout. Do not copy a shared theory back into a
consumer; keep its session and qualified theory name stable.

## Staged sessions

| Entry | Role | State |
| --- | --- | --- |
| `Bounded_Integer_Kernels` | Sharp integer Siegel lemma used by GS and Roth | Session, PDF, GS, and Roth builds passed on 13 November 2026 |
| `Finite_Embedding_Bounds` | House, coordinate, and embedding kernel bounds for GS | Standalone session and PDF passed on 12 November 2026 |
| `Gelfond_Schneider` | Main transcendence theorem | Standalone session and PDF passed on 12 November 2026 |
| `Roth_Diophantine_Approximation` | Main rational Roth theorem | Standalone session and PDF passed on 12 November 2026 |
| `Bivariate_Resultants` | Bivariate specialisation, derivative multiplicity, and pair resultants | AFP-style session, PDF, browser, and outline passed on 13 November 2026 |
| `Primitive_Real_Characters` | Primitive real-character classification and fundamental discriminants | Standalone session and PDF passed on 12 November 2026 |
| `Stokes` | Manifold Stokes theorem | Standalone session and PDF passed on 12 November 2026 |
| `Green_Cauchy_Pompeiu` | Planar Green, winding, and Cauchy–Pompeiu | Standalone session and PDF passed on 12 November 2026 |

`No_Siegel` remains at `../No_Siegel` as the paper entry. Its session and PDF
passed on 12 November 2026 against the staged bivariate and character entries.
Its [`AFP_ENTRY_BOUNDARIES.md`](../No_Siegel/AFP_ENTRY_BOUNDARIES.md) records
the checked boundary between Green's note and the independent prerequisites.

## Distinctness and deferred candidates

* **Planar Green and Cauchy–Pompeiu.** The split entry has 20 theories and
  imports `Stokes_Local` and `Smooth_Cutoff` from Stokes. The existing AFP
  `Green` entry proves a type-II Green theorem for graph-bounded domains; this
  entry includes rectangular-union boundary cancellation, absolutely
  continuous winding, and Cauchy–Pompeiu formulas. The public statements
  appear distinct, but their proof arguments need an editorial overlap review
  before submission.
* **Hasse derivatives and weighted index.** Roth has a coherent four-theory
  infrastructure (`Disjoint_Index`, `Hasse_Derivative`, `Hasse_Support`,
  `Roth_Index_Count`). Assess the public interface and overlap with AFP's
  polynomial libraries before extracting it. The Wronskian and determinant
  estimates remain part of Roth's proof unless a separate application
  warrants another entry.

`Roth_Hancl_Rucki` is an integration bridge to an existing AFP theorem locale.
It is better prepared as an update or companion to that entry than presented
as an independent mathematical submission.

## Submission checks

All staged sessions have eponymous names and passed standalone builds with
PDF documents on 12 November 2026. On 13 November, the sharpened bounded
kernel entry passed with its GS and Roth consumers, and the expanded
`Bivariate_Resultants` entry passed an AFP-style session, browser, outline,
and PDF build. `No_Siegel` passed with a PDF against the revised bivariate
entry. The remaining editorial work for other entries includes source
citations, author attribution for the two kernel entries, and public-interface
and overlap reviews. Roth's optional Hasse-derivative split is deferred pending
a useful standalone theorem. `Roth_Hancl_Rucki` remains a companion candidate.
