# Stokes

This staged AFP entry contains one Isabelle session, `Stokes`, based on the
AFP `Smooth_Manifolds` session. It proves Stokes' theorem for compactly
supported near-top coordinate form families on oriented smooth half-space
atlases. Chart-independent body and boundary integrals are defined using
finite smooth partitions of unity and proved equal by local half-space Stokes
and gluing.

The session also develops a one-dimensional exact-form theorem and proves a
concrete two-chart instance for the closed unit disk. The Green-form theorem
identifies the local coordinate sign. The separate staged entry
`Green_Cauchy_Pompeiu` imports this session for shared local integration and
cutoff results.

Principal results are in `BoundaryIntegration/Global_Gluing.thy`,
`One_Dimensional_Integration.thy`, `BoundaryIntegration/Disk_Stokes.thy`, and
`BoundaryIntegration/Green_Form.thy`. The session builds its PDF document
from `document/root.tex`.
