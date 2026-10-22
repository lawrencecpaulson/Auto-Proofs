# Stokes

This AFP entry contains one Isabelle session, `Stokes`, based on the AFP
`Smooth_Manifolds` session. Its `ROOT` lists all 33 theories and builds the
article in `document/root.tex`.

The development proves Stokes' theorem for compactly supported near-top
coordinate form families on oriented smooth half-space atlases. It defines
chart-independent body and boundary integrals using finite smooth partitions
of unity and proves their equality by local half-space Stokes and gluing.
It also develops a one-dimensional exact-form theorem and proves a concrete
two-chart instance for the closed unit disk. The Green-form theorem identifies
the local coordinate sign; it does not state Green's theorem using ordinary
planar area and contour integrals.

The principal results are in:

- `BoundaryIntegration/Global_Gluing.thy`: global Stokes and corollaries.
- `One_Dimensional_Integration.thy`: the one-dimensional integral.
- `BoundaryIntegration/Disk_Stokes.thy`: the closed disk instance.
- `BoundaryIntegration/Green_Form.thy`: the Green-form coordinate identity.

When this directory is placed alongside `Smooth_Manifolds` in an AFP theories
tree, build and check the document with:

```sh
isabelle build -d ../Smooth_Manifolds -D . -o document=pdf
```
