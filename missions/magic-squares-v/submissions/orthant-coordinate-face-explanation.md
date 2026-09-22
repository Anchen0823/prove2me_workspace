# Coordinate faces of orthant sections

This is a standalone theorem over any linearly ordered field and any finite coordinate type. It says that a face of the cone `L ∩ K_{≥0}^I` is precisely the part of that cone where a fixed collection of coordinates is zero. The converse is included.

The proof is assembled from `OrthantFace.lean`, `OrthantFaceSupport.lean`, and `OrthantCoordinateFace.lean`. It constructs a point inside each face whose nonzero coordinates contain those of every other point in the face, then uses face closure under coordinate support. The platform-facing statement names only Mathlib types and operations.

To construct the support witness, choose one point of the face for each coordinate that is nonzero somewhere on the face and add these finitely many points. All coordinates are nonnegative, so the sum has a zero coordinate only when every point of the face does. If a vector in the ambient cone has zeros wherever the witness does, a sufficiently small positive multiple of that vector can be subtracted from the witness while staying in the cone. The defining face property puts the vector in the face. Conversely, a positive combination of nonnegative vectors can have a zero coordinate only if both summands have that coordinate zero, which proves that every coordinate-zero section is a face.

Local verification used Lean 4.33.1. The complete proof imports only Mathlib and its axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`.
