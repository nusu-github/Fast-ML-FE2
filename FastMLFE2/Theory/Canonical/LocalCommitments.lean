import Mathlib

namespace FastMLFE2.Theory.Canonical

/-!
Canonical authored commitments shared by the paper and PyMatting artifacts.
-/

inductive NeighborhoodStencil where
  | fourConnected
  deriving DecidableEq, Repr

inductive ResizeRule where
  | nearestNeighbor
  deriving DecidableEq, Repr

inductive ProjectionPlacement where
  | insideIteration
  deriving DecidableEq, Repr

inductive FixedLevelSemantics where
  | deterministicSimultaneous
  deriving DecidableEq, Repr

structure CanonicalCommitments where
  neighborhood : NeighborhoodStencil
  resize : ResizeRule
  projection : ProjectionPlacement
  fixedLevel : FixedLevelSemantics
  deriving DecidableEq, Repr

def canonicalCommitments : CanonicalCommitments where
  neighborhood := .fourConnected
  resize := .nearestNeighbor
  projection := .insideIteration
  fixedLevel := .deterministicSimultaneous

@[simp] theorem canonicalCommitments_neighborhood :
    canonicalCommitments.neighborhood = .fourConnected := rfl

@[simp] theorem canonicalCommitments_resize :
    canonicalCommitments.resize = .nearestNeighbor := rfl

@[simp] theorem canonicalCommitments_projection :
    canonicalCommitments.projection = .insideIteration := rfl

@[simp] theorem canonicalCommitments_fixedLevel :
    canonicalCommitments.fixedLevel = .deterministicSimultaneous := rfl

end FastMLFE2.Theory.Canonical
