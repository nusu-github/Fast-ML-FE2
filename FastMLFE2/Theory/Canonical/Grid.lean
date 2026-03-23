import FastMLFE2.Theory.Canonical.Builder

namespace FastMLFE2.Theory.Canonical

/-!
Faithful two-dimensional grid geometry for boundary-aware four-neighbor semantics.
-/

open FastMLFE2.Theory.Core

abbrev Pixel (h w : Nat) := Fin h × Fin w

inductive Direction4 where
  | up
  | down
  | left
  | right
  deriving DecidableEq, Fintype, Repr

def allDirections : Finset Direction4 :=
  [Direction4.up, Direction4.down, Direction4.left, Direction4.right].toFinset

@[simp] theorem mem_allDirections (d : Direction4) :
    d ∈ allDirections := by
  cases d <;> simp [allDirections]

def IsValidDir
    {h w : Nat}
    (p : Pixel h w) : Direction4 → Prop
  | .up => 0 < p.1.1
  | .down => p.1.1 + 1 < h
  | .left => 0 < p.2.1
  | .right => p.2.1 + 1 < w

instance
    {h w : Nat}
    (p : Pixel h w) : DecidablePred (IsValidDir p) := by
  intro d
  cases d <;> dsimp [IsValidDir] <;> infer_instance

abbrev ValidDir
    {h w : Nat}
    (p : Pixel h w) :=
  { d : Direction4 // IsValidDir p d }

instance
    {h w : Nat}
    (p : Pixel h w) : Fintype (ValidDir p) := by
  dsimp [ValidDir]
  infer_instance

def validDirections
    {h w : Nat}
    (p : Pixel h w) : Finset Direction4 :=
  (if IsValidDir p .up then {Direction4.up} else ∅) ∪
    (if IsValidDir p .down then {Direction4.down} else ∅) ∪
    (if IsValidDir p .left then {Direction4.left} else ∅) ∪
    (if IsValidDir p .right then {Direction4.right} else ∅)

def validDirCount
    {h w : Nat}
    (p : Pixel h w) : Nat :=
  (if IsValidDir p .up then 1 else 0) +
    (if IsValidDir p .down then 1 else 0) +
    (if IsValidDir p .left then 1 else 0) +
    (if IsValidDir p .right then 1 else 0)

def IsInterior
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  0 < p.1.1 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w

def IsTopEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  p.1.1 = 0 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w

def IsBottomEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  0 < p.1.1 ∧ p.1.1 + 1 = h ∧ 0 < p.2.1 ∧ p.2.1 + 1 < w

def IsLeftEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  0 < p.1.1 ∧ p.1.1 + 1 < h ∧ p.2.1 = 0 ∧ p.2.1 + 1 < w

def IsRightEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  0 < p.1.1 ∧ p.1.1 + 1 < h ∧ 0 < p.2.1 ∧ p.2.1 + 1 = w

def IsTopLeftCorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  p.1.1 = 0 ∧ p.2.1 = 0

def IsTopRightCorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  p.1.1 = 0 ∧ p.2.1 + 1 = w

def IsBottomLeftCorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  p.1.1 + 1 = h ∧ p.2.1 = 0

def IsBottomRightCorner
    {h w : Nat}
    (p : Pixel h w) : Prop :=
  p.1.1 + 1 = h ∧ p.2.1 + 1 = w

private def upNeighbor
    {h w : Nat}
    (p : Pixel h w)
    (hUp : 0 < p.1.1) : Pixel h w :=
  (⟨p.1.1 - 1, lt_trans (Nat.sub_lt (Nat.succ_le_of_lt hUp) (by decide)) p.1.2⟩, p.2)

private def downNeighbor
    {h w : Nat}
    (p : Pixel h w)
    (hDown : p.1.1 + 1 < h) : Pixel h w :=
  (⟨p.1.1 + 1, hDown⟩, p.2)

private def leftNeighbor
    {h w : Nat}
    (p : Pixel h w)
    (hLeft : 0 < p.2.1) : Pixel h w :=
  (p.1, ⟨p.2.1 - 1, lt_trans (Nat.sub_lt (Nat.succ_le_of_lt hLeft) (by decide)) p.2.2⟩)

private def rightNeighbor
    {h w : Nat}
    (p : Pixel h w)
    (hRight : p.2.1 + 1 < w) : Pixel h w :=
  (p.1, ⟨p.2.1 + 1, hRight⟩)

def neighborPixel
    {h w : Nat}
    (p : Pixel h w) : ValidDir p → Pixel h w
  | ⟨.up, hUp⟩ => upNeighbor p hUp
  | ⟨.down, hDown⟩ => downNeighbor p hDown
  | ⟨.left, hLeft⟩ => leftNeighbor p hLeft
  | ⟨.right, hRight⟩ => rightNeighbor p hRight

def fourNeighborhood
    {h w : Nat}
    (p : Pixel h w) : Finset (Pixel h w) :=
  (Finset.univ : Finset (ValidDir p)).image (neighborPixel p)

structure GridPixelData (h w : Nat) where
  alpha : Pixel h w → ℝ
  image : Pixel h w → ℝ
  epsilonR : ℝ
  omega : ℝ

namespace GridPixelData

def toCanonicalPixelData
    {h w : Nat}
    (data : GridPixelData h w) :
    CanonicalPixelData (Pixel h w) (fun p => ValidDir p) where
  alpha := data.alpha
  image := data.image
  neighborPixel := neighborPixel
  epsilonR := data.epsilonR
  omega := data.omega

end GridPixelData

end FastMLFE2.Theory.Canonical
