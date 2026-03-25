import FastMLFE2.Canonical.Grid
import FastMLFE2.Canonical.LocalCommitments

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

/-!
Canonical multilevel schedule definitions for authored semantics.
-/

def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    Nat.log2 (n - 1) + 1

def roundFloatToNatAtLeastOne (x : Float) : Nat :=
  max 1 (Float.round x).toUInt64.toNat

def levelSizeAt (size level levelCount : Nat) : Nat :=
  if levelCount = 0 then
    size
  else
    roundFloatToNatAtLeastOne
      ((Float.ofNat size) ^ (Float.ofNat level / Float.ofNat levelCount))

def levelCount (width height : Nat) : Nat :=
  ceilLog2 (max width height)

def levelSizes (width height : Nat) : List (Nat × Nat) :=
  let levels := levelCount width height
  if levels = 0 then
    [(width, height)]
  else
    (List.range (levels + 1)).map fun level =>
      ((levelSizeAt width level levels), (levelSizeAt height level levels))

@[simp] theorem ceilLog2_zero : ceilLog2 0 = 0 := by
  simp [ceilLog2]

@[simp] theorem ceilLog2_one : ceilLog2 1 = 0 := by
  simp [ceilLog2]

@[simp] theorem levelCount_eq_ceilLog2 (width height : Nat) :
    levelCount width height = ceilLog2 (max width height) := rfl

/-- Nearest-neighbor source coordinate for a resized 1D axis. -/
def nearestNeighborCoord {source target : Nat} [Fact (0 < source)]
    (i : Fin target) : Fin source :=
  ⟨min (source - 1) (i.1 * source / target), by
    have hSource : 0 < source := Fact.out
    exact lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hSource zero_lt_one)⟩

/-- Nearest-neighbor source pixel for a resized 2D grid. -/
def nearestNeighborPixel {hSrc wSrc hDst wDst : Nat} [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (p : Pixel hDst wDst) : Pixel hSrc wSrc :=
  (nearestNeighborCoord (source := hSrc) (target := hDst) p.1,
    nearestNeighborCoord (source := wSrc) (target := wDst) p.2)

/-- Pull a function-valued grid back along nearest-neighbor resize. -/
def nearestNeighborResize {α : Type*} {hSrc wSrc hDst wDst : Nat} [Fact (0 < hSrc)]
    [Fact (0 < wSrc)] (state : Pixel hSrc wSrc → α) : Pixel hDst wDst → α :=
  fun p => state (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
    (wDst := wDst) p)

@[simp] theorem nearestNeighborResize_apply {α : Type*} {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] (state : Pixel hSrc wSrc → α)
    (p : Pixel hDst wDst) :
    nearestNeighborResize (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) state p =
      state (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
        (wDst := wDst) p) := rfl

@[simp] theorem nearestNeighborImage_apply {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] (image : Pixel hSrc wSrc → ℝ)
    (p : Pixel hDst wDst) :
    nearestNeighborResize (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) image p =
      image (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
        (wDst := wDst) p) := rfl

@[simp] theorem nearestNeighborAlpha_apply {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] (alpha : Pixel hSrc wSrc → ℝ)
    (p : Pixel hDst wDst) :
    nearestNeighborResize (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) alpha p =
      alpha (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
        (wDst := wDst) p) := rfl

@[simp] theorem nearestNeighborCoord_self {source : Nat} [Fact (0 < source)]
    (i : Fin source) :
    nearestNeighborCoord (source := source) (target := source) i = i := by
  apply Fin.ext
  have hdiv : i.1 * source / source = i.1 := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right i.1 (m := source) Fact.out)
  have hmin : min (source - 1) (i.1 * source / source) = i.1 := by
    rw [hdiv]
    exact Nat.min_eq_right (Nat.le_pred_of_lt i.2)
  simpa [nearestNeighborCoord] using hmin

@[simp] theorem nearestNeighborResize_self {α : Type*} {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)] (state : Pixel h w → α) :
    nearestNeighborResize (hSrc := h) (wSrc := w) (hDst := h) (wDst := w) state = state := by
  funext p
  simp [nearestNeighborResize, nearestNeighborPixel, nearestNeighborCoord_self]

/-- A fused nearest-neighbor update that reads the coarse state through the coarse-to-fine
lookup at the point of use instead of materializing a resized fine state first. -/
noncomputable def fusedNearestNeighborUpdateAt {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] {η : Pixel hDst wDst → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel hDst wDst) η)
    (state : PixelState (Pixel hSrc wSrc))
    (p : Pixel hDst wDst) : LocalUnknown :=
  builder.jacobiUpdateAt
    (fun q => state (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc)
      (hDst := hDst) (wDst := wDst) q)) p

@[simp] theorem fusedNearestNeighborUpdateAt_apply {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] {η : Pixel hDst wDst → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel hDst wDst) η)
    (state : PixelState (Pixel hSrc wSrc))
    (p : Pixel hDst wDst) :
    fusedNearestNeighborUpdateAt (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
      (wDst := wDst) builder state p =
      builder.jacobiUpdateAt
        (fun q => state (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc)
          (hDst := hDst) (wDst := wDst) q)) p := rfl

/-- A nearest-neighbor resize followed by one fine-level update is exactly the fused update
that reads coarse pixels directly through the same nearest-neighbor pullback. -/
theorem nearestNeighborResize_then_update_eq_fused {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)] {η : Pixel hDst wDst → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel hDst wDst) η)
    (state : PixelState (Pixel hSrc wSrc))
    (p : Pixel hDst wDst) :
    builder.jacobiStep (nearestNeighborResize (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
      (wDst := wDst) state) p =
      fusedNearestNeighborUpdateAt (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst)
        (wDst := wDst) builder state p := by
  unfold nearestNeighborResize fusedNearestNeighborUpdateAt LocalContextBuilder.jacobiStep
    LocalContextBuilder.jacobiUpdateAt
  rfl

theorem nearestNeighborResize_sameSize_then_update_eq {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)] {η : Pixel h w → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel h w) η)
    (state : PixelState (Pixel h w))
    (p : Pixel h w) :
    builder.jacobiStep (nearestNeighborResize (hSrc := h) (wSrc := w) (hDst := h)
      (wDst := w) state) p = builder.jacobiStep state p := by
  rw [nearestNeighborResize_self]

theorem nearestNeighborResize_sameSize_iterate_eq {height width : Nat}
    [Fact (0 < height)] [Fact (0 < width)] {η : Pixel height width → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel height width) η)
    (state : PixelState (Pixel height width))
    (n : Nat) :
    Nat.iterate (builder.jacobiStep) n
      (nearestNeighborResize (hSrc := height) (wSrc := width) (hDst := height)
        (wDst := width) state) =
      Nat.iterate (builder.jacobiStep) n state := by
  induction n generalizing state with
  | zero =>
      simp [Nat.iterate]
  | succ n ih =>
      have hIH := ih state
      calc
        Nat.iterate (builder.jacobiStep) (Nat.succ n)
            (nearestNeighborResize (hSrc := height) (wSrc := width) (hDst := height)
              (wDst := width) state)
            = builder.jacobiStep (Nat.iterate (builder.jacobiStep) n
                (nearestNeighborResize (hSrc := height) (wSrc := width) (hDst := height)
                  (wDst := width) state)) := by
                rw [Function.iterate_succ_apply']
        _ = builder.jacobiStep (Nat.iterate (builder.jacobiStep) n state) := by
              rw [hIH]
        _ = Nat.iterate (builder.jacobiStep) (Nat.succ n) state := by
              rw [Function.iterate_succ_apply']

/-- When two consecutive levels have the same size, their updates can be merged by adding
their iteration counts. -/
theorem nearestNeighborResize_sameSize_merge_iterate_eq {height width : Nat}
    [Fact (0 < height)] [Fact (0 < width)] {η : Pixel height width → Type*} [∀ p, Fintype (η p)]
    (builder : LocalContextBuilder (Pixel height width) η)
    (state : PixelState (Pixel height width))
    (n₁ n₂ : Nat) :
    Nat.iterate (builder.jacobiStep) n₂
      (Nat.iterate (builder.jacobiStep) n₁
        (nearestNeighborResize (hSrc := height) (wSrc := width) (hDst := height)
          (wDst := width) state)) =
      Nat.iterate (builder.jacobiStep) (n₁ + n₂) state := by
  rw [nearestNeighborResize_self]
  have hIter := congrArg (fun g => g state) (Function.iterate_add (builder.jacobiStep) n₂ n₁)
  rw [Nat.add_comm] at hIter
  exact hIter.symm

end FastMLFE2.Canonical
