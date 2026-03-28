import FastMLFE2.Canonical.InteriorKernel
import FastMLFE2.Core.ClosedForm
import FastMLFE2.Theorems.Solvability.ClosedForm
import FastMLFE2.Theorems.Grid.GridLocal

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Canonical
open FastMLFE2.Level

namespace GridPixelData

noncomputable def validDirEquivDirection4
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Direction4 ≃ ValidDir p where
  toFun := FastMLFE2.Canonical.GridPixelData.interiorToValidDir p hInterior
  invFun := fun j => j.1
  left_inv := by
    intro d
    cases d <;> rfl
  right_inv := by
    intro j
    cases j with
    | mk d hd =>
        ext
        cases d <;> rfl

private theorem totalWeight_eq_interiorTotalWeight
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    (data.localCtx p state).totalWeight =
      (data.interiorLocalCtx p state hInterior).totalWeight := by
  let e := validDirEquivDirection4 p hInterior
  symm
  unfold FastMLFE2.Core.LocalContext.totalWeight
  simpa [GridPixelData.interiorLocalCtx, GridPixelData.localCtx] using
    (Fintype.sum_equiv e
      (fun d => (data.interiorLocalCtx p state hInterior).neighborWeight d)
      (fun j => (data.localCtx p state).neighborWeight j)
      (fun d => by
        cases d <;> rfl))

private theorem foregroundSum_eq_interiorForegroundSum
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    (data.localCtx p state).foregroundSum =
      (data.interiorLocalCtx p state hInterior).foregroundSum := by
  let e := validDirEquivDirection4 p hInterior
  symm
  unfold FastMLFE2.Core.LocalContext.foregroundSum
  simpa [GridPixelData.interiorLocalCtx, GridPixelData.localCtx] using
    (Fintype.sum_equiv e
      (fun d =>
        (data.interiorLocalCtx p state hInterior).neighborWeight d *
          (data.interiorLocalCtx p state hInterior).fgNeighbor d)
      (fun j => (data.localCtx p state).neighborWeight j * (data.localCtx p state).fgNeighbor j)
      (fun d => by
        cases d <;> rfl))

private theorem backgroundSum_eq_interiorBackgroundSum
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    (data.localCtx p state).backgroundSum =
      (data.interiorLocalCtx p state hInterior).backgroundSum := by
  let e := validDirEquivDirection4 p hInterior
  symm
  unfold FastMLFE2.Core.LocalContext.backgroundSum
  simpa [GridPixelData.interiorLocalCtx, GridPixelData.localCtx] using
    (Fintype.sum_equiv e
      (fun d =>
        (data.interiorLocalCtx p state hInterior).neighborWeight d *
          (data.interiorLocalCtx p state hInterior).bgNeighbor d)
      (fun j => (data.localCtx p state).neighborWeight j * (data.localCtx p state).bgNeighbor j)
      (fun d => by
        cases d <;> rfl))

theorem localCtx_rhs_eq_interior_rhs
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    (data.localCtx p state).rhs = (data.interiorLocalCtx p state hInterior).rhs := by
  ext i
  fin_cases i
  · simpa [FastMLFE2.Core.LocalContext.rhs,
      FastMLFE2.Canonical.GridPixelData.interiorLocalCtx] using
      congrArg
        (fun x =>
          (data.localCtx p state).alphaCenter * (data.localCtx p state).imageValue + x)
        (foregroundSum_eq_interiorForegroundSum data p state hInterior)
  · simpa [FastMLFE2.Core.LocalContext.rhs,
      FastMLFE2.Canonical.GridPixelData.interiorLocalCtx] using
      congrArg
        (fun x =>
          (1 - (data.localCtx p state).alphaCenter) * (data.localCtx p state).imageValue + x)
        (backgroundSum_eq_interiorBackgroundSum data p state hInterior)

theorem localCtx_normalMatrix_eq_interior_normalMatrix
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    (data.localCtx p state).normalMatrix =
      (data.interiorLocalCtx p state hInterior).normalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · rw [FastMLFE2.Core.LocalContext.normalMatrix,
      FastMLFE2.Core.LocalContext.normalMatrix,
      totalWeight_eq_interiorTotalWeight (data := data) (p := p) (state := state)
        (hInterior := hInterior)]
    simp [FastMLFE2.Canonical.GridPixelData.interiorLocalCtx,
      FastMLFE2.Canonical.GridPixelData.localCtx]
  · simp [FastMLFE2.Core.LocalContext.normalMatrix,
      FastMLFE2.Canonical.GridPixelData.interiorLocalCtx,
      FastMLFE2.Canonical.GridPixelData.localCtx]
  · simp [FastMLFE2.Core.LocalContext.normalMatrix,
      FastMLFE2.Canonical.GridPixelData.interiorLocalCtx,
      FastMLFE2.Canonical.GridPixelData.localCtx]
  · rw [FastMLFE2.Core.LocalContext.normalMatrix,
      FastMLFE2.Core.LocalContext.normalMatrix,
      totalWeight_eq_interiorTotalWeight (data := data) (p := p) (state := state)
        (hInterior := hInterior)]
    simp [FastMLFE2.Canonical.GridPixelData.interiorLocalCtx,
      FastMLFE2.Canonical.GridPixelData.localCtx]

theorem localCtx_closedFormDenom_eq_interior_closedFormDenom
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    LocalContext.closedFormDenom (data.localCtx p state) =
      LocalContext.closedFormDenom (data.interiorLocalCtx p state hInterior) := by
  rw [LocalContext.closedFormDenom_eq_det, LocalContext.closedFormDenom_eq_det,
    localCtx_normalMatrix_eq_interior_normalMatrix]

theorem localCtx_closedFormForegroundNumerator_eq_interior
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    LocalContext.closedFormForegroundNumerator (data.localCtx p state) =
      LocalContext.closedFormForegroundNumerator (data.interiorLocalCtx p state hInterior) := by
  rw [LocalContext.closedFormForegroundNumerator, LocalContext.closedFormForegroundNumerator,
    FastMLFE2.Core.LocalContext.rhs_foreground,
    FastMLFE2.Core.LocalContext.rhs_background,
    FastMLFE2.Core.LocalContext.rhs_foreground,
    FastMLFE2.Core.LocalContext.rhs_background,
    foregroundSum_eq_interiorForegroundSum,
    backgroundSum_eq_interiorBackgroundSum,
    totalWeight_eq_interiorTotalWeight]
  rfl

theorem localCtx_closedFormBackgroundNumerator_eq_interior
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    LocalContext.closedFormBackgroundNumerator (data.localCtx p state) =
      LocalContext.closedFormBackgroundNumerator (data.interiorLocalCtx p state hInterior) := by
  rw [LocalContext.closedFormBackgroundNumerator, LocalContext.closedFormBackgroundNumerator,
    FastMLFE2.Core.LocalContext.rhs_foreground,
    FastMLFE2.Core.LocalContext.rhs_background,
    FastMLFE2.Core.LocalContext.rhs_foreground,
    FastMLFE2.Core.LocalContext.rhs_background,
    foregroundSum_eq_interiorForegroundSum,
    backgroundSum_eq_interiorBackgroundSum,
    totalWeight_eq_interiorTotalWeight]
  rfl

theorem localCtx_closedForm_eq_interiorClosedFormSolution
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    LocalContext.closedFormSolution (data.localCtx p state) =
      data.interiorClosedFormSolution p state hInterior := by
  ext i
  fin_cases i
  · change foreground (LocalContext.closedFormSolution (data.localCtx p state)) =
      foreground (data.interiorClosedFormSolution p state hInterior)
    rw [LocalContext.foreground_closedFormSolution, GridPixelData.interiorClosedFormSolution,
      LocalContext.foreground_closedFormSolution,
      localCtx_closedFormForegroundNumerator_eq_interior,
      localCtx_closedFormDenom_eq_interior_closedFormDenom]
  · change background (LocalContext.closedFormSolution (data.localCtx p state)) =
      background (data.interiorClosedFormSolution p state hInterior)
    rw [LocalContext.background_closedFormSolution, GridPixelData.interiorClosedFormSolution,
      LocalContext.background_closedFormSolution,
      localCtx_closedFormBackgroundNumerator_eq_interior,
      localCtx_closedFormDenom_eq_interior_closedFormDenom]

private example
    {h w : Nat}
    (data : GridPixelData h w)
    (p : Pixel h w)
    (state : PixelState (Pixel h w))
    (hInterior : IsInterior p) :
    data.interiorClosedFormSolution p state hInterior =
      LocalContext.closedFormSolution (data.localCtx p state) := by
  simpa using (localCtx_closedForm_eq_interiorClosedFormSolution data p state hInterior).symm

end GridPixelData

end FastMLFE2.Theorems
