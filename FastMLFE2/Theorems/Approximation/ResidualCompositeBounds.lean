import FastMLFE2.Theorems.Approximation.ClosedFormMeanResidual
import FastMLFE2.Theorems.Solvability.MeanResidualBounds
import FastMLFE2.Compositing.OneChannel
import Mathlib

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Compositing

namespace LocalContext

variable {ι : Type*} [Fintype ι]

/-- Proposition 3 (local form): closed-form compositing error is a scaled mean residual. -/
theorem abs_closedFormCompositingError_le_abs_meanResidual
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    |compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx)) - ctx.imageValue| ≤
      |ctx.meanResidual| := by
  have hcomp :
      compose ctx.alphaCenter (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx)) - ctx.imageValue =
      - ctx.totalWeight * ctx.meanResidual / ctx.weightedMeanDenom := by
    have h1 :
        compose ctx.alphaCenter
            (foreground (closedFormSolution ctx))
            (background (closedFormSolution ctx)) -
          compose ctx.alphaCenter ctx.foregroundMean ctx.backgroundMean =
        (ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) * ctx.meanResidual /
          ctx.weightedMeanDenom := by
      rw [compose_sub_compose]
      rw [foreground_correction_uses_meanResidual,
        background_correction_uses_meanResidual]
      ring_nf
    have h2 :
        compose ctx.alphaCenter ctx.foregroundMean ctx.backgroundMean =
          ctx.imageValue - ctx.meanResidual := by
      simp [FastMLFE2.Core.LocalContext.meanResidual, compose]
      ring
    have hq :
        ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2 =
          ctx.weightedMeanDenom - ctx.totalWeight := by
      simp [FastMLFE2.Core.LocalContext.weightedMeanDenom]
      ring
    have h3 :
        compose ctx.alphaCenter (foreground (closedFormSolution ctx))
          (background (closedFormSolution ctx)) - ctx.imageValue =
        (compose ctx.alphaCenter (foreground (closedFormSolution ctx))
          (background (closedFormSolution ctx)) -
          compose ctx.alphaCenter ctx.foregroundMean ctx.backgroundMean) -
        ctx.meanResidual := by
      rw [h2]
      ring
    calc
      compose ctx.alphaCenter (foreground (closedFormSolution ctx))
          (background (closedFormSolution ctx)) - ctx.imageValue
          = (compose ctx.alphaCenter (foreground (closedFormSolution ctx))
              (background (closedFormSolution ctx)) -
            compose ctx.alphaCenter ctx.foregroundMean ctx.backgroundMean) -
            ctx.meanResidual := h3
      _ = ((ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2) * ctx.meanResidual /
            ctx.weightedMeanDenom) - ctx.meanResidual := by
          rw [h1]
      _ = ((ctx.weightedMeanDenom - ctx.totalWeight) * ctx.meanResidual /
            ctx.weightedMeanDenom) - ctx.meanResidual := by
          rw [hq]
      _ = - ctx.totalWeight * ctx.meanResidual / ctx.weightedMeanDenom := by
          have hD : 0 < ctx.weightedMeanDenom := weightedMeanDenom_pos ctx
          field_simp [hD.ne']
          ring_nf
  rw [hcomp]
  have hWnonneg : 0 ≤ ctx.totalWeight := le_of_lt (totalWeight_pos ctx)
  have hDpos : 0 < ctx.weightedMeanDenom := weightedMeanDenom_pos ctx
  have hcoeff : ctx.totalWeight / ctx.weightedMeanDenom ≤ 1 := by
    have hWleD : ctx.totalWeight ≤ ctx.weightedMeanDenom := by
      rw [FastMLFE2.Core.LocalContext.weightedMeanDenom]
      nlinarith [sq_nonneg ctx.alphaCenter, sq_nonneg (1 - ctx.alphaCenter)]
    rw [div_le_one hDpos]
    exact hWleD
  have habs :
      |-ctx.totalWeight * ctx.meanResidual / ctx.weightedMeanDenom| =
        (ctx.totalWeight / ctx.weightedMeanDenom) * |ctx.meanResidual| := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hWnonneg, abs_of_pos hDpos]
    ring
  rw [habs]
  calc
    (ctx.totalWeight / ctx.weightedMeanDenom) * |ctx.meanResidual| ≤
      1 * |ctx.meanResidual| := by
        exact mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    _ = |ctx.meanResidual| := by ring

/-- Proposition 3: a bound on `meanResidual` transfers directly to composite error. -/
theorem abs_closedFormCompositingError_le_of_meanResidual_le
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    {ε : ℝ}
    (hε : |ctx.meanResidual| ≤ ε) :
    |compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx)) - ctx.imageValue| ≤ ε := by
  exact (abs_closedFormCompositingError_le_abs_meanResidual ctx).trans hε

/-- Finite-family infinity norm for real-valued quantities. -/
noncomputable def familyInfinityNorm {β : Type*} [Fintype β] [Nonempty β] (f : β → ℝ) : ℝ :=
  (Finset.univ.image fun b => |f b|).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Pointwise monotonicity of the finite-family infinity norm. -/
theorem familyInfinityNorm_mono
    {β : Type*} [Fintype β] [Nonempty β] {f g : β → ℝ}
    (h : ∀ b, |f b| ≤ |g b|) :
    familyInfinityNorm f ≤ familyInfinityNorm g := by
  unfold familyInfinityNorm
  refine (Finset.max'_le_iff _ _).2 ?_
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
  have hymax : |g b| ≤ (Finset.univ.image fun b => |g b|).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty) := by
    exact Finset.le_max' (s := Finset.univ.image fun b => |g b|) (x := |g b|)
      (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  exact (h b).trans hymax

/-- Proposition 3 (level-wide corollary): max composite error is controlled by max residual. -/
theorem familyClosedFormCompositingError_le_familyMeanResidual
    {β : Type*} [Fintype β] [Nonempty β]
    (ctxs : β → LocalContext ι)
    (hCtx : ∀ b, CoreMathAssumptions (ctxs b)) :
    familyInfinityNorm
        (fun b =>
          compose (ctxs b).alphaCenter
            (foreground (closedFormSolution (ctxs b)))
            (background (closedFormSolution (ctxs b))) - (ctxs b).imageValue) ≤
      familyInfinityNorm (fun b => (ctxs b).meanResidual) := by
  refine familyInfinityNorm_mono ?_
  intro b
  exact abs_closedFormCompositingError_le_abs_meanResidual (ctxs b)

/-- Proposition 3 (level-wide epsilon form). -/
theorem familyClosedFormCompositingError_le_of_familyMeanResidualBound
    {β : Type*} [Fintype β] [Nonempty β]
    (ctxs : β → LocalContext ι)
    (hCtx : ∀ b, CoreMathAssumptions (ctxs b))
    {ε : ℝ}
    (hε : familyInfinityNorm (fun b => (ctxs b).meanResidual) ≤ ε) :
    familyInfinityNorm
        (fun b =>
          compose (ctxs b).alphaCenter
            (foreground (closedFormSolution (ctxs b)))
            (background (closedFormSolution (ctxs b))) - (ctxs b).imageValue) ≤
      ε := by
  exact (familyClosedFormCompositingError_le_familyMeanResidual
    (ctxs := ctxs) hCtx).trans hε

/-- Proposition 3 boxed-input specialization. -/
theorem abs_closedFormCompositingError_le_one_of_boxed_inputs
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    |compose ctx.alphaCenter
        (foreground (closedFormSolution ctx))
        (background (closedFormSolution ctx)) - ctx.imageValue| ≤ 1 := by
  exact (abs_closedFormCompositingError_le_abs_meanResidual ctx).trans
    (abs_meanResidual_le_one_of_boxed_inputs ctx hI hα hfg hbg)

end LocalContext

end FastMLFE2.Theorems
