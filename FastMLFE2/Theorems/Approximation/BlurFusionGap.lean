import FastMLFE2.Approximation.BlurFusion
import FastMLFE2.Theorems.Approximation.NearBinary

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

abbrev Ctx (ι : Type*) := _root_.FastMLFE2.Core.LocalContext ι
abbrev Unknown := _root_.FastMLFE2.Core.LocalUnknown

/--
A synthetic one-neighbor context whose local cost is exactly the Blur-Fusion stage-two surrogate.

The single neighbor has weight `1`, foreground value `\hat F_i`, and background value `\hat B_i`.
-/
noncomputable def blurStageTwoCtx (ctx : Ctx ι) : Ctx Unit where
  alphaCenter := ctx.alphaCenter
  imageValue := ctx.imageValue
  alphaNeighbor := fun _ => ctx.alphaCenter
  fgNeighbor := fun _ => FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx
  bgNeighbor := fun _ => FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx
  epsilonR := 1
  omega := 0

/-- The exact joint minimizer of the Blur-Fusion stage-two surrogate. -/
noncomputable def blurStageTwoJointOutput (ctx : Ctx ι) : Unknown :=
  closedFormSolution (blurStageTwoCtx ctx)

/-- The exact foreground minimizer of the one-dimensional sequential stage-two problem. -/
noncomputable def blurStageTwoSequentialForeground (ctx : Ctx ι) : ℝ :=
  FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx +
    ctx.alphaCenter * FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx /
      (1 + ctx.alphaCenter ^ 2)

/-- The effective denominator of the exact joint stage-two foreground correction. -/
def blurStageTwoJointDenom (ctx : Ctx ι) : ℝ :=
  1 + ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2

private theorem blurStageTwoCtx_coreMathAssumptions
    (ctx : Ctx ι)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    CoreMathAssumptions (blurStageTwoCtx ctx) where
  epsilonPos := by norm_num [blurStageTwoCtx]
  omegaNonneg := by norm_num [blurStageTwoCtx]
  alphaCenterBounded := hα
  neighborNonempty := ⟨()⟩

@[simp] theorem alphaCenter_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).alphaCenter = ctx.alphaCenter := rfl

@[simp] theorem imageValue_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).imageValue = ctx.imageValue := rfl

@[simp] theorem totalWeight_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).totalWeight = 1 := by
  simp [blurStageTwoCtx, FastMLFE2.Core.LocalContext.totalWeight,
    FastMLFE2.Core.LocalContext.neighborWeight]

@[simp] theorem neighborWeight_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).neighborWeight () = 1 := by
  simp [blurStageTwoCtx, FastMLFE2.Core.LocalContext.neighborWeight]

@[simp] theorem foregroundMean_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).foregroundMean =
      FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx := by
  simp [blurStageTwoCtx, FastMLFE2.Core.LocalContext.foregroundMean,
    FastMLFE2.Core.LocalContext.foregroundSum,
    FastMLFE2.Core.LocalContext.totalWeight,
    FastMLFE2.Core.LocalContext.neighborWeight,
    FastMLFE2.Approximation.LocalContext.blurForegroundMean]

@[simp] theorem backgroundMean_blurStageTwoCtx (ctx : Ctx ι) :
    (blurStageTwoCtx ctx).backgroundMean =
      FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx := by
  simp [blurStageTwoCtx, FastMLFE2.Core.LocalContext.backgroundMean,
    FastMLFE2.Core.LocalContext.backgroundSum,
    FastMLFE2.Core.LocalContext.totalWeight,
    FastMLFE2.Core.LocalContext.neighborWeight,
    FastMLFE2.Approximation.LocalContext.blurBackgroundMean]

@[simp] theorem weightedMeanDenom_blurStageTwoCtx (ctx : Ctx ι) :
    LocalContext.weightedMeanDenom (blurStageTwoCtx ctx) = blurStageTwoJointDenom ctx := by
  simp [blurStageTwoJointDenom, LocalContext.weightedMeanDenom]

theorem localCost_blurStageTwoCtx_eq_blurStageTwoCost
    (ctx : Ctx ι)
    (g : Unknown) :
    (blurStageTwoCtx ctx).localCost g =
      FastMLFE2.Approximation.LocalContext.blurStageTwoCost ctx g := by
  simp [blurStageTwoCtx, FastMLFE2.Core.LocalContext.localCost,
    FastMLFE2.Core.LocalContext.neighborWeight,
    FastMLFE2.Approximation.LocalContext.blurStageTwoCost]
  ring

theorem blurStageTwoJointOutput_isCostStationary
    (ctx : Ctx ι)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    (blurStageTwoCtx ctx).IsCostStationary (blurStageTwoJointOutput ctx) := by
  letI : CoreMathAssumptions (blurStageTwoCtx ctx) := blurStageTwoCtx_coreMathAssumptions ctx hα
  simpa [blurStageTwoJointOutput] using
    closedForm_isCostStationary (ctx := blurStageTwoCtx ctx)

theorem foreground_blurStageTwoJointOutput_eq
    (ctx : Ctx ι)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    foreground (blurStageTwoJointOutput ctx) =
      FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx +
        ctx.alphaCenter *
          FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx /
            blurStageTwoJointDenom ctx := by
  letI : CoreMathAssumptions (blurStageTwoCtx ctx) := blurStageTwoCtx_coreMathAssumptions ctx hα
  have hbase := foreground_closedFormSolution_sub_foregroundMean_eq (ctx := blurStageTwoCtx ctx)
  have hresid :
      ctx.imageValue + ctx.alphaCenter *
          FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx -
          ctx.alphaCenter *
            FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx -
          FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx =
        FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx := by
    rw [FastMLFE2.Approximation.LocalContext.blurMeanResidual_eq]
    ring
  have hbase' :
      foreground (blurStageTwoJointOutput ctx) -
          FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx =
        ctx.alphaCenter * FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx /
          blurStageTwoJointDenom ctx := by
    simpa [blurStageTwoJointOutput, hresid] using hbase
  linarith

theorem blurStageTwoSequential_sub_joint_eq
    (ctx : Ctx ι)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    blurStageTwoSequentialForeground ctx - foreground (blurStageTwoJointOutput ctx) =
      ctx.alphaCenter * FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx *
        (1 - ctx.alphaCenter) ^ 2 /
        ((1 + ctx.alphaCenter ^ 2) * blurStageTwoJointDenom ctx) := by
  rw [blurStageTwoSequentialForeground, foreground_blurStageTwoJointOutput_eq ctx hα]
  have hden1 : 0 < 1 + ctx.alphaCenter ^ 2 := by positivity
  have hden2 : 0 < blurStageTwoJointDenom ctx := by
    rw [blurStageTwoJointDenom]
    positivity
  field_simp [hden1.ne', hden2.ne', blurStageTwoJointDenom]
  simp [blurStageTwoJointDenom]
  ring_nf

theorem abs_blurMeanResidual_le_one_of_boxed
    (ctx : Ctx ι)
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hμF :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ≤ 1)
    (hμB :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| ≤ 1 := by
  rw [FastMLFE2.Approximation.LocalContext.blurMeanResidual_eq]
  have hlow :
      -1 ≤
        ctx.imageValue -
          (ctx.alphaCenter * FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx +
            (1 - ctx.alphaCenter) *
              FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx) := by
    nlinarith [hI.1, hI.2, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2]
  have hupp :
      ctx.imageValue -
          (ctx.alphaCenter * FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx +
            (1 - ctx.alphaCenter) *
              FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx)
        ≤ 1 := by
    nlinarith [hI.1, hI.2, hα.1, hα.2, hμF.1, hμF.2, hμB.1, hμB.2]
  exact abs_le.2 ⟨hlow, hupp⟩

theorem abs_blurStageTwoSequential_sub_joint_le_quadratic
    (ctx : Ctx ι)
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hμF :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ≤ 1)
    (hμB :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    |blurStageTwoSequentialForeground ctx - foreground (blurStageTwoJointOutput ctx)| ≤
      ctx.alphaCenter * (1 - ctx.alphaCenter) ^ 2 := by
  have hgap := blurStageTwoSequential_sub_joint_eq ctx hα
  have hres := abs_blurMeanResidual_le_one_of_boxed ctx hI hμF hμB hα
  have hα0 : 0 ≤ ctx.alphaCenter := hα.1
  have hβ0 : 0 ≤ 1 - ctx.alphaCenter := sub_nonneg.mpr hα.2
  have hden1 : 0 < 1 + ctx.alphaCenter ^ 2 := by positivity
  have hden2 : 0 < blurStageTwoJointDenom ctx := by
    rw [blurStageTwoJointDenom]
    positivity
  rw [hgap, abs_div, abs_mul, abs_mul]
  rw [abs_of_nonneg hα0, abs_of_nonneg (sq_nonneg (1 - ctx.alphaCenter)),
    abs_of_pos (mul_pos hden1 hden2)]
  have hnum_nonneg :
      0 ≤ ctx.alphaCenter * |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| *
        (1 - ctx.alphaCenter) ^ 2 := by
    positivity
  have hden_ge_one : 1 ≤ (1 + ctx.alphaCenter ^ 2) * blurStageTwoJointDenom ctx := by
    have h1 : 1 ≤ 1 + ctx.alphaCenter ^ 2 := by
      nlinarith [sq_nonneg ctx.alphaCenter]
    have h2 : 1 ≤ blurStageTwoJointDenom ctx := by
      rw [blurStageTwoJointDenom]
      nlinarith [sq_nonneg ctx.alphaCenter, sq_nonneg (1 - ctx.alphaCenter)]
    nlinarith
  have hstep1 :
      ctx.alphaCenter *
          |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| *
          (1 - ctx.alphaCenter) ^ 2 /
          ((1 + ctx.alphaCenter ^ 2) * blurStageTwoJointDenom ctx) ≤
        ctx.alphaCenter *
          |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| *
          (1 - ctx.alphaCenter) ^ 2 := by
    exact div_le_self hnum_nonneg hden_ge_one
  have hstep2 :
      ctx.alphaCenter *
          |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| *
          (1 - ctx.alphaCenter) ^ 2 ≤
        ctx.alphaCenter * (1 - ctx.alphaCenter) ^ 2 := by
    have hmul :
        ctx.alphaCenter *
            |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| ≤
          ctx.alphaCenter * 1 := by
      exact mul_le_mul_of_nonneg_left hres hα0
    calc
      ctx.alphaCenter *
          |FastMLFE2.Approximation.LocalContext.blurMeanResidual ctx| *
          (1 - ctx.alphaCenter) ^ 2
          ≤ (ctx.alphaCenter * 1) * (1 - ctx.alphaCenter) ^ 2 := by
              exact mul_le_mul_of_nonneg_right hmul (sq_nonneg (1 - ctx.alphaCenter))
      _ = ctx.alphaCenter * (1 - ctx.alphaCenter) ^ 2 := by ring
  exact le_trans hstep1 hstep2

theorem abs_blurStageTwoSequential_sub_joint_le_crossTerm
    (ctx : Ctx ι)
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hμF :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurForegroundMean ctx ≤ 1)
    (hμB :
      0 ≤ FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ∧
        FastMLFE2.Approximation.LocalContext.blurBackgroundMean ctx ≤ 1)
    (hα : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1) :
    |blurStageTwoSequentialForeground ctx - foreground (blurStageTwoJointOutput ctx)| ≤
      ctx.alphaCenter * (1 - ctx.alphaCenter) := by
  have hquad := abs_blurStageTwoSequential_sub_joint_le_quadratic ctx hI hμF hμB hα
  have hβ0 : 0 ≤ 1 - ctx.alphaCenter := sub_nonneg.mpr hα.2
  have hβ1 : 1 - ctx.alphaCenter ≤ 1 := by linarith
  have hquad_le :
      ctx.alphaCenter * (1 - ctx.alphaCenter) ^ 2 ≤
        ctx.alphaCenter * (1 - ctx.alphaCenter) := by
    have hsq_le : (1 - ctx.alphaCenter) ^ 2 ≤ 1 - ctx.alphaCenter := by
      nlinarith [hβ0, hβ1]
    exact mul_le_mul_of_nonneg_left hsq_le hα.1
  exact le_trans hquad hquad_le

end LocalContext

end FastMLFE2.Theorems
