import FastMLFE2.Theory.Theorems.NearBinary

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def meanResidualSolution (ctx : LocalContext ι) : LocalUnknown :=
  mkLocalUnknown
    (ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom)
    (ctx.backgroundMean + (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom)

@[simp] theorem foreground_meanResidualSolution (ctx : LocalContext ι) :
    foreground (meanResidualSolution ctx) =
      ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom := by
  simp [meanResidualSolution]

@[simp] theorem background_meanResidualSolution (ctx : LocalContext ι) :
    background (meanResidualSolution ctx) =
      ctx.backgroundMean + (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom := by
  simp [meanResidualSolution]

@[simp] theorem foreground_clamp01_meanResidualSolution (ctx : LocalContext ι) :
    foreground (clamp01 (meanResidualSolution ctx)) =
      clamp01Scalar
        (ctx.foregroundMean + ctx.alphaCenter * ctx.meanResidual / ctx.weightedMeanDenom) := by
  simp [meanResidualSolution]

@[simp] theorem background_clamp01_meanResidualSolution (ctx : LocalContext ι) :
    background (clamp01 (meanResidualSolution ctx)) =
      clamp01Scalar
        (ctx.backgroundMean +
          (1 - ctx.alphaCenter) * ctx.meanResidual / ctx.weightedMeanDenom) := by
  simp [meanResidualSolution]

theorem meanResidualSolution_eq_closedFormSolution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    meanResidualSolution ctx = closedFormSolution ctx := by
  funext i
  fin_cases i
  · simpa [foreground, meanResidualSolution, mkLocalUnknown] using
      (foreground_correction_uses_meanResidual (ctx := ctx)).symm
  · simpa [background, meanResidualSolution, mkLocalUnknown] using
      (background_correction_uses_meanResidual (ctx := ctx)).symm

theorem clamp01_meanResidualSolution_eq_clamp01_closedFormSolution
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx] :
    clamp01 (meanResidualSolution ctx) = clamp01 (closedFormSolution ctx) := by
  simp [meanResidualSolution_eq_closedFormSolution (ctx := ctx)]

end LocalContext

end FastMLFE2.Theory.Theorems
