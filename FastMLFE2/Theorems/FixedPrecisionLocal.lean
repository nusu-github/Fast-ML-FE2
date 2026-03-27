import FastMLFE2.FixedPrecision.LocalSolver

namespace FastMLFE2.Theorems

open FastMLFE2.FixedPrecision
open FastMLFE2.Core

namespace FixedPrecision

open FixedLocalContext

variable {cfg : FixedFormat} {ι : Type*} [Fintype ι]

theorem decodedWrappedTotalWeight_eq_of_noWrap (ctx : FixedLocalContext cfg ι)
    (h : ctx.NoWrapLocalStep) :
    decodeAccumulator cfg ctx.wrappedTotalWeight =
      (ctx.unwrappedTotalWeightInt : ℝ) / cfg.scale := by
  rcases h with ⟨hW, _, _⟩
  simp [decodeAccumulator, hW]

theorem decodedWrappedForegroundSum_eq_of_noWrap (ctx : FixedLocalContext cfg ι)
    (h : ctx.NoWrapLocalStep) :
    decodeAccumulator cfg ctx.wrappedForegroundSum =
      (ctx.unwrappedForegroundSumInt : ℝ) / cfg.scale := by
  rcases h with ⟨_, hF, _⟩
  simp [decodeAccumulator, hF]

theorem decodedWrappedBackgroundSum_eq_of_noWrap (ctx : FixedLocalContext cfg ι)
    (h : ctx.NoWrapLocalStep) :
    decodeAccumulator cfg ctx.wrappedBackgroundSum =
      (ctx.unwrappedBackgroundSumInt : ℝ) / cfg.scale := by
  rcases h with ⟨_, _, hB⟩
  simp [decodeAccumulator, hB]

theorem decodedStep_eq_quantizedRealStep_of_noWrap (ctx : FixedLocalContext cfg ι)
    (h : ctx.NoWrapLocalStep) :
    decodeUnknown cfg (ctx.fixedMeanResidualStep) =
      decodeUnknown cfg (ctx.quantizedMeanResidualStep) := by
  rcases h with ⟨hW, hF, hB⟩
  simp [FixedLocalContext.fixedMeanResidualStep, FixedLocalContext.quantizedMeanResidualStep,
    decodeUnknown, decodeAccumulator, hW, hF, hB]

omit [Fintype ι] in
theorem decodeLocalContext_alphaCenter_eq (ctx : FixedLocalContext cfg ι) :
    ctx.decodeLocalContext.alphaCenter = decodeStorage cfg ctx.alphaCenter := rfl

omit [Fintype ι] in
theorem decodeLocalContext_imageValue_eq (ctx : FixedLocalContext cfg ι) :
    ctx.decodeLocalContext.imageValue = decodeStorage cfg ctx.imageValue := rfl

end FixedPrecision

end FastMLFE2.Theorems
