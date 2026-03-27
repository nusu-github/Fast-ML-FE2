import FastMLFE2.FixedPrecision.Format
import FastMLFE2.Theorems.ClosedFormMeanResidual

namespace FastMLFE2.FixedPrecision

open FastMLFE2.Core

structure FixedLocalContext (cfg : FixedFormat) (ι : Type*) where
  alphaCenter : Storage cfg
  imageValue : Storage cfg
  alphaNeighbor : ι → Storage cfg
  fgNeighbor : ι → Storage cfg
  bgNeighbor : ι → Storage cfg
  epsilonR : Storage cfg
  omega : Storage cfg

namespace FixedLocalContext

variable {cfg : FixedFormat} {ι : Type*} [Fintype ι]

noncomputable def decodeLocalContext (ctx : FixedLocalContext cfg ι) : LocalContext ι where
  alphaCenter := decodeStorage cfg ctx.alphaCenter
  imageValue := decodeStorage cfg ctx.imageValue
  alphaNeighbor := fun j => decodeStorage cfg (ctx.alphaNeighbor j)
  fgNeighbor := fun j => decodeStorage cfg (ctx.fgNeighbor j)
  bgNeighbor := fun j => decodeStorage cfg (ctx.bgNeighbor j)
  epsilonR := decodeStorage cfg ctx.epsilonR
  omega := decodeStorage cfg ctx.omega

noncomputable def encodedNeighborWeight (ctx : FixedLocalContext cfg ι) (j : ι) : Accumulator cfg :=
  encodeSigned cfg
    (decodeStorage cfg ctx.epsilonR +
      decodeStorage cfg ctx.omega *
        |decodeStorage cfg ctx.alphaCenter - decodeStorage cfg (ctx.alphaNeighbor j)|)

noncomputable def wrappedTotalWeight (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  ∑ j, encodedNeighborWeight ctx j

noncomputable def wrappedForegroundSum (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  ∑ j, wrapScaleMul cfg (encodedNeighborWeight ctx j)
    (castStorageToAccumulator cfg (ctx.fgNeighbor j))

noncomputable def wrappedBackgroundSum (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  ∑ j, wrapScaleMul cfg (encodedNeighborWeight ctx j)
    (castStorageToAccumulator cfg (ctx.bgNeighbor j))

noncomputable def unwrappedTotalWeightInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, (encodedNeighborWeight ctx j).toInt

noncomputable def unwrappedForegroundSumInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, (wrapScaleMul cfg (encodedNeighborWeight ctx j)
    (castStorageToAccumulator cfg (ctx.fgNeighbor j))).toInt

noncomputable def unwrappedBackgroundSumInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, (wrapScaleMul cfg (encodedNeighborWeight ctx j)
    (castStorageToAccumulator cfg (ctx.bgNeighbor j))).toInt

def NoWrapLocalStep (ctx : FixedLocalContext cfg ι) : Prop :=
  (ctx.wrappedTotalWeight.toInt = ctx.unwrappedTotalWeightInt) ∧
    (ctx.wrappedForegroundSum.toInt = ctx.unwrappedForegroundSumInt) ∧
    (ctx.wrappedBackgroundSum.toInt = ctx.unwrappedBackgroundSumInt)

noncomputable def quantizedMeanResidualStep (ctx : FixedLocalContext cfg ι) : FixedUnknown cfg :=
  let alpha := decodeStorage cfg ctx.alphaCenter
  let alpha1 := 1 - alpha
  let image := decodeStorage cfg ctx.imageValue
  let totalWeight := (ctx.unwrappedTotalWeightInt : ℝ) / cfg.scale
  let foregroundSum := (ctx.unwrappedForegroundSumInt : ℝ) / cfg.scale
  let backgroundSum := (ctx.unwrappedBackgroundSumInt : ℝ) / cfg.scale
  let foregroundMean := foregroundSum / totalWeight
  let backgroundMean := backgroundSum / totalWeight
  let residual := image - alpha * foregroundMean - alpha1 * backgroundMean
  let denom := totalWeight + alpha ^ 2 + alpha1 ^ 2
  let foregroundValue := foregroundMean + alpha * residual / denom
  let backgroundValue := backgroundMean + alpha1 * residual / denom
  (encodeNearestClamp01 cfg foregroundValue, encodeNearestClamp01 cfg backgroundValue)

noncomputable def fixedMeanResidualStep (ctx : FixedLocalContext cfg ι) : FixedUnknown cfg :=
  let alpha := decodeStorage cfg ctx.alphaCenter
  let alpha1 := 1 - alpha
  let image := decodeStorage cfg ctx.imageValue
  let totalWeight := decodeAccumulator cfg ctx.wrappedTotalWeight
  let foregroundSum := decodeAccumulator cfg ctx.wrappedForegroundSum
  let backgroundSum := decodeAccumulator cfg ctx.wrappedBackgroundSum
  let foregroundMean := foregroundSum / totalWeight
  let backgroundMean := backgroundSum / totalWeight
  let residual := image - alpha * foregroundMean - alpha1 * backgroundMean
  let denom := totalWeight + alpha ^ 2 + alpha1 ^ 2
  let foregroundValue := foregroundMean + alpha * residual / denom
  let backgroundValue := backgroundMean + alpha1 * residual / denom
  (encodeNearestClamp01 cfg foregroundValue, encodeNearestClamp01 cfg backgroundValue)

end FixedLocalContext

end FastMLFE2.FixedPrecision
