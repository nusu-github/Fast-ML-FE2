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

noncomputable def unwrappedNeighborWeightInt (ctx : FixedLocalContext cfg ι) (j : ι) : Int :=
  Int.floor
    ((decodeStorage cfg ctx.epsilonR +
      decodeStorage cfg ctx.omega *
        |decodeStorage cfg ctx.alphaCenter - decodeStorage cfg (ctx.alphaNeighbor j)|) *
      cfg.scale + (1 : ℝ) / 2)

noncomputable def wrappedForegroundTerm (ctx : FixedLocalContext cfg ι) (j : ι) : Accumulator cfg :=
  BitVec.ofInt cfg.accWidth
    ((ctx.unwrappedNeighborWeightInt j * (ctx.fgNeighbor j).toNat) / cfg.scale)

noncomputable def wrappedBackgroundTerm (ctx : FixedLocalContext cfg ι) (j : ι) : Accumulator cfg :=
  BitVec.ofInt cfg.accWidth
    ((ctx.unwrappedNeighborWeightInt j * (ctx.bgNeighbor j).toNat) / cfg.scale)

noncomputable def unwrappedTotalWeightInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, ctx.unwrappedNeighborWeightInt j

noncomputable def unwrappedForegroundSumInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, (ctx.unwrappedNeighborWeightInt j * (ctx.fgNeighbor j).toNat) / cfg.scale

noncomputable def unwrappedBackgroundSumInt (ctx : FixedLocalContext cfg ι) : Int :=
  ∑ j, (ctx.unwrappedNeighborWeightInt j * (ctx.bgNeighbor j).toNat) / cfg.scale

noncomputable def wrappedTotalWeight (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  BitVec.ofInt cfg.accWidth ctx.unwrappedTotalWeightInt

noncomputable def wrappedForegroundSum (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  BitVec.ofInt cfg.accWidth ctx.unwrappedForegroundSumInt

noncomputable def wrappedBackgroundSum (ctx : FixedLocalContext cfg ι) : Accumulator cfg :=
  BitVec.ofInt cfg.accWidth ctx.unwrappedBackgroundSumInt

structure LocalRangeCert (ctx : FixedLocalContext cfg ι) : Prop where
  totalWeightFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedTotalWeightInt
  foregroundSumFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedForegroundSumInt
  backgroundSumFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedBackgroundSumInt

def NoWrapLocalStep (ctx : FixedLocalContext cfg ι) : Prop :=
  (ctx.wrappedTotalWeight.toInt = ctx.unwrappedTotalWeightInt) ∧
    (ctx.wrappedForegroundSum.toInt = ctx.unwrappedForegroundSumInt) ∧
    (ctx.wrappedBackgroundSum.toInt = ctx.unwrappedBackgroundSumInt)

theorem NoWrapLocalStep_of_rangeCert (ctx : FixedLocalContext cfg ι)
    (hcfg : 0 < cfg.accWidth) (h : LocalRangeCert ctx) :
    ctx.NoWrapLocalStep := by
  rcases h with ⟨hW, hF, hB⟩
  refine ⟨?_, ?_, ?_⟩
  · exact BitVec.toInt_ofInt_eq_self hcfg hW.1 (by
      have hs : FastMLFE2.FixedPrecision.signedMax cfg < (2 : Int) ^ (cfg.accWidth - 1) := by
        simp [FastMLFE2.FixedPrecision.signedMax]
      exact lt_of_le_of_lt hW.2 hs)
  · exact BitVec.toInt_ofInt_eq_self hcfg hF.1 (by
      have hs : FastMLFE2.FixedPrecision.signedMax cfg < (2 : Int) ^ (cfg.accWidth - 1) := by
        simp [FastMLFE2.FixedPrecision.signedMax]
      exact lt_of_le_of_lt hF.2 hs)
  · exact BitVec.toInt_ofInt_eq_self hcfg hB.1 (by
      have hs : FastMLFE2.FixedPrecision.signedMax cfg < (2 : Int) ^ (cfg.accWidth - 1) := by
        simp [FastMLFE2.FixedPrecision.signedMax]
      exact lt_of_le_of_lt hB.2 hs)

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
