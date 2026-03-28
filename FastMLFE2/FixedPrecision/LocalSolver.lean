import FastMLFE2.FixedPrecision.Format
import FastMLFE2.FixedPrecision.Coefficients

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

noncomputable def unwrappedTotalWeightNat (ctx : FixedLocalContext cfg ι) : Nat :=
  Int.toNat ctx.unwrappedTotalWeightInt

noncomputable def unwrappedForegroundSumNat (ctx : FixedLocalContext cfg ι) : Nat :=
  Int.toNat ctx.unwrappedForegroundSumInt

noncomputable def unwrappedBackgroundSumNat (ctx : FixedLocalContext cfg ι) : Nat :=
  Int.toNat ctx.unwrappedBackgroundSumInt

def alphaCode (ctx : FixedLocalContext cfg ι) : Nat :=
  min cfg.scale ctx.alphaCenter.toNat

def alphaComplementCode (ctx : FixedLocalContext cfg ι) : Nat :=
  cfg.scale - ctx.alphaCode

def imageCode (ctx : FixedLocalContext cfg ι) : Nat :=
  min cfg.scale ctx.imageValue.toNat

def branchIsLow (ctx : FixedLocalContext cfg ι) : Prop :=
  isLowBranch cfg ctx.alphaCenter

def branchIsHigh (ctx : FixedLocalContext cfg ι) : Prop :=
  isHighBranch cfg ctx.alphaCenter

noncomputable def invTotalWeightCoeff (ctx : FixedLocalContext cfg ι) : Coefficient cfg :=
  weightReciprocalCoeff cfg ctx.unwrappedTotalWeightNat

noncomputable def invWeightPlusScaleCoeff (ctx : FixedLocalContext cfg ι) : Coefficient cfg :=
  weightReciprocalCoeff cfg (ctx.unwrappedTotalWeightNat + cfg.scale)

noncomputable def gainDenomNat (ctx : FixedLocalContext cfg ι) : Nat :=
  ctx.unwrappedTotalWeightNat * cfg.scale + ctx.alphaCode ^ 2 + ctx.alphaComplementCode ^ 2

noncomputable def invGainDenomCoeff (ctx : FixedLocalContext cfg ι) : Coefficient cfg :=
  gainReciprocalCoeff cfg ctx.gainDenomNat

noncomputable def foregroundMeanCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  (ctx.unwrappedForegroundSumInt * ctx.invTotalWeightCoeff.toNat) / coeffScale cfg

noncomputable def backgroundMeanCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  (ctx.unwrappedBackgroundSumInt * ctx.invTotalWeightCoeff.toNat) / coeffScale cfg

noncomputable def residualNumeratorInt (ctx : FixedLocalContext cfg ι) : Int :=
  (ctx.imageCode : Int) * cfg.scale -
    (ctx.alphaCode : Int) * ctx.foregroundMeanCodeInt -
    (ctx.alphaComplementCode : Int) * ctx.backgroundMeanCodeInt

noncomputable def foregroundGainCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  ((ctx.alphaCode : Int) * ctx.invGainDenomCoeff.toNat) / cfg.scale

noncomputable def backgroundGainCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  ((ctx.alphaComplementCode : Int) * ctx.invGainDenomCoeff.toNat) / cfg.scale

noncomputable def branchCorrectionCodeInt
    (ctx : FixedLocalContext cfg ι) (coeff : Int) : Int :=
  (coeff * ctx.residualNumeratorInt) / (coeffScale cfg * cfg.scale)

noncomputable def foregroundCorrectionCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  if _hLow : ctx.alphaCenter.toNat ≤ cfg.branchTauLow then
    0
  else if _hHigh : cfg.branchTauHigh ≤ ctx.alphaCenter.toNat then
    ctx.branchCorrectionCodeInt ctx.invWeightPlusScaleCoeff.toNat
  else
    ctx.branchCorrectionCodeInt ctx.foregroundGainCodeInt

noncomputable def backgroundCorrectionCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  if _hLow : ctx.alphaCenter.toNat ≤ cfg.branchTauLow then
    ctx.branchCorrectionCodeInt ctx.invWeightPlusScaleCoeff.toNat
  else if _hHigh : cfg.branchTauHigh ≤ ctx.alphaCenter.toNat then
    0
  else
    ctx.branchCorrectionCodeInt ctx.backgroundGainCodeInt

noncomputable def fullyFixedForegroundCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  ctx.foregroundMeanCodeInt + ctx.foregroundCorrectionCodeInt

noncomputable def fullyFixedBackgroundCodeInt (ctx : FixedLocalContext cfg ι) : Int :=
  ctx.backgroundMeanCodeInt + ctx.backgroundCorrectionCodeInt

noncomputable def fullyFixedForegroundCodeNat (ctx : FixedLocalContext cfg ι) : Nat :=
  clampCodeNat cfg (Int.toNat ctx.fullyFixedForegroundCodeInt)

noncomputable def fullyFixedBackgroundCodeNat (ctx : FixedLocalContext cfg ι) : Nat :=
  clampCodeNat cfg (Int.toNat ctx.fullyFixedBackgroundCodeInt)

structure LocalRangeCert (ctx : FixedLocalContext cfg ι) : Prop where
  totalWeightFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedTotalWeightInt
  foregroundSumFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedForegroundSumInt
  backgroundSumFits : FastMLFE2.FixedPrecision.IntFitsAcc cfg ctx.unwrappedBackgroundSumInt

def NoWrapLocalStep (ctx : FixedLocalContext cfg ι) : Prop :=
  (ctx.wrappedTotalWeight.toInt = ctx.unwrappedTotalWeightInt) ∧
    (ctx.wrappedForegroundSum.toInt = ctx.unwrappedForegroundSumInt) ∧
    (ctx.wrappedBackgroundSum.toInt = ctx.unwrappedBackgroundSumInt)

structure LocalSafetyCert (ctx : FixedLocalContext cfg ι) : Prop where
  range : LocalRangeCert ctx
  totalWeightPositive : 0 < ctx.unwrappedTotalWeightNat
  gainDenomPositive : 0 < ctx.gainDenomNat
  alphaCodeBound : ctx.alphaCenter.toNat ≤ cfg.scale
  imageCodeBound : ctx.imageValue.toNat ≤ cfg.scale

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

noncomputable def referenceFullyFixedStep (ctx : FixedLocalContext cfg ι) : FixedUnknown cfg :=
  (storageOfCode cfg ctx.fullyFixedForegroundCodeNat,
    storageOfCode cfg ctx.fullyFixedBackgroundCodeNat)

noncomputable def fullyFixedMeanResidualStep (ctx : FixedLocalContext cfg ι) : FixedUnknown cfg :=
  ctx.referenceFullyFixedStep

theorem decodedFullyFixedStep_eq_reference_of_safety
    (ctx : FixedLocalContext cfg ι)
    (_h : LocalSafetyCert ctx) :
    decodeUnknown cfg ctx.fullyFixedMeanResidualStep =
      decodeUnknown cfg ctx.referenceFullyFixedStep := by
  rfl

theorem LocalRangeCert.ofSafety
    (ctx : FixedLocalContext cfg ι)
    (h : LocalSafetyCert ctx) :
    LocalRangeCert ctx :=
  h.range

end FixedLocalContext

end FastMLFE2.FixedPrecision
