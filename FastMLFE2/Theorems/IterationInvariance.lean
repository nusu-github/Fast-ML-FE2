import FastMLFE2.Theorems.ChannelReuse
import FastMLFE2.Theorems.CanonicalBuilder

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Level
open FastMLFE2.Canonical

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

theorem neighborWeight_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ)
    (j : η p) :
    (data.canonicalBuilder.build p state₁).neighborWeight j =
      (data.canonicalBuilder.build p state₂).neighborWeight j :=
  FastMLFE2.Theorems.LocalContext.neighborWeight_eq_of_sameWeightData
    (canonicalBuilder_sameWeightData data p state₁ state₂) j

theorem totalWeight_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ) :
    (data.canonicalBuilder.build p state₁).totalWeight =
      (data.canonicalBuilder.build p state₂).totalWeight :=
  FastMLFE2.Theorems.LocalContext.totalWeight_eq_of_sameWeightData
    (canonicalBuilder_sameWeightData data p state₁ state₂)

theorem weightedMeanDenom_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ) :
    (data.canonicalBuilder.build p state₁).weightedMeanDenom =
      (data.canonicalBuilder.build p state₂).weightedMeanDenom :=
  FastMLFE2.Theorems.LocalContext.weightedMeanDenom_eq_of_sameWeightData
    (canonicalBuilder_sameWeightData data p state₁ state₂)

theorem normalMatrix_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ) :
    (data.canonicalBuilder.build p state₁).normalMatrix =
      (data.canonicalBuilder.build p state₂).normalMatrix :=
  FastMLFE2.Theorems.LocalContext.normalMatrix_eq_of_sameWeightData
    (canonicalBuilder_sameWeightData data p state₁ state₂)

theorem closedFormDenom_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ) :
    FastMLFE2.Theorems.LocalContext.closedFormDenom (data.canonicalBuilder.build p state₁) =
      FastMLFE2.Theorems.LocalContext.closedFormDenom (data.canonicalBuilder.build p state₂) :=
  FastMLFE2.Theorems.LocalContext.closedFormDenom_eq_of_sameWeightData
    (canonicalBuilder_sameWeightData data p state₁ state₂)

theorem branchClass_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ)
    (tau : ℝ) :
    (if (data.canonicalBuilder.build p state₁).alphaCenter ≤ tau then 0 else
        if 1 - tau ≤ (data.canonicalBuilder.build p state₁).alphaCenter then 1 else 2) =
      (if (data.canonicalBuilder.build p state₂).alphaCenter ≤ tau then 0 else
        if 1 - tau ≤ (data.canonicalBuilder.build p state₂).alphaCenter then 1 else 2) := by
  simp [CanonicalPixelData.canonicalBuilder, CanonicalPixelData.toLocalContext]

theorem cacheRelevantCoefficients_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ)
    (tau : ℝ) :
    (data.canonicalBuilder.build p state₁).totalWeight =
      (data.canonicalBuilder.build p state₂).totalWeight ∧
    (data.canonicalBuilder.build p state₁).weightedMeanDenom =
      (data.canonicalBuilder.build p state₂).weightedMeanDenom ∧
    FastMLFE2.Theorems.LocalContext.closedFormDenom (data.canonicalBuilder.build p state₁) =
      FastMLFE2.Theorems.LocalContext.closedFormDenom (data.canonicalBuilder.build p state₂) ∧
    (data.canonicalBuilder.build p state₁).normalMatrix =
      (data.canonicalBuilder.build p state₂).normalMatrix ∧
    (if (data.canonicalBuilder.build p state₁).alphaCenter ≤ tau then 0 else
        if 1 - tau ≤ (data.canonicalBuilder.build p state₁).alphaCenter then 1 else 2) =
      (if (data.canonicalBuilder.build p state₂).alphaCenter ≤ tau then 0 else
        if 1 - tau ≤ (data.canonicalBuilder.build p state₂).alphaCenter then 1 else 2) := by
  constructor
  · exact totalWeight_eq_of_build data p state₁ state₂
  · constructor
    · exact weightedMeanDenom_eq_of_build data p state₁ state₂
    · constructor
      · exact closedFormDenom_eq_of_build data p state₁ state₂
      · constructor
        · exact normalMatrix_eq_of_build data p state₁ state₂
        · exact branchClass_eq_of_build data p state₁ state₂ tau

theorem zeroBranchPredicate_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ)
    (tau : ℝ) :
    (data.canonicalBuilder.build p state₁).alphaCenter ≤ tau ↔
      (data.canonicalBuilder.build p state₂).alphaCenter ≤ tau := by
  simp [CanonicalPixelData.canonicalBuilder, CanonicalPixelData.toLocalContext]

theorem oneBranchPredicate_eq_of_build
    (data : CanonicalPixelData κ η)
    (p : κ)
    (state₁ state₂ : PixelState κ)
    (tau : ℝ) :
    1 - tau ≤ (data.canonicalBuilder.build p state₁).alphaCenter ↔
      1 - tau ≤ (data.canonicalBuilder.build p state₂).alphaCenter := by
  simp [CanonicalPixelData.canonicalBuilder, CanonicalPixelData.toLocalContext]

end CanonicalPixelData

end FastMLFE2.Theorems
