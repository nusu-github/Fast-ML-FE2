import Mathlib.Data.BitVec
import FastMLFE2.Core.LocalEquation

namespace FastMLFE2.FixedPrecision

open FastMLFE2.Core

inductive RoundingMode where
  | nearest
  deriving DecidableEq, Repr

structure FixedFormat where
  wordWidth : Nat
  accWidth : Nat
  scale : Nat
  coeffFracBits : Nat := 12
  recipFracBits : Nat := 16
  weightScale : Nat := scale
  branchTauLow : Nat := 0
  branchTauHigh : Nat := scale
  roundingMode : RoundingMode := .nearest
  wordWidthPos : 0 < wordWidth
  accWidthPos : 0 < accWidth
  scalePos : 0 < scale
  weightScalePos : 0 < weightScale := by
    simp_all
  deriving Repr

abbrev Storage (cfg : FixedFormat) := BitVec cfg.wordWidth

abbrev Accumulator (cfg : FixedFormat) := BitVec cfg.accWidth

abbrev Coefficient (cfg : FixedFormat) := BitVec cfg.accWidth

abbrev FixedUnknown (cfg : FixedFormat) := Storage cfg × Storage cfg

def coeffScale (cfg : FixedFormat) : Nat :=
  2 ^ cfg.coeffFracBits

def recipScale (cfg : FixedFormat) : Nat :=
  2 ^ cfg.recipFracBits

def maxCode (cfg : FixedFormat) : Nat :=
  2 ^ cfg.wordWidth - 1

def signedMin (cfg : FixedFormat) : Int :=
  -((2 : Int) ^ (cfg.accWidth - 1))

def signedMax (cfg : FixedFormat) : Int :=
  (2 : Int) ^ (cfg.accWidth - 1) - 1

def IntFitsAcc (cfg : FixedFormat) (z : Int) : Prop :=
  signedMin cfg ≤ z ∧ z ≤ signedMax cfg

noncomputable def decodeStorage (cfg : FixedFormat) (x : Storage cfg) : ℝ :=
  (x.toNat : ℝ) / cfg.scale

noncomputable def decodeAccumulator (cfg : FixedFormat) (x : Accumulator cfg) : ℝ :=
  (x.toInt : ℝ) / cfg.scale

noncomputable def decodeUnknown (cfg : FixedFormat) (g : FixedUnknown cfg) : LocalUnknown :=
  mkLocalUnknown (decodeStorage cfg g.1) (decodeStorage cfg g.2)

noncomputable def decodeCoefficient (cfg : FixedFormat) (x : Coefficient cfg) : ℝ :=
  (x.toNat : ℝ) / coeffScale cfg

noncomputable def roundedNat (x : ℝ) : Nat :=
  Int.toNat (Int.floor (x + (1 : ℝ) / 2))

noncomputable def encodeNearestNat (cfg : FixedFormat) (x : ℝ) : Nat :=
  min (maxCode cfg) (roundedNat (clamp01Scalar x * cfg.scale))

noncomputable def encodeNearestClamp01 (cfg : FixedFormat) (x : ℝ) : Storage cfg :=
  BitVec.ofNat cfg.wordWidth (encodeNearestNat cfg x)

noncomputable def encodeSigned (cfg : FixedFormat) (x : ℝ) : Accumulator cfg :=
  ((Int.floor (x * cfg.scale + (1 : ℝ) / 2)) : BitVec cfg.accWidth)

noncomputable def encodeCoefficientFloor (cfg : FixedFormat) (x : ℝ) : Coefficient cfg :=
  BitVec.ofNat cfg.accWidth (Int.toNat (Int.floor (x * coeffScale cfg)))

noncomputable def encodeScaledRatioFloor
    (cfg : FixedFormat) (numer denom : Nat) : Coefficient cfg :=
  if denom = 0 then
    0
  else
    encodeCoefficientFloor cfg ((numer : ℝ) / denom)

def castStorageToAccumulator (cfg : FixedFormat) (x : Storage cfg) : Accumulator cfg :=
  BitVec.ofNat cfg.accWidth x.toNat

def wrapAdd (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  x + y

def wrapSub (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  x - y

def wrapScaleMul (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  (((x.toInt * y.toInt) / cfg.scale : Int) : BitVec cfg.accWidth)

def clampCodeNat (cfg : FixedFormat) (n : Nat) : Nat :=
  min cfg.scale n

def storageOfCode (cfg : FixedFormat) (n : Nat) : Storage cfg :=
  BitVec.ofNat cfg.wordWidth (clampCodeNat cfg n)

def storageLeScale (cfg : FixedFormat) (x : Storage cfg) : Prop :=
  x.toNat ≤ cfg.scale

def isLowBranch (cfg : FixedFormat) (x : Storage cfg) : Prop :=
  x.toNat ≤ cfg.branchTauLow

def isHighBranch (cfg : FixedFormat) (x : Storage cfg) : Prop :=
  cfg.branchTauHigh ≤ x.toNat

@[simp] theorem decodeUnknown_foreground (cfg : FixedFormat) (g : FixedUnknown cfg) :
    foreground (decodeUnknown cfg g) = decodeStorage cfg g.1 := by
  simp [decodeUnknown]

@[simp] theorem decodeUnknown_background (cfg : FixedFormat) (g : FixedUnknown cfg) :
    background (decodeUnknown cfg g) = decodeStorage cfg g.2 := by
  simp [decodeUnknown]

@[simp] theorem castStorageToAccumulator_toNat (cfg : FixedFormat) (x : Storage cfg) :
    (castStorageToAccumulator cfg x).toNat = x.toNat % 2 ^ cfg.accWidth := by
  simp [castStorageToAccumulator]

def u8Format : FixedFormat where
  wordWidth := 8
  accWidth := 32
  scale := 255
  coeffFracBits := 12
  recipFracBits := 16
  weightScale := 255
  branchTauLow := 3
  branchTauHigh := 252
  wordWidthPos := by decide
  accWidthPos := by decide
  scalePos := by decide
  weightScalePos := by decide

end FastMLFE2.FixedPrecision
