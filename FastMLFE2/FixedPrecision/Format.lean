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
  roundingMode : RoundingMode := .nearest
  wordWidthPos : 0 < wordWidth
  accWidthPos : 0 < accWidth
  scalePos : 0 < scale
  deriving Repr

abbrev Storage (cfg : FixedFormat) := BitVec cfg.wordWidth

abbrev Accumulator (cfg : FixedFormat) := BitVec cfg.accWidth

abbrev FixedUnknown (cfg : FixedFormat) := Storage cfg × Storage cfg

def maxCode (cfg : FixedFormat) : Nat :=
  2 ^ cfg.wordWidth - 1

noncomputable def decodeStorage (cfg : FixedFormat) (x : Storage cfg) : ℝ :=
  (x.toNat : ℝ) / cfg.scale

noncomputable def decodeAccumulator (cfg : FixedFormat) (x : Accumulator cfg) : ℝ :=
  (x.toInt : ℝ) / cfg.scale

noncomputable def decodeUnknown (cfg : FixedFormat) (g : FixedUnknown cfg) : LocalUnknown :=
  mkLocalUnknown (decodeStorage cfg g.1) (decodeStorage cfg g.2)

noncomputable def roundedNat (x : ℝ) : Nat :=
  Int.toNat (Int.floor (x + (1 : ℝ) / 2))

noncomputable def encodeNearestNat (cfg : FixedFormat) (x : ℝ) : Nat :=
  min (maxCode cfg) (roundedNat (clamp01Scalar x * cfg.scale))

noncomputable def encodeNearestClamp01 (cfg : FixedFormat) (x : ℝ) : Storage cfg :=
  BitVec.ofNat cfg.wordWidth (encodeNearestNat cfg x)

noncomputable def encodeSigned (cfg : FixedFormat) (x : ℝ) : Accumulator cfg :=
  ((Int.floor (x * cfg.scale + (1 : ℝ) / 2)) : BitVec cfg.accWidth)

def castStorageToAccumulator (cfg : FixedFormat) (x : Storage cfg) : Accumulator cfg :=
  BitVec.ofNat cfg.accWidth x.toNat

def wrapAdd (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  x + y

def wrapSub (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  x - y

def wrapScaleMul (cfg : FixedFormat) (x y : Accumulator cfg) : Accumulator cfg :=
  (((x.toInt * y.toInt) / cfg.scale : Int) : BitVec cfg.accWidth)

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
  wordWidthPos := by decide
  accWidthPos := by decide
  scalePos := by decide

end FastMLFE2.FixedPrecision
