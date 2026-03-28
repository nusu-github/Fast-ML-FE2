import FastMLFE2.Theorems.FixedPrecision.FixedPrecisionLocal

namespace FastMLFE2.Theorems

open FastMLFE2.FixedPrecision

namespace FixedPrecision

def tinyWrapFormat : FixedFormat where
  wordWidth := 3
  accWidth := 4
  scale := 1
  wordWidthPos := by decide
  accWidthPos := by decide
  scalePos := by decide

def wrappedFourBitSum : Accumulator tinyWrapFormat :=
  wrapAdd tinyWrapFormat (BitVec.ofNat 4 7) (BitVec.ofNat 4 7)

example : wrappedFourBitSum.toInt = -2 := by decide

theorem wraparound_counterexample :
    wrappedFourBitSum.toInt ≠ (14 : Int) := by decide

end FixedPrecision

end FastMLFE2.Theorems
