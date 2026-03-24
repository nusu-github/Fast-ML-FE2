import FastMLFE2.Canonical.LocalCommitments

namespace FastMLFE2.Canonical

/-!
Canonical multilevel schedule definitions for authored semantics.
-/

def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    Nat.log2 (n - 1) + 1

def roundFloatToNatAtLeastOne (x : Float) : Nat :=
  max 1 (Float.round x).toUInt64.toNat

def levelSizeAt (size level levelCount : Nat) : Nat :=
  if levelCount = 0 then
    size
  else
    roundFloatToNatAtLeastOne
      ((Float.ofNat size) ^ (Float.ofNat level / Float.ofNat levelCount))

def levelCount (width height : Nat) : Nat :=
  ceilLog2 (max width height)

def levelSizes (width height : Nat) : List (Nat × Nat) :=
  let levels := levelCount width height
  if levels = 0 then
    [(width, height)]
  else
    (List.range (levels + 1)).map fun level =>
      ((levelSizeAt width level levels), (levelSizeAt height level levels))

@[simp] theorem ceilLog2_zero : ceilLog2 0 = 0 := by
  simp [ceilLog2]

@[simp] theorem ceilLog2_one : ceilLog2 1 = 0 := by
  simp [ceilLog2]

@[simp] theorem levelCount_eq_ceilLog2 (width height : Nat) :
    levelCount width height = ceilLog2 (max width height) := rfl

end FastMLFE2.Canonical
