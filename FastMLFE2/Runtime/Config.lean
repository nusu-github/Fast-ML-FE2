namespace FastMLFE2.Runtime

inductive LevelSchedule where
  | auto
  | manual (count : Nat)
  deriving BEq, DecidableEq, Repr

structure ExecutionConfig where
  levels : LevelSchedule
  smallSize : Nat
  nSmallIterations : Nat
  nBigIterations : Nat
  epsR : Float
  omega : Float

def defaultConfig : ExecutionConfig :=
  { levels := .auto
  , smallSize := 32
  , nSmallIterations := 10
  , nBigIterations := 2
  , epsR := 0.00001
  , omega := 1.0
  }

def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    Nat.log2 (n - 1) + 1

def roundFloatToNatAtLeastOne (x : Float) : Nat :=
  max 1 (UInt64.toNat (Float.toUInt64 (Float.round x)))

def levelSizeAt (size level levelCount : Nat) : Nat :=
  if levelCount = 0 then
    size
  else
    roundFloatToNatAtLeastOne
      ((Float.ofNat size) ^ (Float.ofNat level / Float.ofNat levelCount))

def autoLevelSizes (width height : Nat) : List (Nat × Nat) :=
  let levelCount := ceilLog2 (max width height)
  if levelCount = 0 then
    [(width, height)]
  else
    (List.range (levelCount + 1)).map fun level =>
      (levelSizeAt width level levelCount, levelSizeAt height level levelCount)

def manualLevelSizes (width height count : Nat) : List (Nat × Nat) :=
  if count = 0 then
    []
  else if count = 1 then
    [(width, height)]
  else
    (List.range count).map fun level =>
      (levelSizeAt width level (count - 1), levelSizeAt height level (count - 1))

def levelSizes (width height : Nat) (levels : LevelSchedule) : List (Nat × Nat) :=
  match levels with
  | .auto => autoLevelSizes width height
  | .manual count => manualLevelSizes width height count

def iterationsForLevel (config : ExecutionConfig) (width height : Nat) : Nat :=
  if width ≤ config.smallSize && height ≤ config.smallSize then
    config.nSmallIterations
  else
    config.nBigIterations

end FastMLFE2.Runtime
