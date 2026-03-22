open System

namespace FastMLFE2

private opaque NativeGrayImageImpl : NonemptyType

def NativeGrayImage : Type := NativeGrayImageImpl.type

instance : Nonempty NativeGrayImage := NativeGrayImageImpl.property

@[extern "lean_fastmlfe2_gray_image_of_float_array"]
private opaque ofFloatArrayImpl (width height : UInt32) (data : @& FloatArray) : IO NativeGrayImage

@[extern "lean_fastmlfe2_gray_image_to_float_array"]
private opaque toFloatArrayImpl (image : @& NativeGrayImage) : IO FloatArray

@[extern "lean_fastmlfe2_gray_image_width"]
private opaque widthImpl (image : @& NativeGrayImage) : IO UInt32

@[extern "lean_fastmlfe2_gray_image_height"]
private opaque heightImpl (image : @& NativeGrayImage) : IO UInt32

@[extern "lean_fastmlfe2_gray_image_resize"]
private opaque resizeImpl (image : @& NativeGrayImage) (width height : UInt32) : IO NativeGrayImage

@[extern "lean_fastmlfe2_gray_image_resize_nearest"]
private opaque resizeNearestImpl (image : @& NativeGrayImage) (width height : UInt32) : IO NativeGrayImage

@[extern "lean_fastmlfe2_gray_image_reference_refine_single_pass"]
private opaque referenceRefineSinglePassImpl
    (image alpha fg bg : @& NativeGrayImage) (epsR omega : Float) :
    IO (NativeGrayImage × NativeGrayImage)

@[extern "lean_fastmlfe2_gray_image_clamp01"]
private opaque clamp01Impl (image : @& NativeGrayImage) : IO PUnit

@[extern "lean_fastmlfe2_gray_image_read_png_gray"]
private opaque readPngGrayImpl (path : @& String) : IO NativeGrayImage

@[extern "lean_fastmlfe2_gray_image_write_png_gray"]
private opaque writePngGrayImpl (path : @& String) (image : @& NativeGrayImage) : IO PUnit

@[extern "lean_fastmlfe2_gray_image_read_png_rgb_channel"]
private opaque readPngRgbChannelImpl (path : @& String) (channel : UInt32) : IO NativeGrayImage

@[extern "lean_fastmlfe2_gray_image_write_png_rgb"]
private opaque writePngRgbImpl
    (path : @& String) (red green blue : @& NativeGrayImage) : IO PUnit

private abbrev NativeGrayTriple := NativeGrayImage × (NativeGrayImage × NativeGrayImage)

@[extern "lean_fastmlfe2_rgb_image_reference_refine"]
private opaque referenceRefineImpl
    (imageRed imageGreen imageBlue alpha : @& NativeGrayImage)
    (fgRed fgGreen fgBlue bgRed bgGreen bgBlue : @& NativeGrayImage)
    (iterations : UInt32) (epsR omega residualTol updateTol : Float) :
    IO (NativeGrayTriple × NativeGrayTriple)

@[extern "lean_fastmlfe2_rgb_image_global_spd_vcycle"]
private opaque globalSpdVcycleImpl
    (imageRed imageGreen imageBlue alpha : @& NativeGrayImage)
    (fgRed fgGreen fgBlue bgRed bgGreen bgBlue : @& NativeGrayImage)
    (levelCount maxCycles preSmoothing postSmoothing coarseIterations : UInt32)
    (epsR omega residualTol : Float) :
    IO (NativeGrayTriple × NativeGrayTriple)

private def maxDim : Nat := 2 ^ 32 - 1

private def toDim32 (name : String) (n : Nat) : IO UInt32 := do
  if n ≤ maxDim then
    return UInt32.ofNat n
  else
    throw <| IO.userError s!"{name} exceeds UInt32 range: {n}"

namespace NativeGrayImage

def ofFloatArray (width height : Nat) (data : FloatArray) : IO NativeGrayImage := do
  ofFloatArrayImpl (← toDim32 "width" width) (← toDim32 "height" height) data

def toFloatArray (image : NativeGrayImage) : IO FloatArray :=
  toFloatArrayImpl image

def width (image : NativeGrayImage) : IO Nat := do
  return UInt32.toNat (← widthImpl image)

def height (image : NativeGrayImage) : IO Nat := do
  return UInt32.toNat (← heightImpl image)

def resize (image : NativeGrayImage) (width height : Nat) : IO NativeGrayImage := do
  resizeImpl image (← toDim32 "width" width) (← toDim32 "height" height)

def resizeNearest (image : NativeGrayImage) (width height : Nat) : IO NativeGrayImage := do
  resizeNearestImpl image (← toDim32 "width" width) (← toDim32 "height" height)

def referenceRefineSinglePass
    (image alpha fg bg : NativeGrayImage) (epsR omega : Float) :
    IO (NativeGrayImage × NativeGrayImage) :=
  referenceRefineSinglePassImpl image alpha fg bg epsR omega

def clamp01 (image : NativeGrayImage) : IO PUnit :=
  clamp01Impl image

def readPngGray (path : FilePath) : IO NativeGrayImage :=
  readPngGrayImpl path.toString

def writePngGray (path : FilePath) (image : NativeGrayImage) : IO PUnit :=
  writePngGrayImpl path.toString image

def readPngRgbChannel (path : FilePath) (channel : Nat) : IO NativeGrayImage := do
  if channel < 3 then
    readPngRgbChannelImpl path.toString (UInt32.ofNat channel)
  else
    throw <| IO.userError s!"RGB channel index out of range: {channel}"

end NativeGrayImage

structure NativeRgbImage where
  red : NativeGrayImage
  green : NativeGrayImage
  blue : NativeGrayImage

namespace NativeRgbImage

def width (image : NativeRgbImage) : IO Nat :=
  image.red.width

def height (image : NativeRgbImage) : IO Nat :=
  image.red.height

private def assertSameShapeGray
    (context : String) (reference other : NativeGrayImage) : IO PUnit := do
  let rw ← reference.width
  let rh ← reference.height
  let ow ← other.width
  let oh ← other.height
  if rw != ow || rh != oh then
    throw <| IO.userError
      s!"{context}: shape mismatch, expected {rw}x{rh}, got {ow}x{oh}"

def assertWellFormed (image : NativeRgbImage) : IO PUnit := do
  assertSameShapeGray "NativeRgbImage" image.red image.green
  assertSameShapeGray "NativeRgbImage" image.red image.blue

private def assertCompatibleRefineInputs
    (image : NativeRgbImage) (alpha : NativeGrayImage)
    (fg bg : NativeRgbImage) : IO PUnit := do
  image.assertWellFormed
  fg.assertWellFormed
  bg.assertWellFormed
  assertSameShapeGray "NativeRgbImage.referenceRefine image/alpha" image.red alpha
  assertSameShapeGray "NativeRgbImage.referenceRefine image/fg" image.red fg.red
  assertSameShapeGray "NativeRgbImage.referenceRefine image/bg" image.red bg.red

def readPng (path : FilePath) : IO NativeRgbImage := do
  let image : NativeRgbImage := {
    red := ← NativeGrayImage.readPngRgbChannel path 0
    green := ← NativeGrayImage.readPngRgbChannel path 1
    blue := ← NativeGrayImage.readPngRgbChannel path 2
  }
  image.assertWellFormed
  pure image

def writePng (path : FilePath) (image : NativeRgbImage) : IO PUnit := do
  image.assertWellFormed
  writePngRgbImpl path.toString image.red image.green image.blue

def resize (image : NativeRgbImage) (width height : Nat) : IO NativeRgbImage := do
  pure {
    red := ← image.red.resize width height
    green := ← image.green.resize width height
    blue := ← image.blue.resize width height
  }

def resizeNearest (image : NativeRgbImage) (width height : Nat) : IO NativeRgbImage := do
  pure {
    red := ← image.red.resizeNearest width height
    green := ← image.green.resizeNearest width height
    blue := ← image.blue.resizeNearest width height
  }

def clamp01 (image : NativeRgbImage) : IO PUnit := do
  image.red.clamp01
  image.green.clamp01
  image.blue.clamp01

def referenceRefine
    (maxIterations : Nat)
    (image : NativeRgbImage) (alpha : NativeGrayImage)
    (fg bg : NativeRgbImage) (epsR omega residualTol updateTol : Float) :
    IO (NativeRgbImage × NativeRgbImage) := do
  assertCompatibleRefineInputs image alpha fg bg
  let ((fgR, (fgG, fgB)), (bgR, (bgG, bgB))) ←
    referenceRefineImpl
      image.red image.green image.blue alpha
      fg.red fg.green fg.blue
      bg.red bg.green bg.blue
      (← toDim32 "maxIterations" maxIterations)
      epsR omega residualTol updateTol
  pure
    ({ red := fgR, green := fgG, blue := fgB },
     { red := bgR, green := bgG, blue := bgB })

def globalSpdVcycle
    (levelCount maxCycles preSmoothing postSmoothing coarseIterations : Nat)
    (image : NativeRgbImage) (alpha : NativeGrayImage)
    (fg bg : NativeRgbImage) (epsR omega residualTol : Float) :
    IO (NativeRgbImage × NativeRgbImage) := do
  assertCompatibleRefineInputs image alpha fg bg
  let ((fgR, (fgG, fgB)), (bgR, (bgG, bgB))) ←
    globalSpdVcycleImpl
      image.red image.green image.blue alpha
      fg.red fg.green fg.blue
      bg.red bg.green bg.blue
      (← toDim32 "levelCount" levelCount)
      (← toDim32 "maxCycles" maxCycles)
      (← toDim32 "preSmoothing" preSmoothing)
      (← toDim32 "postSmoothing" postSmoothing)
      (← toDim32 "coarseIterations" coarseIterations)
      epsR omega residualTol
  pure
    ({ red := fgR, green := fgG, blue := fgB },
     { red := bgR, green := bgG, blue := bgB })

end NativeRgbImage

end FastMLFE2
