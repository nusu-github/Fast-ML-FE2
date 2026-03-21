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

@[extern "lean_fastmlfe2_gray_image_paper_refine_pass"]
private opaque paperRefinePassImpl
    (image alpha fg bg : @& NativeGrayImage) (epsR omega : Float) :
    IO (NativeGrayImage × NativeGrayImage)

@[extern "lean_fastmlfe2_gray_image_clamp01"]
private opaque clamp01Impl (image : @& NativeGrayImage) : IO PUnit

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

def paperRefinePass
    (image alpha fg bg : NativeGrayImage) (epsR omega : Float) :
    IO (NativeGrayImage × NativeGrayImage) :=
  paperRefinePassImpl image alpha fg bg epsR omega

def clamp01 (image : NativeGrayImage) : IO PUnit :=
  clamp01Impl image

end NativeGrayImage

end FastMLFE2
