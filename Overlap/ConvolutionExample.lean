import Overlap.PackedConvolution

namespace Overlap.ConvolutionExample
open PackedConvolution

private def lhs : Tree :=
  .node (.node (.node (.leaf 3) (.leaf 1)) (.node (.leaf 4) (.leaf 0)))
    (.node (.node (.leaf 2) (.leaf 6)) (.node (.leaf 5) (.leaf 7)))

private def rhs : Tree :=
  .node (.node (.leaf 2) (.leaf 5)) (.node (.leaf 1) (.node (.leaf 3) (.leaf 0)))

private def certificate : Tree :=
  .node
    (.node (.node (.leaf 6) (.leaf 17)) (.node (.leaf 16) (.node (.leaf 30) (.leaf 11))))
    (.node (.node (.leaf 34) (.node (.leaf 42) (.leaf 51)))
      (.node (.leaf 58) (.node (.leaf 22) (.node (.leaf 21) (.leaf 0)))))

/-- An independent 8-by-5 certificate, with a zero at the highest degree. -/
theorem rectangular_convolution :
    convolution [3, 1, 4, 0, 2, 6, 5, 7] [2, 5, 1, 3, 0] =
      [6, 17, 16, 30, 11, 34, 42, 51, 58, 22, 21, 0] := by
  have checked := tree_certified (xs := lhs) (ys := rhs) (proposed := certificate)
    (base := 2048) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact checked

end Overlap.ConvolutionExample
