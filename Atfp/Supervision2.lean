module

import Atfp.Chapter4.Section4.Datafun

namespace Datafun

def Ty.Δ : Ty → Ty
  | .unit => .unit
  | .prod A B => .prod A.Δ B.Δ
  | .arr A B => .arr (.prod (.discrete A) A.Δ) B.Δ
  | .coprod A B => .coprod A.Δ B.Δ
  | .powerset T => .powerset T
  | .discrete _ => .unit

end Datafun
