import Atfp.Chapter4.Section4.Compiler

namespace Datafun

def test (e : Tm.{0}) : String :=
  match typeCheck [] e with
  | some ⟨_, h⟩ => Datafun.compile h .nil
  | none => "fail"

#eval test (.abs .unit (.var 0))
#eval test (.app (.abs .unit (.var 0)) .unit)
#eval test (.abs (.prod .unit .unit) (.prod (.fst (.var 0)) (.snd (.var 0))))
#eval test (.let (.disc .unit) (.var 0))
#eval test (.sup (.powerset .unit) (.bot (.powerset .unit)) (.bot (.powerset .unit)))
#eval test (.sup (.prod .unit (.powerset .unit))
  (.bot (.prod .unit (.powerset .unit))) (.bot (.prod .unit (.powerset .unit))))
#eval test (.one .unit)
#eval test (.for (.one .unit) (.one (.var 0)))
#eval test (.fix (.powerset .unit) (.bot (.powerset .unit)))
#eval
  let h := HasType.dvar (Γ := ([(.D, .unit)] : Ctx.{0})) 0 .unit rfl
  Datafun.compile h (.cons "x" .nil)
#eval test (.abs (.coprod .unit .unit) (.case (.var 0) (.var 0) (.var 0)))
#eval
  let h := HasType.coprod_intro₁ (Γ := ([(.none, .unit)] : Ctx.{0})) _ _ .unit
    (.var 0 .unit rfl)
  Datafun.compile h (.cons "x" .nil)

end Datafun
