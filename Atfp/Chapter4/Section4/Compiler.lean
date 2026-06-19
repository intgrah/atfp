module

public import Atfp.Chapter4.Section4.TypeCheck

public section

namespace Datafun

variable {Γ : Ctx}

inductive Env : Ctx → Type where
  | nil : Env []
  | cons {q : Qualifier} {A : Ty} {Γ : Ctx} : String → Env Γ → Env ((q, A) :: Γ)

def Env.get {Γ : Ctx} : Env Γ → (x : Nat) → (p : Qualifier × Ty) → Γ[x]? = some p → String
  | .cons v _, 0, _, _ => v
  | .cons _ env, x + 1, _, h => env.get x _ h

def Env.disc {Γ : Ctx} : Env Γ → Env [Γ]ᵈ
  | .nil => .nil
  | .cons (q := .D) v env => .cons v env.disc
  | .cons (q := .none) _ env => env.disc

def FinTy.compile : FinTy → String
  | 1 => "()"
  | T₁ * T₂ => s!"({T₁.compile}, {T₂.compile})"
  | T₁ + T₂ => s!"(Either {T₁.compile} {T₂.compile})"
  | 𝒫' T => s!"[{T.compile}]"
  | .discrete T => T.compile

def Ty.compile : Ty → String
  | 1 => "()"
  | A * B => s!"({A.compile}, {B.compile})"
  | .arr A B => s!"({A.compile} -> {B.compile})"
  | A + B => s!"(Either {A.compile} {B.compile})"
  | 𝒫 T => s!"[{T.compile}]"
  | .discrete A => A.compile

def LatTy.compileBot : LatTy → String
  | .unit => "()"
  | .prod L₁ L₂ => s!"({L₁.compileBot}, {L₂.compileBot})"
  | .powerset _ => "[]"

def LatTy.compileSup (a b : String) : LatTy → String
  | .unit => "()"
  | .prod L₁ L₂ =>
    s!"(case ({a}, {b}) of \{ ((_l1, _l2), (_r1, _r2)) -> \
      ({L₁.compileSup "_l1" "_r1"}, {L₂.compileSup "_l2" "_r2"}) })"
  | .powerset _ => s!"(nub (sort ({a} ++ {b})))"

def LatTy.compileEq (a b : String) : LatTy → String
  | .unit => "True"
  | .prod L₁ L₂ =>
    s!"(case ({a}, {b}) of \{ ((_l1, _l2), (_r1, _r2)) -> \
      {L₁.compileEq "_l1" "_r1"} && {L₂.compileEq "_l2" "_r2"} })"
  | .powerset _ => s!"({a} == {b})"

abbrev M := StateM Nat

def fresh (prefix_ : String := "v") : M String :=
  modifyGet fun d => (s!"{prefix_}{d}", d + 1)

public def HasType.compile {Γ} (env : Env Γ) {e A} : (Γ ⊢ e : A) → M String
  | .var x A h => return env.get x (.none, A) h
  | .dvar x A h => return env.get x (.D, A) h
  | .unit_intro => return "()"
  | .prod_intro _ _ _ _ h₁ h₂ => do
    let c₁ ← h₁.compile env
    let c₂ ← h₂.compile env
    return s!"({c₁}, {c₂})"
  | .prod_elim₁ _ _ _ h => do
    let c ← h.compile env
    return s!"(fst {c})"
  | .prod_elim₂ _ _ _ h => do
    let c ← h.compile env
    return s!"(snd {c})"
  | .abs_intro _ A _ h => do
    let v ← fresh
    let c ← h.compile (.cons v env)
    return s!"(\\({v} :: {A.compile}) -> {c})"
  | .abs_elim _ _ _ _ h₁ h₂ => do
    let c₁ ← h₁.compile env
    let c₂ ← h₂.compile env
    return s!"({c₁} {c₂})"
  | .coprod_intro₁ _ _ _ h => do
    let c ← h.compile env
    return s!"(Left {c})"
  | .coprod_intro₂ _ _ _ h => do
    let c ← h.compile env
    return s!"(Right {c})"
  | .coprod_elim _ _ _ _ _ _ h h₁ h₂ => do
    let ce ← h.compile env
    let v₁ ← fresh
    let c₁ ← h₁.compile (.cons v₁ env)
    let v₂ ← fresh
    let c₂ ← h₂.compile (.cons v₂ env)
    return s!"(case {ce} of \{ Left {v₁} -> {c₁}; Right {v₂} -> {c₂} })"
  | .disc_intro _ _ h =>
    h.compile env.disc
  | .disc_elim _ _ _ _ h₁ h₂ => do
    let c₁ ← h₁.compile env
    let v ← fresh
    let c₂ ← h₂.compile (.cons v env)
    return s!"(let {v} = {c₁} in {c₂})"
  | .bot_intro L => return L.compileBot
  | .sup_intro _ _ L h₁ h₂ => do
    let c₁ ← h₁.compile env
    let c₂ ← h₂.compile env
    return L.compileSup c₁ c₂
  | .one_intro _ _ h => do
    let c ← h.compile env.disc
    return s!"[{c}]"
  | .for_intro _ _ _ L h₁ h₂ => do
    let c₁ ← h₁.compile env
    let acc ← fresh "_acc"
    let v ← fresh
    let c₂ ← h₂.compile (.cons v env)
    return s!"(foldl (\\{acc} {v} -> {L.compileSup acc c₂}) {L.compileBot} {c₁})"
  | .fix_intro _ L h => do
    let v ← fresh
    let c ← h.compile (.cons v env.disc)
    let nxt ← fresh "_nxt"
    let fixf ← fresh "_fix"
    return s!"(let {fixf} {v} = \
      let {nxt} = {c} in \
      if {L.compileEq v nxt} then {v} else {fixf} {nxt} \
      in {fixf} {L.compileBot})"

def compile {Γ e A} (h : Γ ⊢ e : A) (env : Env Γ) : String :=
  (h.compile env |>.run 0).1

end Datafun
