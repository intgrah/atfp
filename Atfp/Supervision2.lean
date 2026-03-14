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

def box : Ctx → Ctx
  | [] => []
  | (_, A) :: Γ => (.D, A) :: box Γ

def d : Ctx → Ctx
  | [] => []
  | (.none, A) :: Γ => (.D, A.Δ) :: d Γ
  | (.D, _) :: Γ => d Γ

universe u

inductive HasType' : Ctx → Tm → Ty → Type u
  | var {Γ} x A :
    (Γ[x]? = some (.none, A)) →
    HasType' Γ (.var x) A
  | dvar {Γ} x A :
    (Γ[x]? = some (.D, A)) →
    HasType' Γ (.var x) A
  | unit_intro {Γ} :
    HasType' Γ .unit 1
  | prod_intro {Γ} e₁ e₂ A₁ A₂ :
    HasType' Γ e₁ A₁ →
    HasType' Γ e₂ A₂ →
    HasType' Γ (e₁.prod e₂) (A₁.prod A₂)
  | prod_elim₁ {Γ} e A₁ A₂ :
    HasType' Γ e (A₁.prod A₂) →
    HasType' Γ (π₁ e) A₁
  | prod_elim₂ {Γ} e (A₁ A₂ : Ty) :
    HasType' Γ e (A₁.prod A₂) →
    HasType' Γ (π₂ e) A₂
  | coprod_intro₁ {Γ} e A₁ A₂ :
    HasType' Γ e A₁ →
    HasType' Γ (ι₁ e) (.coprod A₁ A₂)
  | coprod_intro₂ {Γ} e A₁ A₂ :
    HasType' Γ e A₂ →
    HasType' Γ (ι₂ e) (.coprod A₁ A₂)
  | coprod_elim {Γ} e e₁ e₂ A₁ A₂ C :
    HasType' Γ e (.coprod A₁ A₂) →
    HasType' ((.none, A₁) :: Γ) e₁ C →
    HasType' ((.none, A₂) :: Γ) e₂ C →
    HasType' Γ (.case e e₁ e₂) C
  | disc_intro {Γ} e A :
    HasType' [Γ]ᵈ e A →
    HasType' Γ [e]ᵈ [A]ᵈ
  | disc_elim {Γ} e₁ e₂ A C :
    HasType' Γ e₁ [A]ᵈ →
    HasType' ((.D, A) :: Γ) e₂ C →
    HasType' Γ (.let e₁ e₂) C
  | bot_intro {Γ} L :
    HasType' Γ (.bot L) L
  | one_intro {Γ} e (T : FinTy) :
    HasType' [Γ]ᵈ e T.toTy →
    HasType' Γ {e} (𝒫 T)
  | sup_intro {Γ} e₁ e₂ (L : LatTy) :
    HasType' Γ e₁ L →
    HasType' Γ e₂ L →
    HasType' Γ (.sup L e₁ e₂) L
  | for_intro {Γ} e₁ e₂ (T : FinTy) (L : LatTy) :
    HasType' Γ e₁ (𝒫 T) →
    HasType' ((.D, T.toTy) :: Γ) e₂ L →
    HasType' Γ (.for e₁ e₂) L

def dlen : Ctx → Nat
  | [] => 0
  | (.none, _) :: Γ => 1 + dlen Γ
  | (.D, _) :: Γ => dlen Γ

def boxIdx (Γ : Ctx) (x : Nat) : Nat := dlen Γ + x

def dIdx : Ctx → Nat → Nat
  | (.none, _) :: _, 0 => 0
  | (.none, _) :: Γ, x + 1 => 1 + dIdx Γ x
  | (.D, _) :: Γ, x + 1 => dIdx Γ x
  | _, _ => 0

mutual

def delta (Γ : Ctx) (e : Tm) (A : Ty) : HasType' Γ e A → Tm
  | .var x _ _ => .var (dIdx Γ x)
  | .dvar _ _ _ => .unit
  | .unit_intro => .unit
  | .prod_intro e₁ e₂ A₁ A₂ h₁ h₂ =>
    .prod (delta Γ e₁ A₁ h₁) (delta Γ e₂ A₂ h₂)
  | .prod_elim₁ e A₁ A₂ h =>
    .fst (delta Γ e (.prod A₁ A₂) h)
  | .prod_elim₂ e A₁ A₂ h =>
    .snd (delta Γ e (.prod A₁ A₂) h)
  | .coprod_intro₁ e A₁ A₂ h =>
    .inl (delta Γ e A₁ h)
  | .coprod_intro₂ e A₁ A₂ h =>
    .inr (delta Γ e A₂ h)
  | .coprod_elim e e₁ e₂ A₁ A₂ C he h₁ h₂ =>
    .case (phi Γ e (.coprod A₁ A₂) he)
      (delta ((.none, A₁) :: Γ) e₁ C h₁)
      (delta ((.none, A₂) :: Γ) e₂ C h₂)
  | .disc_intro _ _ _ => .unit
  | .disc_elim _ e₂ A C _ h₂ =>
    delta ((.D, A) :: Γ) e₂ C h₂
  | .bot_intro L => .bot L
  | .sup_intro e₁ e₂ L h₁ h₂ =>
    .sup L (delta Γ e₁ L h₁) (delta Γ e₂ L h₂)
  | .one_intro _ T _ => .bot (.powerset T)
  | .for_intro e₁ e₂ T L h₁ h₂ =>
    .for (phi Γ e₁ (.powerset T) h₁) (delta ((.D, T.toTy) :: Γ) e₂ L h₂)

def phi (Γ : Ctx) (e : Tm) (A : Ty) : HasType' Γ e A → Tm
  | .var x _ _ => .var (boxIdx Γ x)
  | .dvar x _ _ => .var (boxIdx Γ x)
  | .unit_intro => .unit
  | .prod_intro e₁ e₂ A₁ A₂ h₁ h₂ =>
    .prod (phi Γ e₁ A₁ h₁) (phi Γ e₂ A₂ h₂)
  | .prod_elim₁ e A₁ A₂ h =>
    .fst (phi Γ e (.prod A₁ A₂) h)
  | .prod_elim₂ e A₁ A₂ h =>
    .snd (phi Γ e (.prod A₁ A₂) h)
  | .coprod_intro₁ e A₁ A₂ h =>
    .inl (phi Γ e A₁ h)
  | .coprod_intro₂ e A₁ A₂ h =>
    .inr (phi Γ e A₂ h)
  | .coprod_elim e e₁ e₂ A₁ A₂ C he h₁ h₂ =>
    .case (phi Γ e (.coprod A₁ A₂) he)
      (phi ((.none, A₁) :: Γ) e₁ C h₁)
      (phi ((.none, A₂) :: Γ) e₂ C h₂)
  | .disc_intro e A h =>
    .disc (phi (Ctx.disc Γ) e A h)
  | .disc_elim e₁ e₂ A C h₁ h₂ =>
    .let (phi Γ e₁ (.discrete A) h₁) (phi ((.D, A) :: Γ) e₂ C h₂)
  | .bot_intro L => .bot L
  | .sup_intro e₁ e₂ L h₁ h₂ =>
    .sup L (phi Γ e₁ L h₁) (phi Γ e₂ L h₂)
  | .one_intro e T h =>
    .one (phi (Ctx.disc Γ) e T.toTy h)
  | .for_intro e₁ e₂ T L h₁ h₂ =>
    .for (phi Γ e₁ (.powerset T) h₁) (phi ((.D, T.toTy) :: Γ) e₂ L h₂)

end

/-!

abs_intro

Γ, x : A ⊢ e : B
─────────────────────
Γ ⊢ λx. e : A → B


delta should produce

(A → B).Δ = (A ×^D A.Δ) → B.Δ

so

delta(λx. e) = λ(x', dx). delta(e)

lambda binds x' and dx at top of context, rather than interleaving in the manner required for box Γ ++ d Γ.

delta(e₁ e₂) = delta(e₁) (disc(phi(e₂)), delta(e₂))

similar issue.

derivative should produce a pair
require a stronger monotonicity condition? derivatives monotone?


-/

end Datafun
