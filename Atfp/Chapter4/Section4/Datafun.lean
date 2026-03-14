module

@[expose] public section

namespace Datafun

universe u

inductive FinTy : Type u
  | unit
  | prod (T₁ T₂ : FinTy)
  | coprod (T₁ T₂ : FinTy)
  | powerset (T : FinTy)
  | discrete (T : FinTy)

inductive Ty : Type u
  | unit
  | prod (A B : Ty)
  | arr (A B : Ty)
  | coprod (A B : Ty)
  | powerset (T : FinTy)
  | discrete (A : Ty)

inductive LatTy : Type u
  | unit
  | prod (L₁ L₂ : LatTy)
  | powerset (T : FinTy)

inductive Tm : Type u
  | var (x : Nat)
  | abs (A : Ty) (e : Tm)
  | app (e₁ e₂ : Tm)
  | unit
  | prod (e₁ e₂ : Tm)
  | fst (e : Tm)
  | snd (e : Tm)
  | inl (e : Tm)
  | inr (e : Tm)
  | case (e e₁ e₂ : Tm)
  | bot (L : LatTy)
  | sup (L : LatTy) (e₁ e₂ : Tm)
  | for (e₁ e₂ : Tm)
  | one (e : Tm)
  | disc (e : Tm)
  | let (e₁ e₂ : Tm)
  | fix (L : LatTy) (e : Tm)

inductive Qualifier
  | D
  | none

abbrev Ctx := List (Qualifier × Ty)

def Ctx.disc : Ctx → Ctx :=
  List.filter (· matches (.D, _))

scoped instance : One Ty := ⟨Ty.unit⟩
scoped instance : One FinTy := ⟨FinTy.unit⟩
scoped instance : One LatTy := ⟨LatTy.unit⟩
scoped notation "[" A "]ᵈ" => Ty.discrete A
scoped notation "[" T "]ᵈ" => FinTy.discrete T
scoped prefix:100 "𝒫 " => Ty.powerset

def FinTy.toTy : FinTy → Ty
  | .unit => .unit
  | .prod T₁ T₂ => .prod T₁.toTy T₂.toTy
  | .coprod T₁ T₂ => .coprod T₁.toTy T₂.toTy
  | .powerset T => .powerset T
  | .discrete T => .discrete T.toTy

def LatTy.toTy : LatTy → Ty
  | .unit => .unit
  | .prod L₁ L₂ => .prod L₁.toTy L₂.toTy
  | .powerset T => .powerset T

def FinTy.card : FinTy → Nat
  | 1 => 1
  | prod T₁ T₂ => T₁.card * T₂.card
  | coprod T₁ T₂ => T₁.card + T₂.card
  | powerset T => 2 ^ T.card
  | discrete T => T.card

def LatTy.card : LatTy → Nat
  | .unit => 1
  | .prod L₁ L₂ => L₁.card * L₂.card
  | .powerset T => 2 ^ T.card

scoped instance : Coe LatTy Ty := ⟨LatTy.toTy⟩

scoped notation "π₁" => Tm.fst
scoped notation "π₂" => Tm.snd
scoped notation "ι₁" => Tm.inl
scoped notation "ι₂" => Tm.inr
scoped instance : Singleton Tm Tm := ⟨Tm.one⟩
scoped notation "[" e "]ᵈ" => Tm.disc e
scoped notation "[" Γ "]ᵈ" => Ctx.disc Γ

set_option hygiene false in
scoped notation:max Γ " ⊢ " e " : " A => HasType Γ e A

inductive HasType : Ctx → Tm → Ty → Type u
  | var {Γ} x A :
    (Γ[x]? = some (.none, A)) →
    (Γ ⊢ .var x : A)
  | dvar {Γ} x A :
    (Γ[x]? = some (.D, A)) →
    (Γ ⊢ .var x : A)
  | unit_intro {Γ} :
    (Γ ⊢ .unit : 1)
  | prod_intro {Γ} e₁ e₂ A₁ A₂ :
    (Γ ⊢ e₁ : A₁) →
    (Γ ⊢ e₂ : A₂) →
    (Γ ⊢ e₁.prod e₂ : A₁.prod A₂)
  | prod_elim₁ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₁.prod A₂) →
    (Γ ⊢ π₁ e : A₁)
  | prod_elim₂ {Γ} e (A₁ A₂ : Ty) :
    (Γ ⊢ e : A₁.prod A₂) →
    (Γ ⊢ π₂ e : A₂)
  | abs_intro {Γ} e A B :
    (((.none, A) :: Γ) ⊢ e : B) →
    (Γ ⊢ .abs A e : .arr A B)
  | abs_elim {Γ} e₁ e₂ A B :
    (Γ ⊢ e₁ : .arr A B) →
    (Γ ⊢ e₂ : A) →
    (Γ ⊢ e₁.app e₂ : B)
  | coprod_intro₁ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₁) →
    (Γ ⊢ ι₁ e : .coprod A₁ A₂)
  | coprod_intro₂ {Γ} e A₁ A₂ :
    (Γ ⊢ e : A₂) →
    (Γ ⊢ ι₂ e : .coprod A₁ A₂)
  | coprod_elim {Γ} e e₁ e₂ A₁ A₂ C :
    (Γ ⊢ e : .coprod A₁ A₂) →
    (((.none, A₁) :: Γ) ⊢ e₁ : C) →
    (((.none, A₂) :: Γ) ⊢ e₂ : C) →
    (Γ ⊢ .case e e₁ e₂ : C)
  | disc_intro {Γ} e A :
    ([Γ]ᵈ ⊢ e : A) →
    (Γ ⊢ [e]ᵈ : [A]ᵈ)
  | disc_elim {Γ} e₁ e₂ A C :
    (Γ ⊢ e₁ : [A]ᵈ) →
    (((.D, A) :: Γ) ⊢ e₂ : C) →
    (Γ ⊢ .let e₁ e₂ : C)
  | bot_intro {Γ} L :
    (Γ ⊢ .bot L : L)
  | one_intro {Γ} e (T : FinTy) :
    ([Γ]ᵈ ⊢ e : T.toTy) →
    (Γ ⊢ {e} : 𝒫 T)
  | sup_intro {Γ} e₁ e₂ (L : LatTy) :
    (Γ ⊢ e₁ : L) →
    (Γ ⊢ e₂ : L) →
    (Γ ⊢ .sup L e₁ e₂ : L)
  | for_intro {Γ} e₁ e₂ (T : FinTy) (L : LatTy) :
    (Γ ⊢ e₁ : 𝒫 T) →
    (((.D, T.toTy) :: Γ) ⊢ e₂ : L) →
    (Γ ⊢ .for e₁ e₂ : L)
  | fix_intro {Γ} e (L : LatTy) :
    (((.none, L) :: [Γ]ᵈ) ⊢ e : L) →
    (Γ ⊢ .fix L e : L)

end Datafun
