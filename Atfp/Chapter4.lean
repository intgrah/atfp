module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Category.CompleteLat
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public import Atfp.Chapter3

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finite.Sum
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.CategoryTheory.ConcreteCategory.hom]
meta def delabConcreteHom : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs ≥ 9
  withNaryArg 8 delab

section Section1

/-! Definition 4.1.1 -/

variable {X : Type u} [inst₁ : SemilatticeSup X] [inst₂ : OrderBot X]
#check SemilatticeSup
#check inst₁.toPartialOrder
#check inst₂.bot
#check inst₂.bot_le
#check sup_le_sup
#check inst₁.le_sup_left
#check inst₁.le_sup_right

variable (α : Type u)
#synth SemilatticeSup (Set α)

#synth SemilatticeSup ℕ

#synth SemilatticeSup Bool

/-! Definition 4.1.2 -/

#check SupBotHom
#check OrderHom

/-! Theorem 4.1.3 -/

theorem semilattice_wf_asc_lfp {L : Type u} [SemilatticeSup L] [OrderBot L]
    (hasc : WF_asc L)
    (f : L →o L) :
    ∃ μf : L, Function.IsFixedPt f μf ∧ ∀ x, Function.IsFixedPt f x → μf ≤ x := by
  have incr : ∀ n, f^[n] ⊥ ≤ f^[n + 1] ⊥ :=
    fun n => Monotone.iterate f.monotone n bot_le
  have nsincr : ¬∀ n, f^[n] ⊥ < f^[n + 1] ⊥ := by
    intro h
    exact hasc ⟨fun n => f^[n] ⊥, h⟩
  have ⟨n, hn⟩ : ∃ n, f^[n] ⊥ = f^[n + 1] ⊥ := by
    by_contra h
    push_neg at h
    have : ∀ n, f^[n] ⊥ < f^[n + 1] ⊥ :=
      fun n => lt_of_le_of_ne (incr n) (h n)
    exact nsincr this
  rw [Function.iterate_succ_apply'] at hn
  refine ⟨f^[n] ⊥, hn.symm, ?minimal⟩
  intro x hfix
  have hxconst : ∀ m, f^[m] x = x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      exact hfix
  have : ∀ m, f^[m] ⊥ ≤ f^[m] x :=
    fun m => Monotone.iterate f.monotone m bot_le
  simp only [hxconst] at this
  exact this n

end Section1

section Section2

section Section1

-- TODO transitive closure

end Section1

section Section2

#check ContextFreeGrammar
#check ContextFreeGrammar.NT
#check ContextFreeGrammar.rules

-- TODO string parsing

end Section2

section Section3

-- TODO Dataflow analysis

end Section3

end Section2

section Section3

variable {A B C D : PartOrd}

/-! Definition 4.3.1 -/

namespace PartOrd

def terminal : PartOrd := of PUnit

def terminal.from (X : PartOrd) : X ⟶ terminal :=
  ofHom ⟨fun _ => ⟨⟩, fun _ _ _ => le_rfl⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => ext fun _ => rfl)

def terminalCone : LimitCone (Functor.empty PartOrd) where
  cone := asEmptyCone terminal
  isLimit := isTerminal

def prod (A B : PartOrd.{u}) : PartOrd := of (A × B)

def fst : A.prod B ⟶ A :=
  ofHom ⟨Prod.fst, fun _ _ h => h.1⟩

def snd : A.prod B ⟶ B :=
  ofHom ⟨Prod.snd, fun _ _ h => h.2⟩

def prod_lift (f : C ⟶ A) (g : C ⟶ B) : C ⟶ A.prod B :=
  ofHom {
    toFun x := (f x, g x)
    monotone' _ _ h := ⟨f.hom.monotone h, g.hom.monotone h⟩
  }

def tensor_exchange :
    (A.prod B).prod (C.prod D) ≅ (A.prod C).prod (B.prod D) where
  hom := ofHom {
    toFun := fun ((a, b), (c, d)) => ((a, c), (b, d))
    monotone' := fun _ _ ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ => ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩
  }
  inv := ofHom {
    toFun := fun ((a, c), (b, d)) => ((a, b), (c, d))
    monotone' := fun _ _ ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩ => ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

def prod_isLimit :
    IsLimit (BinaryFan.mk (P := A.prod B) fst snd) :=
  BinaryFan.isLimitMk
    (fun s => prod_lift s.fst s.snd)
    (fun s => rfl)
    (fun s => rfl)
    (fun s m h₁ h₂ => by
      ext x
      apply Prod.ext
      · exact congrArg (·.hom x) h₁
      · exact congrArg (·.hom x) h₂
    )

def binaryProductCone (A B : PartOrd) : LimitCone (pair A B) where
  cone := BinaryFan.mk fst snd
  isLimit := prod_isLimit

instance : CartesianMonoidalCategory PartOrd :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone binaryProductCone

def initial : PartOrd := of PEmpty

def initial.to (X : PartOrd) : initial ⟶ X :=
  ofHom ⟨nofun, nofun⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => ext nofun)

instance : HasInitial PartOrd :=
  IsInitial.hasInitial isInitial

def coprod (A B : PartOrd.{u}) : PartOrd := of (A ⊕ B)

def inl : A ⟶ A.coprod B :=
  ofHom ⟨Sum.inl, fun _ _ => Sum.LiftRel.inl⟩

def inr : B ⟶ A.coprod B :=
  ofHom ⟨Sum.inr, fun _ _ => Sum.LiftRel.inr⟩

def coprod_desc (f : A ⟶ C) (g : B ⟶ C) : A.coprod B ⟶ C :=
  ofHom {
    toFun := Sum.elim f g
    monotone' := by
      rintro (a | b) (a' | b') (hab | hab)
      · exact f.hom.monotone hab
      · exact g.hom.monotone hab
  }

def coprod.isColimit :
    IsColimit (BinaryCofan.mk (P := A.coprod B) PartOrd.inl PartOrd.inr) :=
  BinaryCofan.isColimitMk
    (fun s => coprod_desc s.inl s.inr)
    (fun _ => rfl)
    (fun _ => rfl)
    (fun s m h₁ h₂ => by
      ext (a | b)
      · exact congrArg (·.hom a) h₁
      · exact congrArg (·.hom b) h₂
    )

def dist {A B C : PartOrd.{u}} : A.prod (B.coprod C) ≅ (A.prod B).coprod (A.prod C) where
  hom := ofHom {
    toFun
      | (a, .inl b) => .inl (a, b)
      | (a, .inr c) => .inr (a, c)
    monotone' := by
      rintro ⟨a₁, b₁ | c₁⟩ ⟨a₁, b₂ | c₂⟩ ⟨ha, hb | hc⟩
      · exact Sum.LiftRel.inl ⟨ha, hb⟩
      · exact Sum.LiftRel.inr ⟨ha, hc⟩
  }
  inv := ofHom {
    toFun
      | .inl (a, b) => (a, .inl b)
      | .inr (a, c) => (a, .inr c)
    monotone' := by
      rintro (⟨a₁, b₁⟩ | ⟨a₁, c₁⟩) (⟨a₂, b₂⟩ | ⟨a₂, c₂⟩) (⟨ha, hb⟩ | ⟨ha, hc⟩)
      · exact ⟨ha, Sum.LiftRel.inl hb⟩
      · exact ⟨ha, Sum.LiftRel.inr hc⟩
  }
  hom_inv_id := by ext ⟨a, b | c⟩ <;> rfl
  inv_hom_id := by ext (⟨a, b⟩ | ⟨a, c⟩) <;> rfl

instance (A B : PartOrd) : PartialOrder (A ⟶ B) where
  le f g := ∀ x, f x ≤ g x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ x := (h₁ x).trans (h₂ x)
  le_antisymm f g h₁ h₂ := ext fun x => le_antisymm (h₁ x) (h₂ x)

instance : CartesianMonoidalCategory PartOrd :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalCone binaryProductCone

def exp (A B : PartOrd) : PartOrd := of (A ⟶ B)

def expFunctor (A : PartOrd) : PartOrd ⥤ PartOrd where
  obj := exp A
  map f := ofHom {
    toFun g := g ≫ f
    monotone' _ _ h x := f.hom.monotone (h x)
  }

def ev : A ⊗ of (A ⟶ B) ⟶ B :=
  ofHom {
    toFun := fun (a, f) => f a
    monotone' := fun (_, f₁) (a₂, _) ⟨ha, hf⟩ =>
      (f₁.hom.monotone ha).trans (hf a₂)
  }

def ev' : of (A ⟶ B) ⊗ A ⟶ B :=
  ofHom {
    toFun := fun (f, a) => f a
    monotone' := fun (f₁, _) (_, a₂) ⟨hf, ha⟩ =>
      (f₁.hom.monotone ha).trans (hf a₂)
  }

def coev : B ⟶ of (A ⟶ A.prod B) :=
  ofHom {
    toFun b := ofHom {
      toFun a := (a, b)
      monotone' _ _ ha := ⟨ha, le_rfl⟩
    }
    monotone' _ _ hb := fun _ => ⟨le_rfl, hb⟩
  }

def tensorProductAdjunction (A : PartOrd.{u}) :
    tensorLeft A ⊣ expFunctor A :=
  Adjunction.mkOfUnitCounit {
    unit.app _ := coev
    counit.app _ := ev
  }

def curry (f : A ⊗ B ⟶ C) : B ⟶ of (A ⟶ C) :=
  ofHom {
    toFun b := ofHom {
      toFun a := f (a, b)
      monotone' := fun _ _ ha => f.hom.monotone ⟨ha, le_rfl⟩
    }
    monotone' := fun _ _ hb _ => f.hom.monotone ⟨le_rfl, hb⟩
  }

def curry_left (f : A ⊗ B ⟶ C) : A ⟶ of (B ⟶ C) :=
  ofHom {
    toFun a := ofHom {
      toFun b := f (a, b)
      monotone' := fun _ _ hb => f.hom.monotone ⟨le_rfl, hb⟩
    }
    monotone' := fun _ _ ha _ => f.hom.monotone ⟨ha, le_rfl⟩
  }

def uncurry (f : B ⟶ of (A ⟶ C)) : A ⊗ B ⟶ C :=
  ofHom {
    toFun := fun (a, b) => f b a
    monotone' := fun (_, b₁) (a₂, _) ⟨ha, hb⟩ =>
      ((f b₁).hom.monotone ha).trans (f.hom.monotone hb a₂)
  }

instance : MonoidalClosed PartOrd :=
  MonoidalClosed.mk fun A => Closed.mk _ (PartOrd.tensorProductAdjunction A)

def disc (X : PartOrd) : PartOrd where
  carrier := X
  str.le := Eq
  str.lt a b := a = b ∧ b ≠ a
  str.le_refl := Eq.refl
  str.le_trans _ _ _ := Eq.trans
  str.le_antisymm _ _ h _ := h

namespace disc

notation "[" X "]ᵈ" => disc X

def comonad : Comonad PartOrd where
  obj := disc
  map {X Y} f := @ofHom [X]ᵈ [Y]ᵈ _ _ ⟨f, fun _ _ => congrArg f⟩
  ε.app X := @ofHom [X]ᵈ X _ _ ⟨id, fun | _, _, rfl => le_rfl⟩
  δ.app X := @ofHom [X]ᵈ [[X]ᵈ]ᵈ _ _ ⟨id, fun _ _ h => h⟩

notation "[" f "]ᵈ" => disc.comonad.map f

def iso_terminal : [terminal]ᵈ ≅ terminal where
  hom := @ofHom [terminal]ᵈ terminal _ _ ⟨id, fun _ _ _ => le_rfl⟩
  inv := @ofHom terminal [terminal]ᵈ _ _ ⟨id, fun _ _ _ => rfl⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

def iso_prod (X Y : PartOrd) : [X.prod Y]ᵈ ≅ ([X]ᵈ.prod [Y]ᵈ) where
  hom := @ofHom [X.prod Y]ᵈ ([X]ᵈ.prod [Y]ᵈ) _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mp h)⟩
  inv := @ofHom ([X]ᵈ.prod [Y]ᵈ) [X.prod Y]ᵈ _ _ ⟨id, fun _ _ h => (Prod.ext_iff.mpr h)⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end disc

def powerset : PartOrd ⥤ SemilatSupCat where
  obj X := SemilatSupCat.of (Set X)
  map {X Y} f := {
    toFun s := f '' s
    map_sup' := Set.image_union f
    map_bot' := Set.image_empty f
  }
  map_id X := by
    apply SupBotHom.ext
    intro s
    change 𝟙 X '' s = s
    simp
  map_comp {X Y Z} f g := by
    apply SupBotHom.ext
    intro s
    change (f ≫ g) '' s = g '' (f '' s)
    simp [Set.image_image]

def U := forget₂ SemilatSupCat PartOrd

def U.bot (L : SemilatSupCat) : PartOrd.terminal ⟶ U.obj L :=
  PartOrd.ofHom ⟨fun _ => ⊥, fun _ _ _ => le_rfl⟩

def U.sup (L : SemilatSupCat) : (U.obj L).prod (U.obj L) ⟶ U.obj L :=
  PartOrd.ofHom ⟨fun (x, y) => x ⊔ y, fun _ _ ⟨hx, hy⟩ => sup_le_sup hx hy⟩

def one {X : PartOrd} : [X]ᵈ ⟶ U.obj (powerset.obj X) :=
  PartOrd.ofHom (X := [X]ᵈ) {
    toFun x := ({x} : Set X)
    monotone' := by intro _ _ rfl; rfl
  }

end PartOrd

end Section3

section Section4

namespace STLC

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
  | var (x : ℕ)
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

instance : One Ty := ⟨Ty.unit⟩
instance : One FinTy := ⟨FinTy.unit⟩
instance : One LatTy := ⟨LatTy.unit⟩
notation "[" A "]ᵈ" => Ty.discrete A
notation "[" T "]ᵈ" => FinTy.discrete T
prefix:100 "𝒫 " => Ty.powerset

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

instance : Coe LatTy Ty := ⟨LatTy.toTy⟩

notation "π₁" => Tm.fst
notation "π₂" => Tm.snd
notation "ι₁" => Tm.inl
notation "ι₂" => Tm.inr
instance : Singleton Tm Tm := ⟨Tm.one⟩
notation "[" e "]ᵈ" => Tm.disc e

notation "[" Γ "]ᵈ" => Ctx.disc Γ

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

open PartOrd

set_option hygiene false in
notation "〚" A "〛" => FinTy.denotation A

def FinTy.denotation : FinTy.{u} → PartOrd.{u}
  | 1 => 𝟙_ PartOrd
  | prod T₁ T₂ => 〚T₁〛 ⊗ 〚T₂〛
  | coprod T₁ T₂ => 〚T₁〛.coprod 〚T₂〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛)
  | discrete T => [〚T〛]ᵈ

set_option hygiene false in
notation "〚" A "〛" => Ty.denotation A

def Ty.denotation : Ty.{u} → PartOrd.{u}
  | 1 => PartOrd.terminal
  | prod A B => 〚A〛 ⊗ 〚B〛
  | arr A B => 〚A〛.exp 〚B〛
  | coprod A B => 〚A〛.coprod 〚B〛
  | powerset T => U.obj (PartOrd.powerset.obj 〚T〛)
  | discrete A => [〚A〛]ᵈ

lemma FinTy.toTy_denotation {T : FinTy} : 〚T〛 = 〚T.toTy〛 := by
  induction T with
  | unit => rfl
  | prod T₁ T₂ ihT₁ ihT₂ =>
    dsimp [FinTy.denotation]
    rw [ihT₁, ihT₂]
    rfl
  | coprod T₁ T₂ ihT₁ ihT₂ =>
    dsimp [FinTy.denotation]
    rw [ihT₁, ihT₂]
    rfl
  | powerset T => rfl
  | discrete T ihT =>
    dsimp [FinTy.denotation]
    rw [ihT]
    rfl

instance : HasForget₂ CompleteLat PartOrd where
  forget₂.obj L := PartOrd.of L
  forget₂.map f := PartOrd.ofHom ⟨f, f.toBoundedLatticeHom.toBoundedOrderHom.toOrderHom.monotone⟩

def LatTy.bot' : ∀ L : LatTy, 〚L〛
  | .unit => ()
  | .prod L₁ L₂ => (bot' L₁, bot' L₂)
  | .powerset T => (∅ : Set 〚T〛)

def LatTy.sup' : ∀ L : LatTy, 〚L〛 → 〚L〛 → 〚L〛
  | .unit, _, _ => ()
  | .prod L₁ L₂, (x₁, x₂), (y₁, y₂) => (sup' L₁ x₁ y₁, sup' L₂ x₂ y₂)
  | .powerset T, s₁, s₂ => show Set 〚T〛 from s₁ ∪ s₂

lemma LatTy.bot'_le (L : LatTy) (x : 〚L〛) : L.bot' ≤ x := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1, ih₂ x.2⟩
  | powerset T => exact Set.empty_subset (s := x)

lemma LatTy.le_sup'_left (L : LatTy) (x y : 〚L〛) : x ≤ L.sup' x y := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1 y.1, ih₂ x.2 y.2⟩
  | powerset T => exact Set.subset_union_left (s := x) (t := y)

lemma LatTy.le_sup'_right (L : LatTy) (x y : 〚L〛) : y ≤ L.sup' x y := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ x.1 y.1, ih₂ x.2 y.2⟩
  | powerset T => exact Set.subset_union_right (s := x) (t := y)

lemma LatTy.sup'_le (L : LatTy) {x y z : 〚L〛} (hx : x ≤ z) (hy : y ≤ z) : L.sup' x y ≤ z := by
  induction L with
  | unit => trivial
  | prod L₁ L₂ ih₁ ih₂ => exact ⟨ih₁ hx.1 hy.1, ih₂ hx.2 hy.2⟩
  | powerset T => exact Set.union_subset hx hy

instance LatTy.instSemilatticeSup' (L : LatTy) : SemilatticeSup 〚L〛 where
  sup := L.sup'
  le_sup_left := L.le_sup'_left
  le_sup_right := L.le_sup'_right
  sup_le _ _ _ := L.sup'_le

instance LatTy.instOrderBot' (L : LatTy) : OrderBot 〚L〛 where
  bot := L.bot'
  bot_le := L.bot'_le

def LatTy.bot (L : LatTy) : PartOrd.terminal ⟶ 〚L〛 :=
  ofHom ⟨fun ⟨⟩ => L.bot', fun ⟨⟩ ⟨⟩ ⟨⟩ => le_rfl⟩

def LatTy.sup : ∀ L : LatTy, 〚L〛 ⊗ 〚L〛 ⟶ 〚L〛
  | .unit => terminal.from _
  | .prod L₁ L₂ => tensor_exchange.hom ≫ (sup L₁ ⊗ₘ sup L₂)
  | .powerset T => U.sup (PartOrd.powerset.obj 〚T〛)

instance LatTy.instCompleteLattice : ∀ L : LatTy.{u}, CompleteLattice 〚L〛
  | unit => inferInstanceAs (CompleteLattice PUnit)
  | prod L₁ L₂ =>
    let := L₁.instCompleteLattice
    let := L₂.instCompleteLattice
    inferInstanceAs (CompleteLattice (〚L₁〛 × 〚L₂〛))
  | powerset T => inferInstanceAs (CompleteLattice (Set 〚T〛))

def LatTy.comprehension {A : PartOrd} {X : FinTy} :
    ∀ L : LatTy, (A ⊗ [〚X〛]ᵈ ⟶ 〚L〛) → (A ⊗ 〚𝒫 X〛 ⟶ 〚L〛)
  | .unit, _ => PartOrd.terminal.from _
  | .prod L₁ L₂, f =>
    let f₁ : A ⊗ [〚X〛]ᵈ ⟶ 〚L₁〛 := f ≫ fst
    let f₂ : A ⊗ [〚X〛]ᵈ ⟶ 〚L₂〛 := f ≫ snd
    prod_lift (L₁.comprehension f₁) (L₂.comprehension f₂)
  | .powerset T, f =>
    PartOrd.ofHom {
      toFun | (a, (s : Set 〚X〛)) => ⋃ x ∈ s, f (a, x)
      monotone' := by
        intro (a₁, (s₁ : Set 〚X〛)) (a₂, (s₂ : Set 〚X〛)) ⟨ha, hs⟩
        apply Set.iUnion₂_subset
        intro x hx₁
        have hx₂ : x ∈ s₂ := hs hx₁
        have h₁ : f (a₁, x) ≤ f (a₂, x) := f.hom.monotone ⟨ha, le_rfl⟩
        have h₂ : f (a₂, x) ≤ ⋃ y ∈ s₂, f (a₂, y) :=
          Set.subset_biUnion_of_mem (u := fun y => f (a₂, y)) hx₂
        exact h₁.trans h₂
    }

instance FinTy.instFinite : ∀ T : FinTy, Finite 〚T〛
  | unit => Finite.of_fintype PUnit
  | prod T₁ T₂ => @Finite.instProd 〚T₁〛 〚T₂〛 T₁.instFinite T₂.instFinite
  | coprod T₁ T₂ => @Finite.instSum 〚T₁〛 〚T₂〛 T₁.instFinite T₂.instFinite
  | powerset T => @Set.instFinite 〚T〛 T.instFinite
  | discrete T => T.instFinite

instance LatTy.instFinite : ∀ L : LatTy, Finite 〚L〛
  | unit => Finite.of_fintype PUnit
  | prod L₁ L₂ => @Finite.instProd 〚L₁〛 〚L₂〛 L₁.instFinite L₂.instFinite
  | powerset T => @Set.instFinite 〚T〛 T.instFinite

lemma LatTy.wf_asc (L : LatTy) : WF_asc 〚L〛 := by
  intro ⟨chain, hchain⟩
  have : StrictMono chain := strictMono_nat_of_lt_succ hchain
  exact not_strictMono_of_wellFoundedGT chain this

noncomputable def LatTy.fix {A : PartOrd} {L : LatTy}
(f : [A]ᵈ ⊗ 〚L〛 ⟶ 〚L〛) :
    [A]ᵈ ⟶ 〚L〛 :=
  @PartOrd.ofHom [A]ᵈ 〚L〛 _ _ {
    toFun a :=
      let f_a : 〚L〛 →o 〚L〛 :=
        ⟨fun x => f (a, x), fun _ _ hxy => f.hom.monotone ⟨rfl, hxy⟩⟩
      have := semilattice_wf_asc_lfp L.wf_asc f_a
      this.choose
    monotone' _ _ | rfl => le_rfl
  }

set_option hygiene false in
notation "〚" Γ "〛" => Ctx.denotation Γ

def Ctx.denotation : Ctx.{u} → PartOrd.{u}
  | [] => 𝟙_ PartOrd
  | (.none, A) :: Γ => 〚Γ〛 ⊗ 〚A〛
  | (.D, A) :: Γ => 〚Γ〛 ⊗ [〚A〛]ᵈ

def Ctx.lookup {q A} : (Γ : Ctx) → (x : ℕ) → Γ[x]? = some (q, A) → (〚Γ〛 ⟶ 〚A〛)
  | (.none, A) :: Γ, 0, rfl => snd
  | (.none, _) :: Γ, x + 1, h => fst ≫ Ctx.lookup Γ x h
  | (.D, A) :: Γ, 0, rfl => snd ≫ disc.comonad.ε.app 〚A〛
  | (.D, _) :: Γ, x + 1, h => fst ≫ Ctx.lookup Γ x h

def Ctx.drop (Γ : Ctx) : 〚Γ〛 ⟶ 〚[Γ]ᵈ〛 :=
  match Γ with
  | [] => 𝟙 〚[]〛
  | (.none, _) :: Γ => fst ≫ Ctx.drop Γ
  | (.D, A) :: Γ => Ctx.drop Γ ⊗ₘ 𝟙 [〚A〛]ᵈ

lemma Ctx.disc.idem {Γ : Ctx} : [[Γ]ᵈ]ᵈ = [Γ]ᵈ := by
  let p : Qualifier × Ty → Bool := (· matches (.D, _))
  have := @List.filter_filter _ p p Γ
  simp [Ctx.disc]

def Ctx.δ (Δ : Ctx) (h : [Δ]ᵈ = Δ := by exact Ctx.disc.idem) : 〚Δ〛 ⟶ [〚Δ〛]ᵈ :=
  match Δ with
  | [] => disc.iso_terminal.inv
  | (.D, A) :: Δ =>
    (Ctx.δ Δ (congrArg List.tail h) ⊗ₘ disc.comonad.δ.app 〚A〛) ≫ (disc.iso_prod 〚Δ〛 [〚A〛]ᵈ).inv
  | (.none, e) :: _ =>
    List.filter_eq_self.mp h (.none, e) List.mem_cons_self
      |> Bool.false_ne_true
      |>.elim

set_option hygiene false in
notation "〚" h "〛" => HasType.denotation h

open Ctx (drop δ) in
noncomputable def HasType.denotation {Γ e A} : (Γ ⊢ e : A) → (〚Γ〛 ⟶ 〚A〛)
  | var x A hx => Ctx.lookup Γ x hx
  | dvar x A hx => Ctx.lookup Γ x hx
  | unit_intro => terminal.from 〚Γ〛
  | prod_intro e₁ e₂ A₁ A₂ he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : A₁ from he₁〛
    let g := 〚show Γ ⊢ e₂ : A₂ from he₂〛
    prod_lift f 〚he₂〛
  | prod_elim₁ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ fst
  | prod_elim₂ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁.prod A₂ from he〛 ≫ snd
  | abs_intro e A B he =>
    curry_left 〚show ((.none, A) :: Γ) ⊢ e : B from he〛
  | abs_elim e₁ e₂ A B he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : A.arr B from he₁〛
    let g := 〚show Γ ⊢ e₂ : A from he₂〛
    prod_lift f g ≫ ev'
  | coprod_intro₁ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₁ from he〛 ≫ inl
  | coprod_intro₂ e A₁ A₂ he =>
    〚show Γ ⊢ e : A₂ from he〛 ≫ inr
  | coprod_elim e e₁ e₂ A₁ A₂ C he he₁ he₂ =>
    let f := 〚show Γ ⊢ e : A₁.coprod A₂ from he〛
    let g₁ := 〚show ((.none, A₁) :: Γ) ⊢ e₁ : C from he₁〛
    let g₂ := 〚show ((.none, A₂) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ dist.hom ≫ coprod_desc g₁ g₂
  | disc_intro e A he =>
    drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : A from he〛]ᵈ
  | disc_elim e₁ e₂ A C he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : [A]ᵈ from he₁〛
    let g := 〚show ((.D, A) :: Γ) ⊢ e₂ : C from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ g
  | bot_intro L => PartOrd.terminal.from 〚Γ〛 ≫ LatTy.bot L
  | one_intro e T he =>
    drop Γ ≫ δ [Γ]ᵈ ≫ [〚show [Γ]ᵈ ⊢ e : T.toTy from he〛]ᵈ ≫ (T.toTy_denotation ▸ one)
  | sup_intro e₁ e₂ L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : L from he₁〛
    let g := 〚show Γ ⊢ e₂ : L from he₂〛
    prod_lift f g ≫ LatTy.sup L
  | for_intro e₁ e₂ T L he₁ he₂ =>
    let f := 〚show Γ ⊢ e₁ : 𝒫 T from he₁〛
    let g := 〚show ((.D, T.toTy) :: Γ) ⊢ e₂ : L from he₂〛
    prod_lift (𝟙 〚Γ〛) f ≫ LatTy.comprehension L (T.toTy_denotation ▸ g)
  | fix_intro e L he =>
    let f := 〚show ((.none, L) :: [Γ]ᵈ) ⊢ e : L from he〛
    drop Γ ≫ δ [Γ]ᵈ ≫ LatTy.fix ((disc.comonad.ε.app 〚[Γ]ᵈ〛 ⊗ₘ 𝟙 〚L〛) ≫ f)

end STLC

end Section4

section Section5

-- TODO Incrementalizing fixed point algorithms

end Section5

section Section6

section Section1

/-! Definition 4.6.1 -/

structure Change where
  X : PartOrd.{u}
  Δ : PartOrd.{u}
  V : SetRel X Δ
  update : V → X
  update_monotone : ∀ xdx : V, xdx.1.1 ≤ update xdx
  zero : X → Δ
  zero_valid : ∀ x, (x, zero x) ∈ V
  zero_update: ∀ x, update ⟨(x, zero x), zero_valid x⟩ = x

notation x " ⨁[" 𝕏 "]" dx => Change.update 𝕏 ⟨(x, dx), by aesop⟩
notation "𝟬[" 𝕏 "]" => Change.zero 𝕏

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Change.update]
meta def delabChangeUpdate : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 2
  let 𝕏 ← withAppFn (withAppArg delab)
  let v ← withAppArg delab
  match v with
  | `(⟨($x, $dx), $_⟩) => `($x ⨁[$𝕏] $dx)
  | _ => failure

/-! Example 4.6.2 -/

example : Change where
  X := PartOrd.of (Fin 100)
  Δ := PartOrd.of ℕ
  V := {(n, k) : Fin 100 × ℕ | n + k < 100}
  update | ⟨(n, k), h⟩ => ⟨n + k, by rw [Set.mem_setOf_eq] at h; omega⟩
  update_monotone := by
    simp only [Subtype.forall, Prod.forall]
    intro ⟨n, hn⟩ k h
    simp
  zero x := 0
  zero_valid := Fin.isLt
  zero_update _ := rfl

/-! Example 4.6.3 -/

def Change.ofCompleteLat (L : CompleteLat) : Change where
  X := PartOrd.of L
  Δ := PartOrd.of L
  V := Set.univ
  update | ⟨(x, dx), ⟨⟩⟩ => x ⊔ dx
  update_monotone _ := le_sup_left
  zero _ := ⊥
  zero_valid := Set.mem_univ
  zero_update := sup_bot_eq

end Section1

section Section2

/-! Definition 4.6.4 -/

/--
Helper structure to define derivatives
Dependently typed, as `eq` depends on `hy`
-/
structure Deriv {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ)
    x dx
    (_ : (x, dx) ∈ 𝕏.V) : Prop where
  hy : (f x, f' (x, dx)) ∈ 𝕐.V
  eq : f (x ⨁[𝕏] dx) = f x ⨁[𝕐] f' (x, dx)

def IsDerivative {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) : Prop :=
  ∀ x dx, (hx : (x, dx) ∈ 𝕏.V) → Deriv f f' x dx hx

section

abbrev 𝒫ℕ' := Change.ofCompleteLat (CompleteLat.of (Set ℕ))
abbrev 𝒫ℕ := PartOrd.of (Set ℕ)

def f : 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun X := X ∪ {1, 2}
    monotone' {X Y} h := by
      simp only [Set.union_insert, Set.union_singleton]
      apply Set.insert_subset_insert
      apply Set.insert_subset_insert
      exact h
  }

def f'₀ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx
    monotone' _ _ | ⟨_, hdx⟩ => hdx
  }

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₀ := by
  intro (x : Set ℕ) (dx : Set ℕ) h
  refine ⟨⟨⟩, ?_⟩
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx
  tauto_set

def f'₁ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {1}
    monotone' := by
      intro (x, y) (dx, dy) ⟨hdx, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₁ := by
  intro (x : Set ℕ) (dx : Set ℕ) h
  refine ⟨⟨⟩, ?_⟩
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1}
  tauto_set

def f'₂ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {2}
    monotone' := by
      intro (x, y) (dx, dy) ⟨hdx, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₂ := by
  intro (x : Set ℕ) (dx : Set ℕ) h
  refine ⟨⟨⟩, ?_⟩
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {2}
  ext n
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff]
  tauto

def f'₃ : [𝒫ℕ]ᵈ ⊗ 𝒫ℕ ⟶ 𝒫ℕ :=
  PartOrd.ofHom {
    toFun | (_, dx) => dx \ {1, 2}
    monotone' := by
      intro (x, y) (dx, dy) ⟨_, hdy⟩
      simp only [sdiff_le_iff, sup_sdiff_self]
      trans
      · exact hdy
      · simp
  }

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₃ := by
  intro (x : Set ℕ) (dx : Set ℕ) h
  refine ⟨⟨⟩, ?_⟩
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1, 2}
  tauto_set

end

/-! Definition 4.6.5 -/

namespace SeminaiveFP

variable (L : CompleteLat.{u})
  (f : PartOrd.of L ⟶ PartOrd.of L)
  (f' : [PartOrd.of L]ᵈ ⊗ PartOrd.of L ⟶ PartOrd.of L)

mutual

def x : ℕ → PartOrd.of L
  | 0 => ⊥
  | i + 1 => x i ⊔ dx i

def dx : ℕ → PartOrd.of L
  | 0 => f ⊥
  | i + 1 => f' (x i, dx i)

end

def semifix
    (_ : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') : L :=
  ⨆ i, x L f f' i

/-! Theorem 4.6.6 -/

theorem semifix_fix
    (hasc : WF_asc L)
    (der : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') :
    semifix L f f' der = f.hom.lfp := by
  let x := x L f f'
  let dx := dx L f f'
  have : ∀ i, x (i + 1) = f (x i) := by
    intro i
    induction i with
    | zero =>
      calc x 1
        _ = x 0 ⊔ dx 0 := rfl
        _ = ⊥ ⊔ f ⊥ := rfl
        _ = f ⊥ := bot_sup_eq (f ⊥)
        _ = f (x 0) := rfl
    | succ j ih =>
      calc x (j + 2)
        _ = x (j + 1) ⊔ dx (j + 1) := rfl
        _ = f (x j) ⊔ dx (j + 1) := by rw [ih]
        _ = f (x j) ⊔ f' (x j, dx j) := rfl
        _ = f (x j ⊔ dx j) := der (x j) (dx j) ⟨⟩ |>.2.symm
        _ = f (x (j + 1)) := rfl
  have h : ∀ i, x i = f^[i] ⊥ := by
    intro i
    induction i with
    | zero => rfl
    | succ j ih =>
      rw [this, Function.iterate_succ_apply' f j ⊥, ih]
  have := fixedPoints.lfp_eq_sSup_iterate f.hom
  symm
  change f.hom.lfp = ⨆ i, x i
  simp only [h]
  change f.hom.lfp = ⨆ i, f^[i] ⊥
  apply this
  sorry

end SeminaiveFP

end Section2

namespace Change

section Section3

variable (𝕏 𝕐 : Change)

def Hom.Base : Type u :=
  {(f, f') : (𝕏.X ⟶ 𝕐.X) × ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) | IsDerivative f f'}

def Hom.Rel : Setoid (Base 𝕏 𝕐) where
  r | ⟨(f, _), _⟩, ⟨(g, _), _⟩ => f = g
  iseqv.refl _ := rfl
  iseqv.symm := Eq.symm
  iseqv.trans := Eq.trans

def Hom.Quot := Quotient (Hom.Rel 𝕏 𝕐)

@[ext]
structure Hom where
  base : 𝕏.X ⟶ 𝕐.X
  hasDeriv : ∃ f' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ, IsDerivative base f'

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective' _ _ h :=
    Hom.ext (ConcreteCategory.hom_injective (DFunLike.coe_fn_eq.mp h))

variable {𝕏 𝕐 : Change}

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) : ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) :=
  h.hasDeriv.choose

def id 𝕏 : Hom 𝕏 𝕏 where
  base := 𝟙 𝕏.X
  hasDeriv := ⟨PartOrd.ofHom ⟨fun (_, dx) => dx, fun _ _ ⟨_, h⟩ => h⟩, fun _ _ hx => ⟨hx, rfl⟩⟩

end Section3

instance : LargeCategory Change where
  Hom := Hom
  id := id
  comp {𝕏 𝕐 𝕫} f g := {
    base := f.base ≫ g.base
    hasDeriv := by
      obtain ⟨f, f', hf⟩ := f
      obtain ⟨g, g', hg⟩ := g
      refine ⟨?_, ?_⟩
      · refine PartOrd.ofHom ⟨fun (x, dx) => g' (f x, f' (x, dx)), ?_⟩
        intro (x₁, dx₁) (x₂, dx₂) ⟨h₁, h₂⟩
        change g' (f x₁, f' (x₁, dx₁)) ≤ g' (f x₂, f' (x₂, dx₂))
        refine g'.hom.monotone ⟨?_, ?_⟩
        · change f x₁ = f x₂
          exact congrArg f h₁
        · change f' (x₁, dx₁) ≤ f' (x₂, dx₂)
          exact f'.hom.monotone ⟨h₁, h₂⟩
      · intro x dx hx
        have ⟨hy, hf⟩ := hf x dx hx
        have ⟨hz, hg⟩ := hg (f x) (f' (x, dx)) hy
        refine ⟨hz, ?_⟩
        calc g (f (x ⨁[𝕏] dx))
          _ = g (f x ⨁[𝕐] f' (x, dx)) := congrArg g hf
          _ = g (f x) ⨁[𝕫] g' (f x, f' (x, dx)) := hg
  }

section Section4

/-! Definition 4.6.7 -/

def terminal : Change where
  X := PartOrd.terminal
  Δ := PartOrd.terminal
  V := Set.univ
  update _ := ⟨⟩
  update_monotone _ := le_rfl
  zero _ := ⟨⟩
  zero_valid := Set.mem_univ
  zero_update _ := rfl

def terminal.from (𝕏 : Change) : 𝕏 ⟶ terminal where
  base := PartOrd.terminal.from 𝕏.X
  hasDeriv := ⟨PartOrd.terminal.from ([𝕏.X]ᵈ ⊗ 𝕏.Δ), fun _ _ _ => ⟨⟨⟩, rfl⟩⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => rfl)

end Section4

def initial : Change where
  X := PartOrd.initial
  Δ := PartOrd.initial
  V := Set.univ
  update _ := _
  update_monotone _ := le_rfl
  zero := nofun
  zero_valid := Set.mem_univ
  zero_update _ := rfl

def initial.to (𝕏 : Change) : initial ⟶ 𝕏 where
  base := PartOrd.initial.to 𝕏.X
  hasDeriv := ⟨PartOrd.ofHom ⟨nofun, nofun⟩, nofun⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => Hom.ext <| PartOrd.ext nofun)

section Section5

/-! Definition 4.6.8 -/

def prod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X ⊗ 𝕐.X
  Δ := 𝕏.Δ ⊗ 𝕐.Δ
  V := {((x, y), (dx, dy)) | (x, dx) ∈ 𝕏.V ∧ (y, dy) ∈ 𝕐.V}
  update := fun ⟨((x, y), (dx, dy)), ⟨hx, hy⟩⟩ =>
    (x ⨁[𝕏] dx, y ⨁[𝕐] dy)
  update_monotone := fun ⟨((x, y), (dx, dy)), ⟨hx, hy⟩⟩ =>
    ⟨𝕏.update_monotone ⟨(x, dx), hx⟩, 𝕐.update_monotone ⟨(y, dy), hy⟩⟩
  zero | (x, y) => (𝟬[𝕏] x, 𝟬[𝕐] y)
  zero_valid | (x, y) => ⟨𝕏.zero_valid x, 𝕐.zero_valid y⟩
  zero_update | (x, y) => Prod.ext (𝕏.zero_update x) (𝕐.zero_update y)

end Section5

section Section6

/-! Definition 4.6.9 -/

def coprod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X.coprod 𝕐.X
  Δ := 𝕏.Δ.coprod 𝕐.Δ
  V := { (xy, dxy) |
    match xy, dxy with
    | .inl x, .inl dx => (x, dx) ∈ 𝕏.V
    | .inr y, .inr dy => (y, dy) ∈ 𝕐.V
    | _, _ => False }
  update
    | ⟨(.inl x, .inl dx), h⟩ => .inl (x ⨁[𝕏] dx)
    | ⟨(.inr y, .inr dy), h⟩ => .inr (y ⨁[𝕐] dy)
  update_monotone
    | ⟨(.inl x, .inl dx), h⟩ =>
      Sum.inl_le_inl_iff.mpr (𝕏.update_monotone ⟨(x, dx), h⟩)
    | ⟨(.inr y, .inr dy), h⟩ =>
      Sum.inr_le_inr_iff.mpr (𝕐.update_monotone ⟨(y, dy), h⟩)
  zero
    | .inl x => .inl (𝟬[𝕏] x)
    | .inr y => .inr (𝟬[𝕐] y)
  zero_valid
    | .inl x => 𝕏.zero_valid x
    | .inr y => 𝕐.zero_valid y
  zero_update
    | .inl x => congrArg Sum.inl (𝕏.zero_update x)
    | .inr y => congrArg Sum.inr (𝕐.zero_update y)

end Section6

section Section7

instance {𝕏 𝕐 : Change} : PartialOrder (𝕏 ⟶ 𝕐) :=
  PartialOrder.lift
    (fun f => f.base.hom)
    (fun _ _ h => Hom.ext (PartOrd.Hom.ext h))

noncomputable def exp (𝕏 𝕐 : Change) : Change where
  X := PartOrd.of (𝕏 ⟶ 𝕐)
  Δ := PartOrd.of ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ)
  V := { (f, df) : (𝕏 ⟶ 𝕐) × ([𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ) |
      ∃ g' : [𝕏.X]ᵈ ⊗ 𝕏.Δ ⟶ 𝕐.Δ, ∀ x dx,
        (_ : (x, dx) ∈ 𝕏.V) →
        -- TODO make this a dependent sum
        (_ : (f.base x, df (x, dx)) ∈ 𝕐.V) →
        (_ : (f.base (x ⨁[𝕏] dx), df (x ⨁[𝕏] dx, 𝟬[𝕏] (x ⨁[𝕏] dx))) ∈ 𝕐.V) →
        (_ : (f.base x, df (x, 𝟬[𝕏] x)) ∈ 𝕐.V) →
        (_ : (f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x), g' (x, dx)) ∈ 𝕐.V) →
        ((f.base x ⨁[𝕐] df (x, dx)) = f.base (x ⨁[𝕏] dx) ⨁[𝕐] df (x ⨁[𝕏] dx, 𝟬[𝕏] (x ⨁[𝕏] dx))) ∧
        ((f.base x ⨁[𝕐] df (x, dx)) = (f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x)) ⨁[𝕐] g' (x, dx))
      }
  update := sorry -- ⟨(f, df), h⟩ => fun x => f.base x ⨁[𝕐] df (x, 𝟬[𝕏] x)
  update_monotone := sorry -- | ⟨(f, df), h⟩ => sorry
  zero f := f.hasDeriv.choose
  zero_valid := by
    intro ⟨f, f', hf⟩
    simp
    sorry
  zero_update := by
    intro ⟨f, f', hf⟩
    simp
    sorry

end Section7

section Section8

def disc (𝕏 : Change) : Change where
  X := [𝕏.X]ᵈ
  Δ := 𝟙_ PartOrd
  V := Set.univ
  update | ⟨(x, ⟨⟩), ⟨⟩⟩ => x
  update_monotone _ := rfl
  zero _ := ⟨⟩
  zero_valid := Set.mem_univ
  zero_update _ := rfl

namespace disc

notation "[" 𝕏 "]ᵈ" => disc 𝕏

def comonad : Comonad Change where
  obj := disc
  map {𝕏 𝕐} f := {
    base := PartOrd.disc.comonad.map f.base
    hasDeriv :=
      ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => ⟨⟩, fun _ _ _ => le_rfl⟩, fun x dx hx => ⟨hx, rfl⟩⟩
  }
  ε.app 𝕏 := {
    base := PartOrd.disc.comonad.ε.app 𝕏.X
    hasDeriv := by
      refine ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => 𝟬[𝕏] x, ?_⟩, ?_⟩
      · rintro ⟨x₁, ⟨⟩⟩ ⟨x₂, ⟨⟩⟩ ⟨rfl, ⟨⟩⟩
        rfl
      · intro x ⟨⟩ ⟨⟩
        exact ⟨𝕏.zero_valid x, 𝕏.zero_update x |>.symm⟩
  }
  δ.app 𝕏 := {
    base := PartOrd.disc.comonad.δ.app 𝕏.X
    hasDeriv :=
      ⟨PartOrd.ofHom ⟨fun (x, ⟨⟩) => ⟨⟩, fun _ _ _ => le_rfl⟩, fun x dx hx => ⟨hx, rfl⟩⟩
  }

end disc

end Section8

section Section9

def U.obj (L : SemilatSupCat) : Change where
  X := PartOrd.of L
  Δ := PartOrd.of L
  V := Set.univ
  update | ⟨(x, dx), ⟨⟩⟩ => x ⊔ dx
  update_monotone _ := le_sup_left
  zero _ := ⊥
  zero_valid := Set.mem_univ
  zero_update := sup_bot_eq

def U.map {L M : SemilatSupCat} (f : SupBotHom L M) : U.obj L ⟶ U.obj M where
  base := PartOrd.ofHom
    ⟨f, fun a b hab => OrderHomClass.mono f hab⟩
  hasDeriv := by
    refine ⟨PartOrd.ofHom ⟨fun (l, dl) => f dl, ?_⟩, fun _ _ ⟨⟩ => ⟨⟨⟩, ?_⟩⟩
    · intro (x₁, dx₁) (x₁, dx₂) ⟨h₁, h₂⟩
      exact OrderHomClass.mono f h₂
    · change f (_ ⊔ _) = f _ ⊔ f _
      exact map_sup f _ _

def U : SemilatSupCat ⥤ Change where
  obj := U.obj
  map := U.map

def bot {L : SemilatSupCat} : terminal ⟶ U.obj L where
  base := PartOrd.ofHom ⟨fun ⟨⟩ => ⊥, fun _ _ _ => le_rfl⟩
  hasDeriv :=
    ⟨PartOrd.ofHom ⟨fun (⟨⟩, ⟨⟩) => ⊥, fun _ _ _ => le_rfl⟩,
      fun ⟨⟩ ⟨⟩ ⟨⟩ => ⟨⟨⟩, (bot_sup_eq (α := L.X) ⊥).symm⟩⟩

def sup {L : SemilatSupCat} : (U.obj L).prod (U.obj L) ⟶ U.obj L where
  base := PartOrd.ofHom {
    toFun | (l₁, l₂) => l₁ ⊔ l₂
    monotone' _ _ := fun ⟨hl, hm⟩ =>
      sup_le (le_sup_of_le_left hl) (le_sup_of_le_right hm)
  }
  hasDeriv := by
    refine ⟨PartOrd.ofHom ⟨fun (_, (dl₁, dl₂)) => dl₁ ⊔ dl₂, ?_⟩, ?_⟩
    · intro _ _ ⟨_, ⟨hm₁, hm₂⟩⟩
      exact sup_le (le_sup_of_le_left hm₁) (le_sup_of_le_right hm₂)
    · intro (l₁, l₂) (dl₁, dl₂) ⟨⟨⟩, ⟨⟩⟩
      change L at l₁ l₂ dl₁ dl₂
      exact ⟨⟨⟩, sup_sup_sup_comm l₁ dl₁ l₂ dl₂⟩

end Section9

end Change

end Section6
