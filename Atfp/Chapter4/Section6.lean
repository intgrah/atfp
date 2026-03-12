module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Data.Rel
public import Mathlib.Order.Category.CompleteLat
public import Mathlib.Order.FixedPoints

import Mathlib.Tactic.TautoSet

public import Atfp.Chapter3
public import Atfp.Chapter4.Section3

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
