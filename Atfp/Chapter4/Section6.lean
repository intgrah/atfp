module

public import Mathlib.Data.Rel
public import Mathlib.Order.Category.CompleteLat
public import Mathlib.Order.FixedPoints

import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic.TautoSet

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
  Δ : X → PartOrd.{u}
  update : ∀ x : X, Δ x → X
  update_monotone : ∀ x dx, x ≤ update x dx
  zero : ∀ x, Δ x
  zero_update: ∀ x, update x (zero x) = x

notation:65 x " ⨁[" 𝕏 "] " dx:66 => Change.update 𝕏 x dx
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
  Δ := fun ⟨n, _⟩ => PartOrd.of { k // n + k < 100 }
  update := fun ⟨n, hn⟩ ⟨k, hk⟩ => ⟨n + k, by omega⟩
  update_monotone := by
    intro ⟨n, hn⟩ ⟨k, hk⟩
    simp
  zero := fun ⟨n, hn⟩ => ⟨0, hn⟩
  zero_update _ := rfl

/-! Example 4.6.3 -/

def Change.ofCompleteLat (L : CompleteLat) : Change where
  X := PartOrd.of L
  Δ _ := PartOrd.of L
  update x dx := x ⊔ dx
  update_monotone _ _ := le_sup_left
  zero _ := ⊥
  zero_update := sup_bot_eq

end Section1

section Section2

/-! Definition 4.6.4 -/

def IsDerivative {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (f x)) : Prop :=
  ∀ x dx, f (x ⨁[𝕏] dx) = f x ⨁[𝕐] f' x dx

namespace Examples

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

def f'₀ : ∀ _ : 𝒫ℕ, 𝒫ℕ ⟶ 𝒫ℕ := fun _ => 𝟙 𝒫ℕ

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₀ := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx
  tauto_set

def f'₁ : ∀ _ : 𝒫ℕ, 𝒫ℕ ⟶ 𝒫ℕ := fun _ =>
  PartOrd.ofHom ⟨fun dx => dx \ {1}, fun _ _ h => Set.diff_subset_diff_left h⟩

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₁ := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1}
  tauto_set

def f'₂ : ∀ _ : 𝒫ℕ, 𝒫ℕ ⟶ 𝒫ℕ := fun _ =>
  PartOrd.ofHom ⟨fun dx => dx \ {2}, fun _ _ h => Set.diff_subset_diff_left h⟩

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₂ := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {2}
  ext n
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff]
  tauto

def f'₃ : ∀ _ : 𝒫ℕ, 𝒫ℕ ⟶ 𝒫ℕ := fun _ =>
  PartOrd.ofHom ⟨fun dx => dx \ {1, 2}, fun _ _ h => Set.diff_subset_diff_left h⟩

example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₃ := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1, 2}
  tauto_set

end Examples

/-! Definition 4.6.5 -/

namespace SeminaiveFP

variable (L : CompleteLat.{u})
  (f : PartOrd.of L ⟶ PartOrd.of L)
  (f' : PartOrd.of L → (PartOrd.of L ⟶ PartOrd.of L))

mutual

def x : ℕ → PartOrd.of L
  | 0 => ⊥
  | i + 1 => x i ⊔ dx i

def dx : ℕ → PartOrd.of L
  | 0 => f ⊥
  | i + 1 => f' (x i) (dx i)

end

def semifix : L :=
  ⨆ i, x L f f' i

/-! Theorem 4.6.6 -/

theorem semifix_fix
    [WellFoundedGT L]
    (der : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') :
    semifix L f f' = f.hom.lfp := by
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
        _ = f (x j) ⊔ f' (x j) (dx j) := rfl
        _ = f (x j ⊔ dx j) := (der (x j) (dx j)).symm
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
  open OmegaCompletePartialOrder in
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨f.hom.monotone, fun c => ?_⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition c
  apply le_antisymm
  · have hsup : ωSup c = c n := by
      apply le_antisymm
      · apply ωSup_le_iff.mpr
        intro m
        rcases le_or_gt n m with h | h
        · exact (hn m h).symm ▸ le_rfl
        · exact c.monotone h.le
      · exact le_ωSup c n
    rw [hsup]
    exact le_ωSup (c.map ⟨f.hom, f.hom.monotone⟩) n
  · exact ωSup_le_iff.mpr fun m => f.hom.monotone (le_ωSup c m)

end SeminaiveFP

end Section2

namespace Change

section Section3

@[ext]
structure Hom (𝕏 𝕐 : Change) where
  base : 𝕏.X ⟶ 𝕐.X
  hasDeriv : ∃ f' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (base x),
    IsDerivative base f'

variable {𝕏 𝕐 : Change}

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective' _ _ h :=
    Hom.ext (ConcreteCategory.hom_injective (DFunLike.coe_fn_eq.mp h))

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) :
    ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (h.base x) :=
  h.hasDeriv.choose

def id (𝕏 : Change) : Hom 𝕏 𝕏 where
  base := 𝟙 𝕏.X
  hasDeriv := ⟨fun _ => 𝟙 _, fun _ _ => rfl⟩

end Section3

instance : LargeCategory Change where
  Hom := Hom
  id := id
  comp {𝕏 𝕐 𝕫} f g := {
    base := f.base ≫ g.base
    hasDeriv := by
      replace ⟨f, f', hf⟩ := f
      replace ⟨g, g', hg⟩ := g
      refine ⟨fun x => (f' x) ≫ (g' (f x)), ?_⟩
      intro x dx
      calc g (f (x ⨁[𝕏] dx))
        _ = g (f x ⨁[𝕐] f' x dx) := congrArg g (hf x dx)
        _ = g (f x) ⨁[𝕫] g' (f x) (f' x dx) := hg (f x) (f' x dx)
  }

section Section4

/-! Definition 4.6.7 -/

def terminal : Change where
  X := PartOrd.terminal
  Δ := fun ⟨⟩ => PartOrd.terminal
  update := fun ⟨⟩ ⟨⟩ => ⟨⟩
  update_monotone := fun ⟨⟩ ⟨⟩ => le_refl _
  zero := fun ⟨⟩ => ⟨⟩
  zero_update := fun ⟨⟩ => rfl

def terminal.from (𝕏 : Change) : 𝕏 ⟶ terminal where
  base := PartOrd.terminal.from 𝕏.X
  hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => rfl)

end Section4

def initial : Change where
  X := PartOrd.initial
  Δ := nofun
  update := nofun
  update_monotone := nofun
  zero := nofun
  zero_update := nofun

def initial.to (𝕏 : Change) : initial ⟶ 𝕏 where
  base := PartOrd.initial.to 𝕏.X
  hasDeriv := ⟨nofun, nofun⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => Hom.ext <| PartOrd.ext nofun)

section Section5

/-! Definition 4.6.8 -/

def prod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X ⊗ 𝕐.X
  Δ := fun (x, y) => 𝕏.Δ x ⊗ 𝕐.Δ y
  update := fun (x, y) (dx, dy) =>
    (x ⨁[𝕏] dx, y ⨁[𝕐] dy)
  update_monotone := fun (x, y) (dx, dy) =>
    ⟨𝕏.update_monotone x dx, 𝕐.update_monotone y dy⟩
  zero := fun (x, y) => (𝟬[𝕏] x, 𝟬[𝕐] y)
  zero_update := fun (x, y) =>
    Prod.ext (𝕏.zero_update x) (𝕐.zero_update y)

end Section5

section Section6

variable {𝕏 𝕐 𝕫 : Change}

/-! Definition 4.6.9 -/

def coprod (𝕏 𝕐 : Change) : Change where
  X := 𝕏.X.coprod 𝕐.X
  Δ
    | .inl x => 𝕏.Δ x
    | .inr y => 𝕐.Δ y
  update
    | .inl x, dx => .inl (x ⨁[𝕏] dx)
    | .inr y, dy => .inr (y ⨁[𝕐] dy)
  update_monotone
    | .inl x, dx =>
      Sum.inl_le_inl_iff.mpr (𝕏.update_monotone x dx)
    | .inr y, dy =>
      Sum.inr_le_inr_iff.mpr (𝕐.update_monotone y dy)
  zero
    | .inl x => 𝟬[𝕏] x
    | .inr y => 𝟬[𝕐] y
  zero_update
    | .inl x => congrArg Sum.inl (𝕏.zero_update x)
    | .inr y => congrArg Sum.inr (𝕐.zero_update y)

def inl : 𝕏 ⟶ 𝕏.coprod 𝕐 where
  base := PartOrd.inl
  hasDeriv := ⟨fun _ => 𝟙 _, fun _ _ => rfl⟩

def inr : 𝕐 ⟶ 𝕏.coprod 𝕐 where
  base := PartOrd.inr
  hasDeriv := ⟨fun _ => 𝟙 _, fun _ _ => rfl⟩

def coprod_desc (f : 𝕏 ⟶ 𝕫) (g : 𝕐 ⟶ 𝕫) : 𝕏.coprod 𝕐 ⟶ 𝕫 where
  base := PartOrd.coprod_desc f.base g.base
  hasDeriv := by
    obtain ⟨f', hf'⟩ := f.hasDeriv
    obtain ⟨g', hg'⟩ := g.hasDeriv
    exact ⟨fun | .inl x => f' x | .inr y => g' y,
      fun | .inl x, dx => hf' x dx | .inr y, dy => hg' y dy⟩

end Section6

section Section7

variable {𝕏 𝕐 𝕫 𝕎 : Change}

instance : PartialOrder (𝕏 ⟶ 𝕐) :=
  PartialOrder.lift
    (fun f => f.base.hom)
    (fun _ _ h => Hom.ext (PartOrd.Hom.ext h))

def exp.update'
    (f : 𝕏.X ⟶ 𝕐.X) (df : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (f x))
    (x : 𝕏.X) : 𝕐.X :=
  f x ⨁[𝕐] df x (𝟬[𝕏] x)

theorem exp.update'_eq_of_isDerivative
    {f : 𝕏.X ⟶ 𝕐.X} {f' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (f x)}
    (hf' : IsDerivative f f') :
    update' f f' = f := by
  ext x
  calc f x ⨁[𝕐] f' x (𝟬[𝕏] x)
    _ = f (x ⨁[𝕏] 𝟬[𝕏] x) := (hf' x (𝟬[𝕏] x)).symm
    _ = f x := congrArg f (𝕏.zero_update x)

open exp in
noncomputable def exp (𝕏 𝕐 : Change) : Change where
  X := PartOrd.of (𝕏 ⟶ 𝕐)
  Δ := fun ⟨f, _⟩ => PartOrd.of
    { df : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (f x) //
      (∀ x dx, f x ⨁[𝕐] df x dx = update' f df (x ⨁[𝕏] dx)) ∧
      ∃ g : 𝕏 ⟶ 𝕐, update' f df = g.base.hom
    }
  update := by
    intro ⟨f, _⟩ ⟨df, _, hdf⟩
    refine ⟨PartOrd.ofHom ⟨update' f df, ?_⟩, ?_⟩
    all_goals
      have ⟨g, hg⟩ := hdf
      have hmono : Monotone (update' f df) :=
        hg ▸ g.base.hom.monotone
    · exact hmono
    · have : PartOrd.ofHom ⟨update' f df, hmono⟩ = g.base :=
        PartOrd.ext (congrFun hg)
      rw [this]
      exact g.hasDeriv
  update_monotone := by
    intro ⟨f, _⟩ ⟨df, _, _⟩ x
    exact 𝕐.update_monotone (f x) _
  zero := by
    intro ⟨f, hf⟩
    have hf' := hf.choose_spec
    have upd₀ := update'_eq_of_isDerivative hf'
    refine ⟨hf.choose, ?_, ⟨f, hf⟩, upd₀⟩
    intro x dx
    rw [upd₀]
    exact (hf' x dx).symm
  zero_update := by
    intro ⟨f, hf⟩
    apply Hom.ext
    ext x
    change update' f hf.choose x = f x
    exact congrFun (update'_eq_of_isDerivative hf.choose_spec) x

def terminalCone : LimitCone (Functor.empty Change) where
  cone := asEmptyCone terminal
  isLimit := isTerminal

def fst : 𝕏.prod 𝕐 ⟶ 𝕏 where
  base := PartOrd.fst
  hasDeriv := ⟨fun _ => PartOrd.fst, fun _ _ => rfl⟩

def snd : 𝕏.prod 𝕐 ⟶ 𝕐 where
  base := PartOrd.snd
  hasDeriv := ⟨fun _ => PartOrd.snd, fun _ _ => rfl⟩

def prod_lift (f : 𝕫 ⟶ 𝕏) (g : 𝕫 ⟶ 𝕐) : 𝕫 ⟶ 𝕏.prod 𝕐 where
  base := PartOrd.prod_lift f.base g.base
  hasDeriv := by
    replace ⟨f', hf'⟩ := f.hasDeriv
    replace ⟨g', hg'⟩ := g.hasDeriv
    refine ⟨fun x => PartOrd.prod_lift (f' x) (g' x), ?_⟩
    intro x dx
    exact Prod.ext (hf' x dx) (hg' x dx)

def prod_isLimit : IsLimit (BinaryFan.mk (P := 𝕏.prod 𝕐) fst snd) :=
  BinaryFan.isLimitMk
    (fun s => prod_lift s.fst s.snd)
    (fun _ => rfl)
    (fun _ => rfl)
    (by
      intro _ _ h₁ h₂
      apply Hom.ext
      ext x
      exact Prod.ext (congrArg (·.base.hom x) h₁)
        (congrArg (·.base.hom x) h₂))

def binaryProductCone (𝕏 𝕐 : Change) : LimitCone (pair 𝕏 𝕐) where
  cone := BinaryFan.mk fst snd
  isLimit := prod_isLimit

instance : CartesianMonoidalCategory Change :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    terminalCone binaryProductCone

open exp in
noncomputable def expFunctor (𝕏 : Change) : Change ⥤ Change where
  obj := exp 𝕏
  map {𝕐 𝕫} f := {
    base := PartOrd.ofHom {
      toFun g := g ≫ f
      monotone' _ _ h x := f.base.hom.monotone (h x)
    }
    hasDeriv := by
      obtain ⟨f', hf'⟩ := f.hasDeriv
      refine ⟨?_, ?_⟩
      · intro ⟨g, _⟩
        refine PartOrd.ofHom ⟨fun ⟨df, hdf⟩ => ⟨fun x => df x ≫ f' (g x), ?_, ?_⟩, ?_⟩
        · intro x dx
          calc f.base (g x) ⨁[𝕫] f' (g x) (df x dx)
            _ = f.base (g x ⨁[𝕐] df x dx) :=
                (hf' (g x) (df x dx)).symm
            _ = f.base (g (x ⨁[𝕏] dx) ⨁[𝕐]
                  df (x ⨁[𝕏] dx) (𝟬[𝕏] (x ⨁[𝕏] dx))) :=
                congrArg f.base (hdf.left x dx)
            _ = f.base (g (x ⨁[𝕏] dx)) ⨁[𝕫]
                f' (g (x ⨁[𝕏] dx)) (df (x ⨁[𝕏] dx) (𝟬[𝕏] (x ⨁[𝕏] dx))) := by
                rw [hf']
        · obtain ⟨g_hom, hg_eq⟩ := hdf.right
          refine ⟨g_hom ≫ f, ?_⟩
          ext z
          calc update' (g ≫ f.base) (fun x => df x ≫ f' (g x)) z
            _ = f.base (update' g df z) := hf' (g z) (df z (𝟬[𝕏] z)) |>.symm
            _ = f.base (g_hom.base z) := by rw [hg_eq]
        · intro ⟨df₁, _⟩ ⟨df₂, _⟩ h x dx
          change (df₁ x ≫ f' (g x)) dx ≤ (df₂ x ≫ f' (g x)) dx
          exact (f' (g x)).hom.monotone (h x dx)
      · intro ⟨g, _⟩ ⟨df, _, _⟩
        apply Hom.ext
        ext x
        exact hf' (g x) (df x (𝟬[𝕏] x))
  }

def ev : 𝕏 ⊗ 𝕏.exp 𝕐 ⟶ 𝕐 where
  base := PartOrd.ofHom {
    toFun := fun (x, f) => f.base x
    monotone' := fun (_, f₁) (x₂, _) ⟨hx, hf⟩ =>
      (f₁.base.hom.monotone hx).trans (hf x₂)
  }
  hasDeriv := by
    refine ⟨?_, ?_⟩
    · intro (x, ⟨f, _⟩)
      refine PartOrd.ofHom ⟨fun ⟨dx, ⟨df, _, _⟩⟩ => df x dx, ?_⟩
      intro ⟨dx₁, ⟨df₁, _, _⟩⟩ ⟨dx₂, ⟨df₂, _, _⟩⟩ ⟨hdx, hdf⟩
      calc (df₁ x) dx₁
        _ ≤ (df₁ x) dx₂ := (df₁ x).hom.monotone hdx
        _ ≤ (df₂ x) dx₂ := hdf x dx₂
    intro (x, ⟨f, _⟩) ⟨dx, ⟨df, hev, _⟩⟩
    change exp.update' f df (x ⨁[𝕏] dx) = f x ⨁[𝕐] df x dx
    exact (hev x dx)|>.symm

def coev : 𝕐 ⟶ 𝕏.exp (𝕏 ⊗ 𝕐) where
  base := PartOrd.ofHom {
    toFun y := {
      base := PartOrd.ofHom ⟨fun x => (x, y), fun _ _ hx => ⟨hx, le_rfl⟩⟩
      hasDeriv := by
        refine ⟨fun x => PartOrd.ofHom ⟨fun dx => (dx, 𝟬[𝕐] y), ?_⟩, ?_⟩
        · exact fun _ _ h => ⟨h, le_rfl⟩
        · exact fun _ _ => Prod.ext rfl (𝕐.zero_update y).symm
    }
    monotone' _ _ hy x := ⟨le_rfl, hy⟩
  }
  hasDeriv := by
    refine ⟨fun y => PartOrd.ofHom ⟨fun dy => ?_, ?_⟩, ?_⟩
    · set f : 𝕏.X ⟶ (𝕏 ⊗ 𝕐).X :=
        PartOrd.ofHom ⟨fun x => (x, y), fun _ _ hx => ⟨hx, le_rfl⟩⟩
      let df : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ (𝕏 ⊗ 𝕐).Δ (f x) :=
        fun x => PartOrd.ofHom ⟨fun dx => (dx, dy), fun _ _ h => ⟨h, le_rfl⟩⟩
      refine ⟨df, fun x dx => ?_, ⟨?_, ⟨fun x => ?_, ?_⟩⟩, ?_⟩
      · change (x ⨁[𝕏] dx, y ⨁[𝕐] dy) = (x ⨁[𝕏] dx ⨁[𝕏] 𝟬[𝕏] (x ⨁[𝕏] dx), y ⨁[𝕐] dy)
        rw [𝕏.zero_update]
      · exact PartOrd.ofHom ⟨fun x => (x, y ⨁[𝕐] dy), fun _ _ h => ⟨h, le_rfl⟩⟩
      · exact PartOrd.ofHom ⟨fun dx => (dx, 𝟬[𝕐] (y ⨁[𝕐] dy)), fun _ _ h => ⟨h, le_rfl⟩⟩
      · exact fun _ _ => Prod.ext rfl (𝕐.zero_update (y ⨁[𝕐] dy)).symm
      · ext x
        change (x ⨁[𝕏] 𝟬[𝕏] x, y ⨁[𝕐] dy) = (x, y ⨁[𝕐] dy)
        rw [𝕏.zero_update]
    · intro _ _ h _ _
      exact ⟨le_rfl, h⟩
    · intro y dy
      apply Hom.ext
      ext x
      exact Prod.ext (𝕏.zero_update x).symm rfl

noncomputable def tensorProductAdjunction (𝕏 : Change) :
    tensorLeft 𝕏 ⊣ expFunctor 𝕏 :=
  Adjunction.mkOfUnitCounit {
    unit.app _ := coev
    counit.app _ := ev
  }

noncomputable def curry_left (f : 𝕏 ⊗ 𝕐 ⟶ 𝕫) : 𝕏 ⟶ 𝕐.exp 𝕫 :=
  coev ≫ (expFunctor 𝕐).map (prod_lift snd fst ≫ f)

noncomputable instance : MonoidalClosed Change :=
  MonoidalClosed.mk fun 𝕏 => Closed.mk _ (tensorProductAdjunction 𝕏)

def tensorExchange : (𝕏 ⊗ 𝕐) ⊗ (𝕫 ⊗ 𝕎) ≅ (𝕏 ⊗ 𝕫) ⊗ (𝕐 ⊗ 𝕎) where
  hom := prod_lift (prod_lift (fst ≫ fst) (snd ≫ fst)) (prod_lift (fst ≫ snd) (snd ≫ snd))
  inv := prod_lift (prod_lift (fst ≫ fst) (snd ≫ fst)) (prod_lift (fst ≫ snd) (snd ≫ snd))

def dist : 𝕏 ⊗ (𝕐.coprod 𝕫) ≅ (𝕏 ⊗ 𝕐).coprod (𝕏 ⊗ 𝕫) where
  hom := {
    base := PartOrd.dist.hom
    hasDeriv := ⟨fun | (_, .inl _) => 𝟙 _ | (_, .inr _) => 𝟙 _,
      fun | (_, .inl _), _ => rfl | (_, .inr _), _ => rfl⟩
  }
  inv := {
    base := PartOrd.dist.inv
    hasDeriv := ⟨fun | .inl _ => 𝟙 _ | .inr _ => 𝟙 _,
      fun | .inl _, _ => rfl | .inr _, _ => rfl⟩
  }
  hom_inv_id := Hom.ext <| PartOrd.ext fun | (_, .inl _) => rfl | (_, .inr _) => rfl
  inv_hom_id := Hom.ext <| PartOrd.ext fun | .inl _ => rfl | .inr _ => rfl

end Section7

section Section8

def disc (𝕏 : Change) : Change where
  X := [𝕏.X]ᵈ
  Δ _ := 𝟙_ PartOrd
  update x _ := x
  update_monotone _ _ := le_refl _
  zero _ := ⟨⟩
  zero_update _ := rfl

namespace disc

notation "[" 𝕏 "]ᵈ" => disc 𝕏

def comonad : Comonad Change where
  obj := disc
  map f := {
    base := PartOrd.disc.comonad.map f.base
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }
  ε.app 𝕏 := {
    base := PartOrd.disc.comonad.ε.app 𝕏.X
    hasDeriv := ⟨fun x => PartOrd.ofHom ⟨fun _ => 𝟬[𝕏] x, fun _ _ _ => le_rfl⟩,
      fun x _ => (𝕏.zero_update x).symm⟩
  }
  δ.app 𝕏 := {
    base := PartOrd.disc.comonad.δ.app 𝕏.X
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }

notation "[" f "]ᵈ" => disc.comonad.map f

def iso_terminal : [𝟙_ Change]ᵈ ≅ 𝟙_ Change where
  hom := {
    base := PartOrd.disc.iso_terminal.hom
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }
  inv := {
    base := PartOrd.disc.iso_terminal.inv
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }

def iso_prod (𝕏 𝕐 : Change) : [𝕏 ⊗ 𝕐]ᵈ ≅ [𝕏]ᵈ ⊗ [𝕐]ᵈ where
  hom := {
    base := PartOrd.disc.iso_prod 𝕏.X 𝕐.X |>.hom
    hasDeriv := ⟨fun _ => PartOrd.ofHom ⟨fun ⟨⟩ => (⟨⟩, ⟨⟩), fun _ _ _ => le_rfl⟩,
      fun _ _ => rfl⟩
  }
  inv := {
    base := PartOrd.disc.iso_prod 𝕏.X 𝕐.X |>.inv
    hasDeriv := ⟨fun _ => PartOrd.ofHom ⟨fun ⟨⟨⟩, ⟨⟩⟩ => ⟨⟩, fun _ _ _ => le_rfl⟩,
      fun _ _ => rfl⟩
  }

end disc

end Section8

section Section9

def powerset : Change ⥤ SemilatSupCat where
  obj 𝕏 := SemilatSupCat.of (Set 𝕏.X)
  map {𝕏 𝕐} f := {
    toFun s := f.base '' s
    map_sup' := Set.image_union f.base
    map_bot' := Set.image_empty f.base
  }
  map_id 𝕏 := by
    apply SupBotHom.ext
    intro s
    change 𝟙 𝕏.X '' s = s
    simp
  map_comp {𝕏 𝕐 𝕫} f g := by
    apply SupBotHom.ext
    intro s
    change (f.base ≫ g.base) '' s = g.base '' (f.base '' s)
    simp [Set.image_image]

def U.obj (L : SemilatSupCat) : Change where
  X := PartOrd.of L
  Δ _ := PartOrd.of L
  update x dx := x ⊔ dx
  update_monotone _ _ := le_sup_left
  zero _ := ⊥
  zero_update := sup_bot_eq

def U.map {L M : SemilatSupCat} (f : SupBotHom L M) : U.obj L ⟶ U.obj M where
  base := PartOrd.ofHom
    ⟨f, fun a b hab => OrderHomClass.mono f hab⟩
  hasDeriv := by
    refine ⟨fun _ => PartOrd.ofHom ⟨fun (dx : L) => (f dx : M),
      fun _ _ h => OrderHomClass.mono f h⟩, ?_⟩
    intro (x : L) (dx : L)
    change (f (x ⊔ dx) : M) = f x ⊔ f dx
    exact map_sup f x dx

def U : SemilatSupCat ⥤ Change where
  obj := U.obj
  map := U.map

def bot {L : SemilatSupCat} : 𝟙_ Change ⟶ U.obj L where
  base := PartOrd.ofHom ⟨fun ⟨⟩ => (⊥ : L), fun _ _ _ => le_rfl⟩
  hasDeriv :=
    ⟨fun ⟨⟩ => PartOrd.ofHom ⟨fun ⟨⟩ => (⊥ : L), fun _ _ _ => le_rfl⟩,
      fun ⟨⟩ ⟨⟩ => (bot_sup_eq (⊥ : L)).symm⟩

def sup {L : SemilatSupCat} : U.obj L ⊗ U.obj L ⟶ U.obj L where
  base := PartOrd.ofHom {
    toFun := fun (l₁, l₂) => l₁ ⊔ l₂
    monotone' _ _ := fun ⟨hl, hm⟩ =>
      sup_le (le_sup_of_le_left hl) (le_sup_of_le_right hm)
  }
  hasDeriv := by
    refine ⟨fun _ => PartOrd.ofHom ⟨fun (dl₁, dl₂) => (dl₁ ⊔ dl₂ : L),
      fun _ _ ⟨h₁, h₂⟩ => sup_le_sup h₁ h₂⟩, ?_⟩
    intro (l₁, l₂) (dl₁, dl₂)
    change L at l₁ l₂ dl₁ dl₂
    exact sup_sup_sup_comm l₁ dl₁ l₂ dl₂

def one {𝕏 : Change} : disc 𝕏 ⟶ U.obj (powerset.obj 𝕏) where
  base := PartOrd.one
  hasDeriv := ⟨fun _ => PartOrd.ofHom ⟨fun _ => (∅ : Set 𝕏.X), fun _ _ _ => le_rfl⟩,
    fun x ⟨⟩ => (Set.union_empty {x}).symm⟩

end Section9

end Change
