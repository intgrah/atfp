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

variable (𝕏 𝕐 : Change)

@[ext]
structure Hom where
  base : 𝕏.X ⟶ 𝕐.X
  hasDeriv : ∃ f' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (base x),
    IsDerivative base f'

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective' _ _ h :=
    Hom.ext (ConcreteCategory.hom_injective (DFunLike.coe_fn_eq.mp h))

variable {𝕏 𝕐 : Change}

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) :
    ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (h.base x) :=
  h.hasDeriv.choose

def id 𝕏 : Hom 𝕏 𝕏 where
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

noncomputable def inl : 𝕏 ⟶ 𝕏.coprod 𝕐 where
  base := PartOrd.inl
  hasDeriv := ⟨fun _ => 𝟙 _, fun _ _ => rfl⟩

noncomputable def inr : 𝕐 ⟶ 𝕏.coprod 𝕐 where
  base := PartOrd.inr
  hasDeriv := ⟨fun _ => 𝟙 _, fun _ _ => rfl⟩

noncomputable def coprod_desc (f : 𝕏 ⟶ 𝕫) (g : 𝕐 ⟶ 𝕫) : 𝕏.coprod 𝕐 ⟶ 𝕫 where
  base := PartOrd.coprod_desc f.base g.base
  hasDeriv := by
    obtain ⟨f', hf'⟩ := f.hasDeriv
    obtain ⟨g', hg'⟩ := g.hasDeriv
    exact ⟨fun | .inl x => f' x | .inr y => g' y,
      fun | .inl x, dx => hf' x dx | .inr y, dy => hg' y dy⟩

noncomputable def dist : 𝕏.prod (𝕐.coprod 𝕫) ≅ (𝕏.prod 𝕐).coprod (𝕏.prod 𝕫) where
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
    (hf' : IsDerivative f f') (x : 𝕏.X) :
    update' f f' x = f x :=
  calc f x ⨁[𝕐] f' x (𝟬[𝕏] x)
    _ = f (x ⨁[𝕏] 𝟬[𝕏] x) := (hf' x (𝟬[𝕏] x)).symm
    _ = f x := by rw [𝕏.zero_update]

open exp in
noncomputable def exp (𝕏 𝕐 : Change) : Change where
  X := PartOrd.of (𝕏 ⟶ 𝕐)
  Δ := fun ⟨f, _⟩ => PartOrd.of
    { df : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (f x) //
      (∀ x dx, f x ⨁[𝕐] df x dx = update' f df (x ⨁[𝕏] dx)) ∧
      Monotone (update' f df) ∧
      ∃ g' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕐.Δ (update' f df x),
        ∀ x dx, update' f df (x ⨁[𝕏] dx) = update' f df x ⨁[𝕐] g' x dx
    }
  update := fun ⟨f, _⟩ ⟨df, _, hdf⟩ =>
    ⟨PartOrd.ofHom ⟨update' f df, hdf.left⟩, hdf.right⟩
  update_monotone := by
    intro ⟨f, _⟩ ⟨df, _, _, _⟩ x
    exact 𝕐.update_monotone (f x) _
  zero := by
    intro ⟨f, hf⟩
    have hf' := hf.choose_spec
    have upd₀ := update'_eq_of_isDerivative hf'
    have hmono : Monotone (update' f hf.choose) := by
      intro _ _ h
      rw [upd₀, upd₀]
      exact f.hom.monotone h
    refine ⟨hf.choose, ?_, hmono, ?_⟩
    · intro x dx
      rw [upd₀, hf' x dx]
    · have : update' f hf.choose = ⇑f := funext upd₀
      rw [this]
      exact ⟨hf.choose, hf'⟩
  zero_update := by
    intro ⟨f, hf⟩
    exact Hom.ext (PartOrd.ext (update'_eq_of_isDerivative hf.choose_spec ·))

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

def tensor_exchange :
    (𝕏.prod 𝕐).prod (𝕫.prod 𝕎) ≅ (𝕏.prod 𝕫).prod (𝕐.prod 𝕎) where
  hom := prod_lift (prod_lift (fst ≫ fst) (snd ≫ fst)) (prod_lift (fst ≫ snd) (snd ≫ snd))
  inv := prod_lift (prod_lift (fst ≫ fst) (snd ≫ fst)) (prod_lift (fst ≫ snd) (snd ≫ snd))

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
        refine PartOrd.ofHom ⟨fun ⟨df, hdf⟩ =>
          ⟨fun x => (df x) ≫ (f' (g x)), ?_, ?_⟩, ?_⟩
        · intro x dx
          symm
          calc f.base (g (x ⨁[𝕏] dx)) ⨁[𝕫]
                f' (g (x ⨁[𝕏] dx)) (df (x ⨁[𝕏] dx) (𝟬[𝕏] (x ⨁[𝕏] dx)))
            _ = f.base (g (x ⨁[𝕏] dx) ⨁[𝕐]
                  df (x ⨁[𝕏] dx) (𝟬[𝕏] (x ⨁[𝕏] dx))) := by
                rw [hf']
            _ = f.base (g x ⨁[𝕐] df x dx) := by
                congr 1
                symm
                exact hdf.left x dx
            _ = f.base (g x) ⨁[𝕫] f' (g x) (df x dx) :=
                hf' (g x) (df x dx)
        · have ⟨hmono_g, g'_g, hg'_g⟩ := hdf.right
          let df' : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ 𝕫.Δ ((g ≫ f.base) x) :=
            fun x => (df x) ≫ (f' (g x))
          have updEq : ∀ z, update' (g ≫ f.base) df' z =
              f.base (update' g df z) := by
            intro z
            symm
            exact hf' (g z) (df z (𝟬[𝕏] z))
          have hmono : Monotone (update' (g ≫ f.base) df') := by
            intro _ _ h
            rw [updEq, updEq]
            exact f.base.hom.monotone (hmono_g h)
          refine ⟨hmono, ?_⟩
          have : update' (g ≫ f.base) df'
              = ⇑f.base ∘ update' g df := funext updEq
          rw [this]
          refine ⟨fun x => (g'_g x) ≫ (f' (update' g df x)), ?_⟩
          intro x dx
          calc f.base (update' g df (x ⨁[𝕏] dx))
            _ = f.base (update' g df x ⨁[𝕐] g'_g x dx) :=
                congrArg f.base (hg'_g x dx)
            _ = f.base (update' g df x) ⨁[𝕫]
                f' (update' g df x) (g'_g x dx) :=
                hf' (update' g df x) (g'_g x dx)
        · intro ⟨df₁, _⟩ ⟨df₂, _⟩ h x dx
          change (df₁ x ≫ f' (g x)) dx ≤ (df₂ x ≫ f' (g x)) dx
          exact (f' (g x)).hom.monotone (h x dx)
      · intro ⟨g, _⟩ ⟨df, _, hmono, _⟩
        apply Hom.ext
        ext x
        exact hf' (g x) (df x (𝟬[𝕏] x))
  }

def ev : 𝕏.prod (exp 𝕏 𝕐) ⟶ 𝕐 where
  base := PartOrd.ofHom {
    toFun := fun (x, f) => f.base x
    monotone' := fun (_, f₁) (x₂, _) ⟨hx, hf⟩ =>
      (f₁.base.hom.monotone hx).trans (hf x₂)
  }
  hasDeriv := by
    refine ⟨?_, ?_⟩
    · intro (x, ⟨f, _⟩)
      refine PartOrd.ofHom ⟨fun ⟨dx, ⟨df, _, _, _⟩⟩ => df x dx, ?_⟩
      intro ⟨dx₁, ⟨df₁, _, _, _⟩⟩ ⟨dx₂, ⟨df₂, _, _, _⟩⟩ ⟨hdx, hdf⟩
      calc (df₁ x) dx₁
        _ ≤ (df₁ x) dx₂ := (df₁ x).hom.monotone hdx
        _ ≤ (df₂ x) dx₂ := hdf x dx₂
    intro (x, ⟨f, _⟩) ⟨dx, ⟨df, hev, hmono, _⟩⟩
    change exp.update' f df (x ⨁[𝕏] dx) = f x ⨁[𝕐] df x dx
    symm
    exact hev x dx

def coev : 𝕐 ⟶ exp 𝕏 (𝕏.prod 𝕐) where
  base := PartOrd.ofHom {
    toFun y := {
      base := PartOrd.ofHom {
        toFun x := (x, y)
        monotone' _ _ hx := ⟨hx, le_rfl⟩
      }
      hasDeriv := by
        refine ⟨fun x => PartOrd.ofHom ⟨fun dx => (dx, 𝟬[𝕐] y),
          fun _ _ h => Prod.mk_le_mk.mpr ⟨h, le_rfl⟩⟩, ?_⟩
        intro _ _
        exact Prod.ext rfl (𝕐.zero_update y).symm
    }
    monotone' _ _ hy x := ⟨le_rfl, hy⟩
  }
  hasDeriv := by
    refine ⟨fun y => ?_, ?_⟩
    · refine PartOrd.ofHom ⟨fun dy => ?_, ?_⟩
      · set f : 𝕏.X ⟶ (𝕏.prod 𝕐).X :=
          PartOrd.ofHom ⟨fun x => (x, y), fun _ _ hx => ⟨hx, le_rfl⟩⟩
        set df : ∀ x : 𝕏.X, 𝕏.Δ x ⟶ (𝕏.prod 𝕐).Δ (f x) :=
          fun x => PartOrd.ofHom ⟨fun dx => (dx, dy),
            fun _ _ h => Prod.mk_le_mk.mpr ⟨h, le_rfl⟩⟩
        have upd_eq : exp.update' f df = fun x => (x, y ⨁[𝕐] dy) := by
          ext x
          change (x ⨁[𝕏] 𝟬[𝕏] x, y ⨁[𝕐] dy) = (x, y ⨁[𝕐] dy)
          rw [𝕏.zero_update]
        refine ⟨df, ?_, ?_⟩
        · intro x dx
          change (x ⨁[𝕏] dx, y ⨁[𝕐] dy) =
            (x ⨁[𝕏] dx ⨁[𝕏] 𝟬[𝕏] (x ⨁[𝕏] dx), y ⨁[𝕐] dy)
          rw [𝕏.zero_update]
        · rw [upd_eq]
          refine ⟨fun _ _ h => Prod.mk_le_mk.mpr ⟨h, le_rfl⟩, ?_⟩
          exact ⟨fun x => PartOrd.ofHom ⟨fun dx => (dx, 𝟬[𝕐] (y ⨁[𝕐] dy)),
            fun _ _ h => Prod.mk_le_mk.mpr ⟨h, le_rfl⟩⟩,
            fun x dx => Prod.ext rfl (𝕐.zero_update (y ⨁[𝕐] dy)).symm⟩
      · intro _ _ h _ _
        exact Prod.mk_le_mk.mpr ⟨le_rfl, h⟩
    · intro y dy
      apply Hom.ext
      apply PartOrd.ext
      intro x
      exact Prod.ext (𝕏.zero_update x).symm rfl

noncomputable def tensorProductAdjunction (𝕏 : Change) :
    tensorLeft 𝕏 ⊣ expFunctor 𝕏 :=
  Adjunction.mkOfUnitCounit {
    unit.app _ := coev
    counit.app _ := ev
  }

noncomputable def ev' : (exp 𝕏 𝕐).prod 𝕏 ⟶ 𝕐 :=
  prod_lift snd fst ≫ ev

noncomputable def curry_left (f : 𝕏.prod 𝕐 ⟶ 𝕫) : 𝕏 ⟶ exp 𝕐 𝕫 :=
  coev ≫ (expFunctor 𝕐).map (prod_lift snd fst ≫ f)

noncomputable instance : MonoidalClosed Change :=
  MonoidalClosed.mk fun 𝕏 => Closed.mk _ (tensorProductAdjunction 𝕏)

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

def iso_terminal : [terminal]ᵈ ≅ terminal where
  hom := {
    base := PartOrd.disc.iso_terminal.hom
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }
  inv := {
    base := PartOrd.disc.iso_terminal.inv
    hasDeriv := ⟨fun _ => PartOrd.terminal.from _, fun _ _ => rfl⟩
  }

def iso_prod (𝕏 𝕐 : Change) : [𝕏.prod 𝕐]ᵈ ≅ ([𝕏]ᵈ).prod ([𝕐]ᵈ) where
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

def bot {L : SemilatSupCat} : terminal ⟶ U.obj L where
  base := PartOrd.ofHom ⟨fun ⟨⟩ => (⊥ : L), fun _ _ _ => le_rfl⟩
  hasDeriv :=
    ⟨fun ⟨⟩ => PartOrd.ofHom ⟨fun ⟨⟩ => (⊥ : L), fun _ _ _ => le_rfl⟩,
      fun ⟨⟩ ⟨⟩ => (bot_sup_eq (⊥ : L)).symm⟩

def sup {L : SemilatSupCat} : (U.obj L).prod (U.obj L) ⟶ U.obj L where
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

def one {𝕏 : Change} : disc 𝕏 ⟶ U.obj (PartOrd.powerset.obj 𝕏.X) where
  base := PartOrd.one
  hasDeriv := ⟨fun _ => PartOrd.ofHom ⟨fun _ => (∅ : Set 𝕏.X), fun _ _ _ => le_rfl⟩,
    fun x ⟨⟩ => (Set.union_empty {x}).symm⟩

end Section9

end Change
