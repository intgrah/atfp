module

public import Mathlib.Basic.Rel
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

structure ChangeStructure (X : Type*) [PartialOrder X] (Δ : X → Type*) where
  update : ∀ x : X, Δ x → X
  update_monotone : ∀ x dx, x ≤ update x dx
  zero : ∀ x, Δ x
  zero_update : ∀ x, update x (zero x) = x

structure Change where
  X : Type u
  Δ : X → Type u
  [orderX : PartialOrder X]
  [orderΔ : ∀ x, PartialOrder (Δ x)]
  str : ChangeStructure X Δ

attribute [instance] Change.orderX Change.orderΔ

notation:65 x " ⨁[" 𝕏 "] " dx:66 => ChangeStructure.update (Change.str 𝕏) x dx
notation "𝟬[" 𝕏 "]" => ChangeStructure.zero (Change.str 𝕏)

open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.ChangeStructure.update]
meta def delabChangeUpdate : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 6 && (e.getArg! 3).isAppOfArity ``Change.str 1
  let 𝕏 ← withNaryArg 3 (withAppArg delab)
  let x ← withNaryArg 4 delab
  let dx ← withNaryArg 5 delab
  `($x ⨁[$𝕏] $dx)

/-! Example 4.6.2 -/

example : ChangeStructure (Fin 100) (fun ⟨n, _⟩ => {k // n + k < 100}) where
  update := fun ⟨n, hn⟩ ⟨k, hk⟩ => ⟨n + k, by omega⟩
  update_monotone := by
    intro ⟨n, hn⟩ ⟨k, hk⟩
    simp
  zero := fun ⟨n, hn⟩ => ⟨0, hn⟩
  zero_update _ := rfl

/-! Example 4.6.3 -/

def ChangeStructure.ofSemilatticeSup (L : Type*) [SemilatticeSup L] [OrderBot L] :
    ChangeStructure L (fun _ => L) where
  update x dx := x ⊔ dx
  update_monotone _ _ := le_sup_left
  zero _ := ⊥
  zero_update := sup_bot_eq

end Section1

section Section2

/-! Definition 4.6.4 -/

def IsDerivative {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    {ΔX : X → Type*} {ΔY : Y → Type*}
    (cX : ChangeStructure X ΔX) (cY : ChangeStructure Y ΔY)
    (f : X → Y) (f' : ∀ x, ΔX x → ΔY (f x)) : Prop :=
  ∀ x dx, f (cX.update x dx) = cY.update (f x) (f' x dx)

namespace Examples

abbrev 𝒫ℕ := Set ℕ
abbrev 𝒫ℕ' := ChangeStructure.ofSemilatticeSup 𝒫ℕ

def f : 𝒫ℕ →o 𝒫ℕ where
  toFun X := X ∪ {1, 2}
  monotone' {X Y} h := by
    simp only [Set.union_insert, Set.union_singleton]
    apply Set.insert_subset_insert
    apply Set.insert_subset_insert
    exact h

def f'₀ : ∀ _ : 𝒫ℕ, 𝒫ℕ →o 𝒫ℕ := fun _ => OrderHom.id

example : IsDerivative 𝒫ℕ' 𝒫ℕ' f (fun x => f'₀ x) := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx
  tauto_set

def f'₁ : ∀ _ : 𝒫ℕ, 𝒫ℕ →o 𝒫ℕ := fun _ =>
  ⟨fun dx => dx \ {1}, fun _ _ h => Set.sdiff_subset_sdiff_left h⟩

example : IsDerivative 𝒫ℕ' 𝒫ℕ' f (fun x => f'₁ x) := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1}
  tauto_set

def f'₂ : ∀ _ : 𝒫ℕ, 𝒫ℕ →o 𝒫ℕ := fun _ =>
  ⟨fun dx => dx \ {2}, fun _ _ h => Set.sdiff_subset_sdiff_left h⟩

example : IsDerivative 𝒫ℕ' 𝒫ℕ' f (fun x => f'₂ x) := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {2}
  ext n
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff]
  tauto

def f'₃ : ∀ _ : 𝒫ℕ, 𝒫ℕ →o 𝒫ℕ := fun _ =>
  ⟨fun dx => dx \ {1, 2}, fun _ _ h => Set.sdiff_subset_sdiff_left h⟩

example : IsDerivative 𝒫ℕ' 𝒫ℕ' f (fun x => f'₃ x) := by
  intro (x : 𝒫ℕ) (dx : 𝒫ℕ)
  change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1, 2}
  tauto_set

end Examples

/-! Definition 4.6.5 -/

namespace SeminaiveFP

variable (L : Type u) [CompleteLattice L] (f : L →o L) (f' : L → L →o L)

mutual

def x : ℕ → L
  | 0 => ⊥
  | i + 1 => x i ⊔ dx i

def dx : ℕ → L
  | 0 => f ⊥
  | i + 1 => f' (x i) (dx i)

end

def semifix : L :=
  ⨆ i, x L f f' i

/-! Theorem 4.6.6 -/

theorem semifix_fix
    [WellFoundedGT L]
    (der : IsDerivative
      (ChangeStructure.ofSemilatticeSup L)
      (ChangeStructure.ofSemilatticeSup L)
      f (fun x => f' x)) :
    semifix L f f' = f.lfp := by
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
  have := fixedPoints.lfp_eq_sSup_iterate f
  symm
  change f.lfp = ⨆ i, x i
  simp only [h]
  apply this
  open OmegaCompletePartialOrder in
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨f.monotone, fun c => ?_⟩
  have ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition c.toOrderHom
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
    exact le_ωSup (c.map ⟨f, f.monotone⟩) n
  · exact ωSup_le_iff.mpr fun m => f.monotone (le_ωSup c m)

end SeminaiveFP

end Section2

namespace Change

section Section3

@[ext]
structure Hom (𝕏 𝕐 : Change.{u}) where
  base : 𝕏.X →o 𝕐.X
  hasDeriv : ∃ f' : ∀ x : 𝕏.X, 𝕏.Δ x →o 𝕐.Δ (base x),
    IsDerivative 𝕏.str 𝕐.str base (fun x => f' x)

variable {𝕏 𝕐 : Change.{u}}

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective _ _ h :=
    Hom.ext (DFunLike.coe_injective h)

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) :
    ∀ x : 𝕏.X, 𝕏.Δ x →o 𝕐.Δ (h.base x) :=
  h.hasDeriv.choose

def id (𝕏 : Change) : Hom 𝕏 𝕏 where
  base := OrderHom.id
  hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩

end Section3

instance : LargeCategory Change.{u} where
  Hom := Hom
  id := id
  comp {𝕏 𝕐 𝕫} f g := {
    base := g.base.comp f.base
    hasDeriv := by
      have ⟨f', hf⟩ := f.hasDeriv
      have ⟨g', hg⟩ := g.hasDeriv
      refine ⟨fun x => (g' (f x)).comp (f' x), ?_⟩
      intro x dx
      calc g (f (x ⨁[𝕏] dx))
        _ = g (f x ⨁[𝕐] f' x dx) := congrArg g (hf x dx)
        _ = g (f x) ⨁[𝕫] g' (f x) (f' x dx) := hg (f x) (f' x dx)
  }
  id_comp f := Hom.ext (OrderHom.comp_id f.base)
  comp_id f := Hom.ext (OrderHom.id_comp f.base)

section Section4

/-! Definition 4.6.7 -/

def terminal : Change where
  X := PUnit
  Δ _ := PUnit
  str := {
    update := fun ⟨⟩ ⟨⟩ => ⟨⟩
    update_monotone := fun ⟨⟩ ⟨⟩ => le_refl _
    zero := fun ⟨⟩ => ⟨⟩
    zero_update := fun ⟨⟩ => rfl
  }

def terminal.from (𝕏 : Change) : 𝕏 ⟶ terminal where
  base := OrderHom.const _ ⟨⟩
  hasDeriv := ⟨fun _ => OrderHom.const _ ⟨⟩, fun _ _ => rfl⟩

def isTerminal : IsTerminal terminal :=
  IsTerminal.ofUniqueHom terminal.from
    (fun _ _ => rfl)

end Section4

def initial : Change where
  X := PEmpty
  Δ := nofun
  orderΔ := nofun
  str := {
    update := nofun
    update_monotone := nofun
    zero := nofun
    zero_update := nofun
  }

def initial.to (𝕏 : Change) : initial ⟶ 𝕏 where
  base := ⟨nofun, nofun⟩
  hasDeriv := ⟨nofun, nofun⟩

def isInitial : IsInitial initial :=
  IsInitial.ofUniqueHom initial.to
    (fun _ _ => Hom.ext <| DFunLike.ext _ _ nofun)

section Section5

/-! Definition 4.6.8 -/

def prod (𝕏 𝕐 : Change.{u}) : Change.{u} where
  X := 𝕏.X × 𝕐.X
  Δ := fun (x, y) => 𝕏.Δ x × 𝕐.Δ y
  str := {
    update := fun (x, y) (dx, dy) =>
      (x ⨁[𝕏] dx, y ⨁[𝕐] dy)
    update_monotone := fun (x, y) (dx, dy) =>
      ⟨𝕏.str.update_monotone x dx, 𝕐.str.update_monotone y dy⟩
    zero := fun (x, y) => (𝟬[𝕏] x, 𝟬[𝕐] y)
    zero_update := fun (x, y) =>
      Prod.ext (𝕏.str.zero_update x) (𝕐.str.zero_update y)
  }

end Section5

section Section6

variable {𝕏 𝕐 𝕫 : Change.{u}}

/-! Definition 4.6.9 -/

def coprod (𝕏 𝕐 : Change.{u}) : Change.{u} where
  X := 𝕏.X ⊕ 𝕐.X
  Δ
    | .inl x => 𝕏.Δ x
    | .inr y => 𝕐.Δ y
  orderΔ
    | .inl x => 𝕏.orderΔ x
    | .inr y => 𝕐.orderΔ y
  str := {
    update
      | .inl x => fun dx => .inl (x ⨁[𝕏] dx)
      | .inr y => fun dy => .inr (y ⨁[𝕐] dy)
    update_monotone
      | .inl x => fun dx => Sum.inl_le_inl_iff.mpr (𝕏.str.update_monotone x dx)
      | .inr y => fun dy => Sum.inr_le_inr_iff.mpr (𝕐.str.update_monotone y dy)
    zero
      | .inl x => 𝟬[𝕏] x
      | .inr y => 𝟬[𝕐] y
    zero_update
      | .inl x => congrArg Sum.inl (𝕏.str.zero_update x)
      | .inr y => congrArg Sum.inr (𝕐.str.zero_update y)
  }

def inl : 𝕏 ⟶ 𝕏.coprod 𝕐 where
  base := ⟨Sum.inl, Sum.inl_mono⟩
  hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩

def inr : 𝕐 ⟶ 𝕏.coprod 𝕐 where
  base := ⟨Sum.inr, Sum.inr_mono⟩
  hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩

def coprod_desc (f : 𝕏 ⟶ 𝕫) (g : 𝕐 ⟶ 𝕫) : 𝕏.coprod 𝕐 ⟶ 𝕫 where
  base := (PartOrd.coprod_desc (PartOrd.ofHom f.base) (PartOrd.ofHom g.base)).hom
  hasDeriv := by
    have ⟨f', hf'⟩ := f.hasDeriv
    have ⟨g', hg'⟩ := g.hasDeriv
    exact ⟨fun | .inl x => f' x | .inr y => g' y,
      fun | .inl x, dx => hf' x dx | .inr y, dy => hg' y dy⟩

end Section6

section Section7

variable {𝕏 𝕐 𝕫 𝕎 : Change.{u}}

instance : PartialOrder (𝕏 ⟶ 𝕐) :=
  PartialOrder.lift Hom.base (fun _ _ h => Hom.ext h)

def exp.update'
    (f : 𝕏.X →o 𝕐.X) (df : ∀ x : 𝕏.X, 𝕏.Δ x →o 𝕐.Δ (f x))
    (x : 𝕏.X) : 𝕐.X :=
  f x ⨁[𝕐] df x (𝟬[𝕏] x)

theorem exp.update'_eq_of_isDerivative
    {f : 𝕏.X →o 𝕐.X} {f' : ∀ x : 𝕏.X, 𝕏.Δ x →o 𝕐.Δ (f x)}
    (hf' : IsDerivative 𝕏.str 𝕐.str f (fun x => f' x)) :
    update' f f' = f := by
  ext x
  calc f x ⨁[𝕐] f' x (𝟬[𝕏] x)
    _ = f (x ⨁[𝕏] 𝟬[𝕏] x) := (hf' x (𝟬[𝕏] x)).symm
    _ = f x := congrArg f (𝕏.str.zero_update x)

open exp in
noncomputable def exp (𝕏 𝕐 : Change.{u}) : Change.{u} where
  X := 𝕏 ⟶ 𝕐
  Δ f :=
    { df : ∀ x : 𝕏.X, 𝕏.Δ x →o 𝕐.Δ (f.base x) //
      (∀ x dx, f.base x ⨁[𝕐] df x dx = update' f.base df (x ⨁[𝕏] dx)) ∧
      ∃ g : 𝕏 ⟶ 𝕐, update' f.base df = g.base
    }
  str := {
    update := by
      intro ⟨f, _⟩ ⟨df, _, hdf⟩
      refine ⟨⟨update' f df, ?_⟩, ?_⟩
      all_goals
        have ⟨g, hg⟩ := hdf
        have hmono : Monotone (update' f df) :=
          hg ▸ g.base.monotone
      · exact hmono
      · have : (⟨update' f df, hmono⟩ : 𝕏.X →o 𝕐.X) = g.base :=
          DFunLike.ext' hg
        rw [this]
        exact g.hasDeriv
    update_monotone := by
      intro ⟨f, _⟩ ⟨df, _, _⟩ x
      exact 𝕐.str.update_monotone (f x) _
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
  }

def terminalCone : LimitCone (Functor.empty Change) where
  cone := asEmptyCone terminal
  isLimit := isTerminal

def fst : 𝕏.prod 𝕐 ⟶ 𝕏 where
  base := OrderHom.fst
  hasDeriv := ⟨fun _ => OrderHom.fst, fun _ _ => rfl⟩

def snd : 𝕏.prod 𝕐 ⟶ 𝕐 where
  base := OrderHom.snd
  hasDeriv := ⟨fun _ => OrderHom.snd, fun _ _ => rfl⟩

def prod_lift (f : 𝕫 ⟶ 𝕏) (g : 𝕫 ⟶ 𝕐) : 𝕫 ⟶ 𝕏.prod 𝕐 where
  base := f.base.prod g.base
  hasDeriv := by
    replace ⟨f', hf'⟩ := f.hasDeriv
    replace ⟨g', hg'⟩ := g.hasDeriv
    refine ⟨fun x => (f' x).prod (g' x), ?_⟩
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
      exact Prod.ext (congrArg (·.base x) h₁)
        (congrArg (·.base x) h₂))

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
    base := {
      toFun g := g ≫ f
      monotone' _ _ h x := f.base.monotone (h x)
    }
    hasDeriv := by
      have ⟨f', hf'⟩ := f.hasDeriv
      refine ⟨?_, ?_⟩
      · intro h
        let : PartialOrder ((𝕏.exp 𝕐).Δ h) := (𝕏.exp 𝕐).orderΔ h
        let : PartialOrder ((𝕏.exp 𝕫).Δ (h ≫ f)) := (𝕏.exp 𝕫).orderΔ (h ≫ f)
        let g := h.base
        refine ⟨fun ⟨df, hdf⟩ => ⟨fun x => (f' (g x)).comp (df x), ?_, ?_⟩, ?_⟩
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
        · have ⟨g_hom, hg_eq⟩ := hdf.right
          refine ⟨g_hom ≫ f, ?_⟩
          ext z
          calc update' (f.base.comp g) (fun x => (f' (g x)).comp (df x)) z
            _ = f.base (update' g df z) := hf' (g z) (df z (𝟬[𝕏] z)) |>.symm
            _ = f.base (g_hom.base z) := by rw [hg_eq]
        · intro ⟨df₁, _⟩ ⟨df₂, _⟩ h x dx
          change (f' (g x)) (df₁ x dx) ≤ (f' (g x)) (df₂ x dx)
          exact (f' (g x)).monotone (h x dx)
      · intro ⟨g, _⟩ ⟨df, _, _⟩
        apply Hom.ext
        ext x
        exact hf' (g x) (df x (𝟬[𝕏] x))
  }

noncomputable def ev : 𝕏 ⊗ 𝕏.exp 𝕐 ⟶ 𝕐 where
  base := {
    toFun := fun (x, f) => f.base x
    monotone' := fun (_, f₁) (x₂, _) ⟨hx, hf⟩ =>
      (f₁.base.monotone hx).trans (hf x₂)
  }
  hasDeriv := by
    refine ⟨?_, ?_⟩
    · intro p
      let : PartialOrder ((𝕏 ⊗ 𝕏.exp 𝕐).Δ p) := (𝕏 ⊗ 𝕏.exp 𝕐).orderΔ p
      refine ⟨fun ⟨dx, ⟨df, _, _⟩⟩ => df p.1 dx, ?_⟩
      intro ⟨dx₁, ⟨df₁, _, _⟩⟩ ⟨dx₂, ⟨df₂, _, _⟩⟩ ⟨hdx, hdf⟩
      calc (df₁ p.1) dx₁
        _ ≤ (df₁ p.1) dx₂ := (df₁ p.1).monotone hdx
        _ ≤ (df₂ p.1) dx₂ := hdf p.1 dx₂
    intro (x, ⟨f, _⟩) ⟨dx, ⟨df, hev, _⟩⟩
    change exp.update' f df (x ⨁[𝕏] dx) = f x ⨁[𝕐] df x dx
    exact (hev x dx)|>.symm

def coev : 𝕐 ⟶ 𝕏.exp (𝕏 ⊗ 𝕐) where
  base := {
    toFun y := {
      base := ⟨fun x => (x, y), fun _ _ hx => ⟨hx, le_rfl⟩⟩
      hasDeriv := by
        refine ⟨fun x => ⟨fun dx => (dx, 𝟬[𝕐] y), ?_⟩, ?_⟩
        · exact fun _ _ h => ⟨h, le_rfl⟩
        · exact fun _ _ => Prod.ext rfl (𝕐.str.zero_update y).symm
    }
    monotone' _ _ hy x := ⟨le_rfl, hy⟩
  }
  hasDeriv := by
    refine ⟨fun y => ⟨fun dy => ?_, ?_⟩, ?_⟩
    · set f : 𝕏.X →o (𝕏 ⊗ 𝕐).X :=
        ⟨fun x => (x, y), fun _ _ hx => ⟨hx, le_rfl⟩⟩
      let df : ∀ x : 𝕏.X, 𝕏.Δ x →o (𝕏 ⊗ 𝕐).Δ (f x) :=
        fun _ => ⟨fun dx => (dx, dy), fun _ _ h => ⟨h, le_rfl⟩⟩
      refine ⟨df, fun x dx => ?_, ⟨?_, ⟨fun x => ?_, ?_⟩⟩, ?_⟩
      · change (x ⨁[𝕏] dx, y ⨁[𝕐] dy) = (x ⨁[𝕏] dx ⨁[𝕏] 𝟬[𝕏] (x ⨁[𝕏] dx), y ⨁[𝕐] dy)
        rw [𝕏.str.zero_update]
      · exact ⟨fun x => (x, y ⨁[𝕐] dy), fun _ _ h => ⟨h, le_rfl⟩⟩
      · exact ⟨fun dx => (dx, 𝟬[𝕐] (y ⨁[𝕐] dy)), fun _ _ h => ⟨h, le_rfl⟩⟩
      · exact fun _ _ => Prod.ext rfl (𝕐.str.zero_update (y ⨁[𝕐] dy)).symm
      · ext x
        change (x ⨁[𝕏] 𝟬[𝕏] x, y ⨁[𝕐] dy) = (x, y ⨁[𝕐] dy)
        rw [𝕏.str.zero_update]
    · intro _ _ h _ _
      exact ⟨le_rfl, h⟩
    · intro y dy
      apply Hom.ext
      ext x
      exact Prod.ext (𝕏.str.zero_update x).symm rfl

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
    base := (PartOrd.dist (A := PartOrd.of 𝕏.X) (B := PartOrd.of 𝕐.X) (C := PartOrd.of 𝕫.X)).hom.hom
    hasDeriv := ⟨fun
        | (a, .inl b) => OrderHom.id (α := 𝕏.Δ a × 𝕐.Δ b)
        | (a, .inr c) => OrderHom.id (α := 𝕏.Δ a × 𝕫.Δ c),
      fun | (_, .inl _), _ => rfl | (_, .inr _), _ => rfl⟩
  }
  inv := {
    base := (PartOrd.dist (A := PartOrd.of 𝕏.X) (B := PartOrd.of 𝕐.X) (C := PartOrd.of 𝕫.X)).inv.hom
    hasDeriv := ⟨fun
        | .inl (a, b) => OrderHom.id (α := 𝕏.Δ a × 𝕐.Δ b)
        | .inr (a, c) => OrderHom.id (α := 𝕏.Δ a × 𝕫.Δ c),
      fun | .inl _, _ => rfl | .inr _, _ => rfl⟩
  }
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ fun | (_, .inl _) => rfl | (_, .inr _) => rfl
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ fun | .inl _ => rfl | .inr _ => rfl

end Section7

section Section8

def disc (𝕏 : Change) : Change where
  X := 𝕏.X
  Δ _ := PUnit
  orderX := (PartOrd.disc (PartOrd.of 𝕏.X)).str
  str := by
    let : PartialOrder 𝕏.X := (PartOrd.disc (PartOrd.of 𝕏.X)).str
    exact {
      update x _ := x
      update_monotone _ _ := le_refl _
      zero _ := ⟨⟩
      zero_update _ := rfl
    }

namespace disc

notation "[" 𝕏 "]ᵈ" => disc 𝕏

def comonad : Comonad Change where
  obj := disc
  map f := {
    base := (PartOrd.disc.comonad.map (PartOrd.ofHom f.base)).hom
    hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩
  }
  ε.app 𝕏 := {
    base := (PartOrd.disc.comonad.ε.app (PartOrd.of 𝕏.X)).hom
    hasDeriv := ⟨fun x => OrderHom.const _ (𝟬[𝕏] x), fun x _ => (𝕏.str.zero_update x).symm⟩
  }
  δ.app 𝕏 := {
    base := (PartOrd.disc.comonad.δ.app (PartOrd.of 𝕏.X)).hom
    hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩
  }

notation "[" f "]ᵈ" => disc.comonad.map f

def iso_terminal : [𝟙_ Change]ᵈ ≅ 𝟙_ Change where
  hom := {
    base := PartOrd.disc.iso_terminal.hom.hom
    hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩
  }
  inv := {
    base := PartOrd.disc.iso_terminal.inv.hom
    hasDeriv := ⟨fun _ => OrderHom.id, fun _ _ => rfl⟩
  }

def iso_prod (𝕏 𝕐 : Change) : [𝕏 ⊗ 𝕐]ᵈ ≅ [𝕏]ᵈ ⊗ [𝕐]ᵈ where
  hom := {
    base := (PartOrd.disc.iso_prod (PartOrd.of 𝕏.X) (PartOrd.of 𝕐.X)).hom.hom
    hasDeriv := ⟨fun _ => OrderHom.const _ (⟨⟩, ⟨⟩),
      fun _ _ => rfl⟩
  }
  inv := {
    base := (PartOrd.disc.iso_prod (PartOrd.of 𝕏.X) (PartOrd.of 𝕐.X)).inv.hom
    hasDeriv := ⟨fun _ => OrderHom.const _ ⟨⟩,
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
    change (fun x => x) '' s = s
    simp
  map_comp {𝕏 𝕐 𝕫} f g := by
    apply SupBotHom.ext
    intro s
    change (g.base.comp f.base) '' s = g.base '' (f.base '' s)
    simp [Set.image_image]

def U.obj (L : SemilatSupCat) : Change where
  X := L
  Δ _ := L
  str := ChangeStructure.ofSemilatticeSup L

def U.map {L M : SemilatSupCat} (f : SupBotHom L M) : U.obj L ⟶ U.obj M where
  base := OrderHom.ofClass f
  hasDeriv := by
    refine ⟨fun _ => OrderHom.ofClass f, ?_⟩
    intro (x : L) (dx : L)
    change (f (x ⊔ dx) : M) = f x ⊔ f dx
    exact map_sup f x dx

def U : SemilatSupCat ⥤ Change where
  obj := U.obj
  map := U.map

def bot {L : SemilatSupCat} : 𝟙_ Change ⟶ U.obj L where
  base := OrderHom.const _ (⊥ : L)
  hasDeriv :=
    ⟨fun _ => OrderHom.const _ (⊥ : L),
      fun ⟨⟩ ⟨⟩ => (bot_sup_eq (⊥ : L)).symm⟩

def sup {L : SemilatSupCat} : U.obj L ⊗ U.obj L ⟶ U.obj L :=
  let supHom : L × L →o L := {
    toFun := fun (l₁, l₂) => l₁ ⊔ l₂
    monotone' := fun _ _ ⟨h₁, h₂⟩ => sup_le_sup h₁ h₂
  }
  {
    base := supHom
    hasDeriv := by
      refine ⟨fun _ => supHom, ?_⟩
      intro (l₁, l₂) (dl₁, dl₂)
      change L at l₁ l₂ dl₁ dl₂
      exact sup_sup_sup_comm l₁ dl₁ l₂ dl₂
  }

def one {𝕏 : Change} : disc 𝕏 ⟶ U.obj (powerset.obj 𝕏) where
  base := (PartOrd.one (X := PartOrd.of 𝕏.X)).hom
  hasDeriv := ⟨fun _ => OrderHom.const _ (∅ : Set 𝕏.X),
    fun x ⟨⟩ => (Set.union_empty {x}).symm⟩

end Section9

end Change
