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

structure IsDerivative {𝕏 𝕐 : Change.{u}}
    (f : 𝕏.X ⟶ 𝕐.X)
    (f' : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (f x)) : Prop where
  eq : ∀ x dx, f (x ⨁[𝕏] dx) = f x ⨁[𝕐] f' x dx
  zero : ∀ x, f' x (𝟬[𝕏] x) = 𝟬[𝕐] (f x)

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

def f'₀ : (x : Set ℕ) → Set ℕ → Set ℕ := fun _ dx => dx

-- example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₀ where
--   eq x dx := by change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx; tauto_set
--   zero _ := rfl

-- def f'₁ : (x : Set ℕ) → Set ℕ → Set ℕ := fun _ dx => dx \ {1}

-- example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₁ where
--   eq x dx := by change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1}; tauto_set
--   zero _ := by change ⊥ \ {1} = ⊥; simp

-- def f'₂ : (x : Set ℕ) → Set ℕ → Set ℕ := fun _ dx => dx \ {2}

-- example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₂ where
--   eq x dx := by
--     change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {2}
--     ext n
--     simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff]
--     tauto
--   zero _ := by change ⊥ \ {2} = ⊥; simp

-- def f'₃ : (x : Set ℕ) → Set ℕ → Set ℕ := fun _ dx => dx \ {1, 2}

-- example : @IsDerivative 𝒫ℕ' 𝒫ℕ' f f'₃ where
--   eq x dx := by change x ∪ dx ∪ {1, 2} = x ∪ {1, 2} ∪ dx \ {1, 2}; tauto_set
--   zero _ := by change ⊥ \ {1, 2} = ⊥; simp

end Examples

/-! Definition 4.6.5 -/

namespace SeminaiveFP

variable (L : CompleteLat.{u})
  (f : PartOrd.of L ⟶ PartOrd.of L)
  (f' : PartOrd.of L → PartOrd.of L → PartOrd.of L)

mutual

def x : ℕ → PartOrd.of L
  | 0 => ⊥
  | i + 1 => x i ⊔ dx i

def dx : ℕ → PartOrd.of L
  | 0 => f ⊥
  | i + 1 => f' (x i) (dx i)

end

def semifix
    (_ : @IsDerivative
      (Change.ofCompleteLat L)
      (Change.ofCompleteLat L)
      f f') : L :=
  ⨆ i, x L f f' i

/-! Theorem 4.6.6 -/

theorem semifix_fix
    [WellFoundedGT L]
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
        _ = f (x j) ⊔ f' (x j) (dx j) := rfl
        _ = f (x j ⊔ dx j) := (der.eq (x j) (dx j)).symm
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
  rw [OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨f.hom.monotone, fun c => ?_⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition c
  apply le_antisymm
  · have hsup : OmegaCompletePartialOrder.ωSup c = c n := le_antisymm
      (OmegaCompletePartialOrder.ωSup_le_iff.mpr fun m => by
        rcases le_or_gt n m with h | h
        · exact (hn m h).symm ▸ le_rfl
        · exact c.monotone h.le)
      (OmegaCompletePartialOrder.le_ωSup c n)
    rw [hsup]
    exact OmegaCompletePartialOrder.le_ωSup (c.map ⟨f.hom, f.hom.monotone⟩) n
  · exact OmegaCompletePartialOrder.ωSup_le_iff.mpr fun m =>
      f.hom.monotone (OmegaCompletePartialOrder.le_ωSup c m)

end SeminaiveFP

end Section2

namespace Change

section Section3

variable (𝕏 𝕐 : Change)

@[ext]
structure Hom where
  base : 𝕏.X ⟶ 𝕐.X
  hasDeriv : ∃ f' : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (base x),
    IsDerivative base f'

instance : FunLike (Hom 𝕏 𝕐) 𝕏.X 𝕐.X where
  coe f := f.base
  coe_injective' _ _ h :=
    Hom.ext (ConcreteCategory.hom_injective (DFunLike.coe_fn_eq.mp h))

variable {𝕏 𝕐 : Change}

noncomputable def Hom.deriv (h : Hom 𝕏 𝕐) :
    ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (h.base x) :=
  h.hasDeriv.choose

def id 𝕏 : Hom 𝕏 𝕏 where
  base := 𝟙 𝕏.X
  hasDeriv := ⟨fun _ dx => dx, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

end Section3

instance : LargeCategory Change where
  Hom := Hom
  id := id
  comp {𝕏 𝕐 𝕫} f g := {
    base := f.base ≫ g.base
    hasDeriv := by
      obtain ⟨f, f', hf⟩ := f
      obtain ⟨g, g', hg⟩ := g
      refine ⟨fun x dx => g' (f x) (f' x dx), ⟨fun x dx => by
        calc g (f (x ⨁[𝕏] dx))
          _ = g (f x ⨁[𝕐] f' x dx) := congrArg g (hf.eq x dx)
          _ = g (f x) ⨁[𝕫] g' (f x) (f' x dx) := hg.eq (f x) (f' x dx), fun x => by
        dsimp; rw [hf.zero, hg.zero]⟩⟩
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
  hasDeriv := ⟨fun _ _ => ⟨⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩

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
  hasDeriv := ⟨nofun, ⟨nofun, nofun⟩⟩

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

end Section6

section Section7

instance {𝕏 𝕐 : Change} : PartialOrder (𝕏 ⟶ 𝕐) :=
  PartialOrder.lift
    (fun f => f.base.hom)
    (fun _ _ h => Hom.ext (PartOrd.Hom.ext h))

def updBase {𝕏 𝕐 : Change}
    (f : 𝕏.X ⟶ 𝕐.X) (df : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (f x))
    (x : 𝕏.X) : 𝕐.X :=
  f x ⨁[𝕐] df x (𝟬[𝕏] x)

def updBaseHom {𝕏 𝕐 : Change}
    (f : 𝕏.X ⟶ 𝕐.X) (df : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (f x))
    (hz : ∀ x, df x (𝟬[𝕏] x) = 𝟬[𝕐] (f x)) : 𝕏.X ⟶ 𝕐.X :=
  PartOrd.ofHom {
    toFun := updBase f df
    monotone' {x₁ x₂} h := by
      calc updBase f df x₁
        _ = f x₁ ⨁[𝕐] 𝟬[𝕐] (f x₁) := by rw [updBase, hz]
        _ = f x₁ := 𝕐.zero_update _
        _ ≤ f x₂ := f.hom.monotone h
        _ = f x₂ ⨁[𝕐] 𝟬[𝕐] (f x₂) := (𝕐.zero_update _).symm
        _ = updBase f df x₂ := by rw [updBase, hz]
  }

noncomputable def exp (𝕏 𝕐 : Change) : Change where
  X := PartOrd.of (𝕏 ⟶ 𝕐)
  Δ := fun ⟨f, _⟩ => PartOrd.of
    { df : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (f x) //
      (∀ x, df x (𝟬[𝕏] x) = 𝟬[𝕐] (f x))
      ∧
      ∃ g' : ∀ x : 𝕏.X, 𝕏.Δ x → 𝕐.Δ (updBase f df x),
        (∀ x, g' x (𝟬[𝕏] x) = 𝟬[𝕐] (updBase f df x))
        ∧ (∀ x dx, updBase f df (x ⨁[𝕏] dx)
            = updBase f df x ⨁[𝕐] g' x dx)
        ∧ ∀ x dx,
          f x ⨁[𝕐] df x dx
            = updBase f df x ⨁[𝕐] g' x dx }
  update := fun ⟨f, _⟩ ⟨df, hz, hdf⟩ => {
    base := PartOrd.ofHom {
      toFun x := f x ⨁[𝕐] df x (𝟬[𝕏] x)
      monotone' {x₁ x₂} h := by
        calc f x₁ ⨁[𝕐] df x₁ (𝟬[𝕏] x₁)
          _ = f x₁ ⨁[𝕐] 𝟬[𝕐] (f x₁) := by rw [hz]
          _ = f x₁ := 𝕐.zero_update _
          _ ≤ f x₂ := f.hom.monotone h
          _ = f x₂ ⨁[𝕐] 𝟬[𝕐] (f x₂) := (𝕐.zero_update _).symm
          _ = f x₂ ⨁[𝕐] df x₂ (𝟬[𝕏] x₂) := by rw [hz]
    }
    hasDeriv := ⟨hdf.choose, ⟨fun x dx => by
      change updBase f df (x ⨁[𝕏] dx)
        = updBase f df x ⨁[𝕐] hdf.choose x dx
      exact (hdf.choose_spec.2 x dx).1, hdf.choose_spec.1⟩⟩
  }
  update_monotone f dfs := by
    obtain ⟨df, hz, hdf⟩ := dfs
    intro x
    dsimp
    exact 𝕐.update_monotone _ _
  zero fh :=
    let f' := fh.hasDeriv.choose
    let hf' := fh.hasDeriv.choose_spec
    have upd₀ : ∀ x, updBase fh.base f' x = fh.base x :=
      fun x => (hf'.eq x (𝟬[𝕏] x)).symm.trans (congrArg _ (𝕏.zero_update x))
    ⟨f', hf'.zero, ⟨fun x dx => (upd₀ x).symm ▸ f' x dx,
      ⟨fun x => by
        have key : ∀ (a b : 𝕐.X) (h : a = b) (dy : 𝕐.Δ b)
            (_ : dy = 𝟬[𝕐] b),
            (h.symm ▸ dy) = 𝟬[𝕐] a := by
          intro a b h dy hdy; subst h; exact hdy
        exact key _ _ (upd₀ x) _ (hf'.zero x),
      fun x dx => by
        have aux : ∀ (a b : 𝕐.X) (h : a = b) (dy : 𝕐.Δ b),
            a ⨁[𝕐] (h.symm ▸ dy) = b ⨁[𝕐] dy := by
          intro a b h dy; subst h; rfl
        refine ⟨?_, (aux _ _ (upd₀ x) (f' x dx)).symm⟩
        calc updBase fh.base f' (x ⨁[𝕏] dx)
          _ = fh.base (x ⨁[𝕏] dx) := upd₀ _
          _ = fh.base x ⨁[𝕐] f' x dx := hf'.eq x dx
          _ = updBase fh.base f' x ⨁[𝕐]
                ((upd₀ x).symm ▸ f' x dx) :=
              (aux _ _ (upd₀ x) (f' x dx)).symm⟩⟩⟩
  zero_update f := by
    apply Hom.ext
    apply PartOrd.ext
    intro x
    dsimp [update, zero]
    have hf' := f.hasDeriv.choose_spec
    exact (hf'.eq x (𝟬[𝕏] x)).symm.trans (congrArg _ (𝕏.zero_update x))

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
  map {𝕏 𝕐} f := {
    base := PartOrd.disc.comonad.map f.base
    hasDeriv := ⟨fun _ _ => ⟨⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
  }
  ε.app 𝕏 := {
    base := PartOrd.disc.comonad.ε.app 𝕏.X
    hasDeriv := ⟨fun x _ => 𝟬[𝕏] x, ⟨fun x _ => (𝕏.zero_update x).symm, fun _ => rfl⟩⟩
  }
  δ.app 𝕏 := {
    base := PartOrd.disc.comonad.δ.app 𝕏.X
    hasDeriv := ⟨fun _ _ => ⟨⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
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
  hasDeriv := ⟨fun _ (dx : L) => (f dx : M), ⟨fun (x : L) (dx : L) => by
    change (f (x ⊔ dx) : M) = f x ⊔ f dx
    exact map_sup f x dx, fun _ => by
    change (f ⊥ : M) = ⊥
    exact map_bot f⟩⟩

def U : SemilatSupCat ⥤ Change where
  obj := U.obj
  map := U.map

def bot {L : SemilatSupCat} : terminal ⟶ U.obj L where
  base := PartOrd.ofHom ⟨fun ⟨⟩ => (⊥ : L), fun _ _ _ => le_rfl⟩
  hasDeriv :=
    ⟨fun ⟨⟩ ⟨⟩ => (⊥ : L),
      ⟨fun ⟨⟩ ⟨⟩ => (bot_sup_eq (α := L.X) ⊥).symm,
       fun ⟨⟩ => rfl⟩⟩

def sup {L : SemilatSupCat} : (U.obj L).prod (U.obj L) ⟶ U.obj L where
  base := PartOrd.ofHom {
    toFun := fun (l₁, l₂) => l₁ ⊔ l₂
    monotone' _ _ := fun ⟨hl, hm⟩ =>
      sup_le (le_sup_of_le_left hl) (le_sup_of_le_right hm)
  }
  hasDeriv :=
    ⟨fun _ (dl₁, dl₂) => (dl₁ ⊔ dl₂ : L),
      ⟨fun (l₁, l₂) (dl₁, dl₂) => by
        change L at l₁ l₂ dl₁ dl₂
        dsimp [U.obj, prod, update]
        exact sup_sup_sup_comm l₁ dl₁ l₂ dl₂,
      fun _ => by change (⊥ : L) ⊔ ⊥ = ⊥; simp⟩⟩

end Section9

end Change
