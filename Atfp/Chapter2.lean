module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Data.Matrix.Basic

import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Category.RelCat
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Order.Category.PartOrd

@[expose] public section

open CategoryTheory Limits

section Section1

universe u

/-! Example 2.1.1 -/

variable {M : Type u} [inst : Monoid M]
#check Monoid
#check inst.one
#check inst.mul
#check inst.one_mul
#check inst.mul_one
#check inst.mul_assoc

/-! Example 2.1.2 -/

variable {X : Type u}

#check Nat.instAddMonoid

instance : Monoid (X → X) where
  one := @id X
  mul f g := f ∘ g
  one_mul := Function.id_comp
  mul_one := Function.comp_id
  mul_assoc := Function.comp_assoc

#check Matrix.semiring.toMonoidWithZero.toMonoid

#check FreeMonoid.instCancelMonoid.toMonoid

/-! Example 2.1.3 -/

variable [inst : Group X]
#check Group
#check inst.toMonoid
#check inv_mul_cancel
#check mul_inv_cancel

#check Int.instAddGroup

/-! Example 2.1.4 -/

-- For all x ∈ G, there exists a unique i such that x * i = i * x = e

/-! Example 2.1.5 -/

variable [inst : PartialOrder X]
#check PartialOrder
#check inst.le
#check inst.le_refl
#check inst.le_trans
#check inst.le_antisymm

/-! Example 2.1.6 -/

#check Nat.instPartialOrder

instance (priority := low) Nat.instPartialOrderDvd : PartialOrder ℕ where
  le a b := a ∣ b
  lt a b := a ∣ b ∧ ¬b ∣ a
  le_refl := Nat.dvd_refl
  le_trans _ _ _ := Nat.dvd_trans
  le_antisymm _ _ := Nat.dvd_antisymm

variable (α : Type u)
#synth PartialOrder (Set α)

instance {X : Type u} : PartialOrder (List X) where
  le w w' := ∃ w₀, w' = w ++ w₀
  le_refl w := ⟨[], List.append_nil w |>.symm⟩
  le_trans w w' w'' := by
    intro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    rw [h₂, h₁]
    exact ⟨w₁ ++ w₂, List.append_assoc w w₁ w₂⟩
  le_antisymm w w' := by
    intro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    simp_all

end Section1

section Section2

universe u

variable {M N : Type u} [Monoid M] [Monoid N] (f : MonoidHom M N)
#check MonoidHom
#check f.toFun
#check f.map_one
#check f.map_mul

variable (X Y : Pointed) (f : Pointed.Hom X Y)
#check Pointed
#check X.X
#check X.point
#check Pointed.Hom
#check f.toFun
#check f.map_point

variable {M' N' : Type u} [Group M'] [Group N'] (f : MonoidHom M' N')
#check f.toFun
#check f.map_one
#check f.map_mul
#check f.map_inv

section Section1

/-! Example 2.2.1 -/

variable [PartialOrder X] [PartialOrder Y] (f : OrderHom X Y)
#check OrderHom
#check f.toFun
#check f.monotone

end Section1

end Section2

section Section3

universe u

/-! Definition 2.3.1 -/

variable {𝓒 𝓓 : Type u} [inst : Category 𝓒] (X Y Z : 𝓒) (f : X ⟶ Y) (g : Y ⟶ Z)
#check Category
#check X ⟶ Y
#check 𝟙 X
#check f ≫ g
#check inst.id_comp
#check inst.comp_id
#check inst.assoc

section Section1

/-! Example 2.3.2 -/

#check types

/-! Example 2.3.3 -/

#check RelCat.instLargeCategory

/-! Example 2.3.4 -/

def Matrix.instCategory {S} [Semiring S] : Category ℕ where
  Hom m n := Matrix (Fin m) (Fin n) S
  id _ := 1
  comp f g := f * g
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc

/-! Example 2.3.5 -/

#check MonCat.instCategory

/-! Example 2.3.6 -/

#check GrpCat.instCategory

/-! Example 2.3.7 -/

#check PartOrd.instCategory

end Section1

section Section2

variable [inst : Category 𝓒] [inst' : Category 𝓓] (F : 𝓒 ⥤ 𝓓)
#check Functor
#check F.obj
#check F.map
#check F.map_id
#check F.map_comp

end Section2

section Section3

/-! Definition 2.3.8 -/

#check HasTerminal
#check hasTerminal_of_unique
#check terminal.from
#check terminal.hom_ext

/-! Definition 2.3.9 -/

#check HasInitial
#check hasInitial_of_unique
#check initial.to
#check initial.hom_ext

/-! Example 2.3.10 -/

#check Types.isTerminalPunit
#check Types.isInitialPunit

/-! Definition 2.3.11 -/
#check HasBinaryProducts
#check Limits.prod
#check prod.fst
#check prod.snd
#check prod.lift
#check prod.hom_ext
#check prod.map

/-! Example 2.3.12 -/

#check Types.binaryProductIso

/-! Example 2.3.13 -/

noncomputable def MonCat.prod (X Y : MonCat) : MonCat :=
  Limits.prod X Y

-- TODO: binary products in Mon

/-! Example 2.3.14 -/

instance [Category 𝓒] [Category 𝓓] : Category (𝓒 × 𝓓) := inferInstance

/-! Definition 2.3.15 -/

#check HasCoproducts
#check Limits.coprod
#check coprod.inl
#check coprod.inr
#check coprod.desc
#check coprod.hom_ext
#check coprod.map

/-! Example 2.3.16 -/

#check Types.coproductIso

/-! Example 2.3.17 -/

#check Monoid.Coprod

#check MonCat

/-! Definition 2.3.18 -/

#check ihom

-- TODO

end Section3

end Section3
