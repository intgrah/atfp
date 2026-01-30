import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

open CategoryTheory

instance Nat.instMonoidAdd : Monoid ℕ where
  one := 0
  mul := Nat.add
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
  mul_assoc := Nat.add_assoc

instance Nat.instMonoidMax : Monoid ℕ where
  one := 0
  mul := Nat.max
  one_mul := Nat.zero_max
  mul_one := Nat.max_zero
  mul_assoc := Nat.max_assoc

instance Bool.instMonoidOr : Monoid Bool where
  one := false
  mul := or
  one_mul := Bool.false_or
  mul_one := Bool.or_false
  mul_assoc := Bool.or_assoc

instance Bool.instMonoidAnd : Monoid Bool where
  one := true
  mul := and
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  mul_assoc := Bool.and_assoc

instance List.instMonoidAppend (X : Type u) : Monoid (List X) where
  one := []
  mul := List.append
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

instance Set.instMonoidUnion (X : Type u) : Monoid (Set X) where
  one := ∅
  mul := Set.union
  one_mul := Set.empty_union
  mul_one := Set.union_empty
  mul_assoc := Set.union_assoc

open CategoryTheory

instance MonCat : Category (Bundled Monoid) where
  Hom := fun ⟨X, mX⟩ ⟨Y, mY⟩ => MonoidHom X Y
  id := fun ⟨X, mY⟩ => MonoidHom.id X
  comp := by
    intro ⟨X, mX⟩ ⟨Y, mY⟩ ⟨Z, mZ⟩ f g
    exact MonoidHom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

def SetCat : Category (Type u) where
  Hom := (· → ·)
  id := @id
  comp f g := g ∘ f
  id_comp := Function.id_comp
  comp_id := Function.comp_id
  assoc f g h := Function.comp_assoc h g f

def MatCat : Category ℕ where
  Hom m n := Matrix (Fin m) (Fin n) ℝ
  id _ := 1
  comp := (· * ·)
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc

def RelCat : Category (Type u) where
  Hom A B := A → B → Prop
  id _ := Eq
  comp := Relation.Comp
  id_comp _ := Relation.eq_comp
  comp_id _ := Relation.comp_eq
  assoc _ _ _ := Relation.comp_assoc

#check CategoryTheory.Functor

def BundledMonoid.Prod (M₁ M₂ : Bundled Monoid) : Bundled Monoid where
  α := M₁.α × M₂.α
  str := by
    have := M₁.str
    have := M₂.str
    infer_instance

def forget : Bundled Monoid ⥤ Type u where
  obj := fun ⟨M, _⟩ => M
  map := by
    intro ⟨_, _⟩ ⟨_, _⟩ f
    exact f.toFun
  map_id := by intros; rfl
  map_comp := by intros; rfl

section Datatype

#check PFunctor
#check Algebra

end Datatype
