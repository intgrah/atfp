module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Computability.Language
import Mathlib.Data.Set.Semiring

@[expose] public section

universe u

variable {N : Type u} (G : Digraph N)

#check G.Adj

def exampleDigraph : Digraph (Fin 4) where
  Adj
   | 0, 0
   | 0, 1
   | 1, 2
   | 3, 0 => True
   | _, _ => False

def Digraph.adjMatrix (G : Digraph N) [DecidableRel G.Adj] : Matrix N N Bool :=
  (G.Adj · ·)

-- #eval exampleDigraph.adjMatrix

section Section1

/-! Definition 5.1.1 -/

variable {S : Type u} [inst : Semiring S]
#check Semiring
#check inst.zero
#check inst.one
#check inst.add
#check inst.mul
#check inst.toAddCommMonoid
#check inst.toMonoid.mul
#check inst.right_distrib
#check inst.left_distrib

/-! Example 5.1.2 -/

instance : AddZero Bool where
  zero := false
  add := or

instance : AddCommMonoid Bool where
  zero_add := Bool.false_or
  add_zero := Bool.or_false
  add_assoc := Bool.or_assoc
  add_comm := Bool.or_comm
  nsmul := nsmulRec

instance : Monoid Bool where
  one := ⊤
  mul := and
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  mul_assoc := Bool.and_assoc

instance : Semiring Bool where
  zero_mul := Bool.false_and
  mul_zero := Bool.and_false
  left_distrib := Bool.and_or_distrib_left
  right_distrib := Bool.and_or_distrib_right

/-! Example 5.1.3 -/

#synth Semiring Nat

/-! Example 5.1.4 -/

#synth Semiring Int

/-! Example 5.1.5 -/

variable {M : Type u} [Monoid M]
#synth Semiring (SetSemiring M)

/-! Example 5.1.6 -/

#synth Semiring (Tropical ℕ∞)

section Section1

/-! Definition 5.1.7 -/

variable {S : Type u} [inst : CommSemiring S]
#check CommSemiring
#check inst.mul_comm

/-! Definition 5.1.8 -/

variable {S : Type u} [Semiring S] [PartialOrder S] [IsOrderedRing S]
#check IsOrderedRing
#check add_le_add (α := S)
#check mul_le_mul (α := S)

/-! Definition 5.1.9 -/

open scoped Computability in
class ClosedSemiring (α : Type u) extends Semiring α, PartialOrder α, KStar α where
  kstar_eq_one_add_mul_kstar : ∀ a : α, a∗ = 1 + a * a∗
  kstar_eq_one_add_kstar_mul : ∀ a : α, a∗ = 1 + a∗ * a
  kstar_induction_left : ∀ a b x : α, b + a * x ≤ x → a∗ * b ≤ x
  kstar_induction_right : ∀ a b x : α, b + x * a ≤ x → b * a∗ ≤ x

/-! Example 5.1.10 -/

-- TODO monoid powerset

/-! Example 5.1.11 -/

instance : AddZero Prop where
  zero := False
  add := Or

instance : Semiring Prop where
  add_assoc _ _ _ := propext or_assoc
  zero_add := false_or
  add_zero := or_false
  add_comm _ _ := propext or_comm
  mul := And
  one := True
  one_mul := true_and
  mul_one := and_true
  zero_mul := false_and
  mul_zero := and_false
  nsmul := nsmulRec
  mul_assoc _ _ _ := propext and_assoc
  left_distrib _ _ _ := propext and_or_left
  right_distrib _ _ _ := propext or_and_right

instance : IsOrderedRing Prop where
  add_le_add_left _ _ hab _
    | .inl ha => .inl (hab ha)
    | .inr hc => .inr hc
  add_le_add_right _ _ hab _
    | .inl hc => .inl hc
    | .inr ha => .inr (hab ha)
  zero_le_one _ := ⟨⟩
  mul_le_mul_of_nonneg_left _ _ _ _ hbc
    | ⟨ha, hb⟩ => ⟨ha, hbc hb⟩
  mul_le_mul_of_nonneg_right _ _ _ _ hab
    | ⟨ha, hc⟩ => ⟨hab ha, hc⟩

instance : ClosedSemiring Prop where
  kstar _ := True
  kstar_eq_one_add_mul_kstar _ :=
    propext ⟨fun ⟨⟩ => .inl ⟨⟩, fun _ => ⟨⟩⟩
  kstar_eq_one_add_kstar_mul _ :=
    propext ⟨fun ⟨⟩ => .inl ⟨⟩, fun _ => ⟨⟩⟩
  kstar_induction_left _ _ _ h
    | ⟨⟨⟩, hb⟩ => h (.inl hb)
  kstar_induction_right _ _ _ h
    | ⟨hb, ⟨⟩⟩ => h (.inl hb)

instance : IsOrderedRing Bool where
  add_le_add_left a b hab c := by
    change a || c → b || c
    rw [Bool.or_eq_true, Bool.or_eq_true]
    intro
    | .inl ha => exact .inl (hab ha)
    | .inr hc => exact .inr hc
  zero_le_one := Bool.false_lt_true.le
  mul_le_mul_of_nonneg_left a ha b c hbc hab := by
    change a && c
    rw [Bool.and_eq_true]
    change a && b at hab
    rw [Bool.and_eq_true] at hab
    exact ⟨hab.left, hbc hab.right⟩
  mul_le_mul_of_nonneg_right a ha b c hbc hab := by
    change c && a
    rw [Bool.and_eq_true]
    change b && a at hab
    rw [Bool.and_eq_true] at hab
    exact ⟨hbc hab.left, hab.right⟩

instance : ClosedSemiring Bool where
  kstar _ := ⊤
  kstar_eq_one_add_mul_kstar _ := rfl
  kstar_eq_one_add_kstar_mul _ := rfl
  kstar_induction_left a b x h hb := by
    change b || a * x → x at h
    rw [Bool.or_eq_true] at h
    exact h (.inl hb)
  kstar_induction_right a b x h hb := by
    change b && true at hb
    rw [Bool.and_true] at hb
    change b || x * a → x at h
    rw [Bool.or_eq_true] at h
    exact h (.inl hb)

-- TODO

/-! Example 5.1.12 -/

instance : ClosedSemiring (Tropical ℕ∞) where
  kstar _ := Tropical.trop 0
  kstar_eq_one_add_mul_kstar a := by
    cases a using Tropical.tropRec with | h a =>
    cases a <;> rfl
  kstar_eq_one_add_kstar_mul a := by
    cases a using Tropical.tropRec with | h a =>
    cases a <;> rfl
  kstar_induction_left a b x h := by
    sorry
  kstar_induction_right a b x h := by
    sorry

/-! Example 5.1.13 -/

instance : ClosedSemiring ℕ∞ where
  kstar
    | 0 => 1
    | _ => ⊤
  kstar_eq_one_add_mul_kstar
    | ⊤ => rfl
    | 0 => rfl
    | some (n + 1) => rfl
  kstar_eq_one_add_kstar_mul
    | ⊤ => rfl
    | 0 => rfl
    | some (n + 1) => rfl
  kstar_induction_left a b x h := by
    cases a using ENat.nat_induction <;>
    cases b using ENat.nat_induction <;>
    cases x using ENat.nat_induction
    case succ.succ.succ =>
      exfalso
      norm_cast at h
      simp only [Nat.succ_mul, Nat.mul_succ] at h
      omega
    all_goals simp_all
  kstar_induction_right a b x h := by
    cases a using ENat.nat_induction <;>
    cases b using ENat.nat_induction <;>
    cases x using ENat.nat_induction
    case succ.succ.succ =>
      exfalso
      norm_cast at h
      simp only [Nat.succ_mul, Nat.mul_succ] at h
      omega
    all_goals simp_all

/-! Definition 5.1.14 -/

variable {S : Type u} [inst : IdemSemiring S]
#check IdemSemiring
#check add_idem

/-! Definition 5.1.15 -/

#check inst.toPartialOrder
#check inst.toSemilatticeSup
#check inst.bot_le

/-! Lemma 5.1.16 -/

#check inst.toMulLeftMono
#check inst.toMulRightMono

/-! Definition 5.1.17 -/

variable {S : Type u} [inst : KleeneAlgebra S]
#check KleeneAlgebra
#check inst.toIdemSemiring
#check inst.kstar
-- TODO

/-! Non-Example 5.1.18 -/

example : ¬∃ ka : KleeneAlgebra ℕ∞, ka.toSemiring = instCommSemiringENat.toSemiring := by
  intro ⟨kleene, ha⟩
  have h₁ : (3 : ℕ∞) + 3 = 6 := rfl
  have h₂ := @add_idem _ kleene.toIdemSemiring (3 : ℕ∞)
  have heq : (@HAdd.hAdd ℕ∞ ℕ∞ ℕ∞ (@instHAdd ℕ∞ kleene.toIdemSemiring.toDistrib.toAdd) 3 3 = 3) =
             (@HAdd.hAdd ℕ∞ ℕ∞ ℕ∞ (@instHAdd ℕ∞ instCommSemiringENat.toDistrib.toAdd) 3 3 = 3) := by
    rw [ha]
  have h₂' : (3 : ℕ∞) + 3 = 3 := cast heq h₂
  exact absurd (h₁.symm.trans h₂') (by decide)

/-! Example 5.1.19 -/

variable {α : Type u}
#synth KleeneAlgebra (Language α)

/-! Lemma 5.1.20 -/

#check Language.self_eq_mul_add_iff

end Section1

end Section1

section Section2

/-! Definition 5.2.1 -/

#check Module
-- TODO

end Section2

section Section3

variable {S M N : Type*} [ClosedSemiring S]

end Section3

section Section4

-- TODO

end Section4

section Section5

def graph : Digraph (Fin 2) where
  Adj _ _ := True

section Section1

variable {Q : Type u} {G : Digraph Q} [DecidableRel G.Adj]

def reachability : Digraph Q := sorry

end Section1

section Section2

-- TODO path counting

end Section2

section Section3

-- TODO APSP

end Section3

section Section4

-- TODO Kleene's algorithm

end Section4

section Section5

open scoped unitInterval

instance : Add I where
  add a b := ⟨max a.1 b.1, by aesop⟩

instance : AddCommMonoid I where
  zero_add a := max_eq_right zero_le'
  add_zero a := max_eq_left zero_le'
  add_assoc a b c := Subtype.ext (max_assoc a.1 b.1 c.1)
  add_comm a b := Subtype.ext (max_comm a.1 b.1)
  nsmul := nsmulRec

instance : Semiring I where
  left_distrib a b c := Subtype.ext (mul_max_of_nonneg b.1 c.1 (Set.mem_Icc.mp a.2).1)
  right_distrib a b c := Subtype.ext (max_mul_of_nonneg a.1 b.1 (Set.mem_Icc.mp c.2).1)

instance : KleeneAlgebra I where
  kstar _ := 1
  bot_le _ := bot_le
  one_le_kstar _ := le_rfl
  mul_kstar_le_kstar _ := le_top
  kstar_mul_le_kstar _ := le_top
  mul_kstar_le_self _ x _ := show x * 1 ≤ x by rw [mul_one]
  kstar_mul_le_self _ x _ := show 1 * x ≤ x by rw [one_mul]

-- TODO Viterbi

end Section5

-- TODO graph algorithms

end Section5
