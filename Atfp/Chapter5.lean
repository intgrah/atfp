module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Set.Semiring
public import Mathlib.Topology.UnitInterval
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Computability.Language

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

open scoped Pointwise in
noncomputable instance : ClosedSemiring (SetSemiring M) where
  kstar A := (⋃ n, A.down ^ n).up
  kstar_eq_one_add_mul_kstar a := by
    apply SetSemiring.down.injective
    simp only [SetSemiring.down_up, SetSemiring.down_add, SetSemiring.down_mul]
    change (⋃ n, a.down ^ n) = 1 ∪ a.down * ⋃ n, a.down ^ n
    rw [Set.mul_iUnion]
    simp_rw [← pow_succ']
    rw [← pow_zero a.down, Set.union_iUnion_nat_succ fun n => a.down ^ n]
  kstar_eq_one_add_kstar_mul a := by
    apply SetSemiring.down.injective
    simp only [SetSemiring.down_up, SetSemiring.down_add, SetSemiring.down_mul]
    change (⋃ n, a.down ^ n) = 1 ∪ (⋃ n, a.down ^ n) * a.down
    rw [Set.iUnion_mul]
    simp_rw [← pow_succ]
    rw [← pow_zero a.down, Set.union_iUnion_nat_succ fun n => a.down ^ n]
  kstar_induction_left a b x h := by
    rw [← SetSemiring.down_subset_down, SetSemiring.down_add, SetSemiring.down_mul] at h
    rw [← SetSemiring.down_subset_down, SetSemiring.down_mul]
    change (⋃ n, a.down ^ n) * b.down ⊆ x.down
    rw [Set.iUnion_mul]
    have ⟨hb, hax⟩ := Set.union_subset_iff.mp h
    apply Set.iUnion_subset
    intro n
    induction n with
    | zero => rw [pow_zero, one_mul]; exact hb
    | succ n ih => rw [pow_succ', mul_assoc]; exact (Set.mul_subset_mul_left ih).trans hax
  kstar_induction_right a b x h := by
    rw [← SetSemiring.down_subset_down, SetSemiring.down_add, SetSemiring.down_mul] at h
    rw [← SetSemiring.down_subset_down, SetSemiring.down_mul]
    change b.down * (⋃ n, a.down ^ n) ⊆ x.down
    rw [Set.mul_iUnion]
    have ⟨hb, hxa⟩ := Set.union_subset_iff.mp h
    apply Set.iUnion_subset
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one]; exact hb
    | succ n ih => rw [pow_succ, ← mul_assoc]; exact (Set.mul_subset_mul_right ih).trans hxa

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

/-! Example 5.1.12 -/

open Tropical in
instance : ClosedSemiring (Tropical ℕ∞) where
  toPartialOrder := inferInstanceAs (PartialOrder (Tropical ℕ∞)ᵒᵈ)
  kstar _ := trop 0
  kstar_eq_one_add_mul_kstar a := by
    cases a using tropRec with | h a =>
    cases a <;> rfl
  kstar_eq_one_add_kstar_mul a := by
    cases a using tropRec with | h a =>
    cases a <;> rfl
  kstar_induction_left a b x h := by
    change untrop x ≤ untrop (trop 0 * b)
    have h' : untrop x ≤ untrop (b + a * x) := h
    rw [untrop_mul, untrop_trop, zero_add]
    rw [untrop_add] at h'
    exact h'.trans (min_le_left _ _)
  kstar_induction_right a b x h := by
    change untrop x ≤ untrop (b * trop 0)
    have h' : untrop x ≤ untrop (b + x * a) := h
    rw [untrop_mul, untrop_trop, add_zero]
    rw [untrop_add] at h'
    exact h'.trans (min_le_left _ _)

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
    case zero.succ.succ =>
      simp only [zero_mul, add_zero] at h
      change (1 : ℕ∞) * _ ≤ _
      rw [one_mul]
      exact h
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
    case zero.succ.succ =>
      simp only [mul_zero, add_zero] at h
      change _ * (1 : ℕ∞) ≤ _
      rw [mul_one]
      exact h
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
  have h := @add_idem _ kleene.toIdemSemiring (3 : ℕ∞)
  rw [ha] at h
  exact absurd h (by decide)

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

open Matrix

variable {S : Type u} [ClosedSemiring S]

/-! Theorem 5.3.1 -/

theorem ClosedSemiring.zero_le (x : S) : 0 ≤ x := by
  simpa using ClosedSemiring.kstar_induction_left 1 0 x (by simp)

instance Matrix.instPartialOrder {α β : Type*} : PartialOrder (Matrix α β S) :=
  Pi.partialOrder

open scoped Computability in
noncomputable def Matrix.scalarStar (D : Matrix (Fin 1) (Fin 1) S) : Matrix (Fin 1) (Fin 1) S :=
  of fun _ _ => (D 0 0)∗

noncomputable def Matrix.cstar : {n : ℕ} → Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S
  | 0, M => M
  | n + 1, M =>
    let e := finSumFinEquiv (m := n) (n := 1)
    let M' := reindex e.symm e.symm M
    let Ds := scalarStar M'.toBlocks₂₂
    let Fs := cstar (M'.toBlocks₁₁ + M'.toBlocks₁₂ * Ds * M'.toBlocks₂₁)
    reindex e e (fromBlocks Fs (Fs * M'.toBlocks₁₂ * Ds) (Ds * M'.toBlocks₂₁ * Fs)
      (Ds + Ds * M'.toBlocks₂₁ * Fs * M'.toBlocks₁₂ * Ds))

section Plumbing

variable {κ ι γ δ : Type*}

private theorem Matrix.le_def {M N : Matrix γ δ S} : M ≤ N ↔ ∀ i j, M i j ≤ N i j :=
  Iff.rfl

private theorem Matrix.submatrix_le_submatrix {M N : Matrix γ δ S} (f : κ → γ) (g : ι → δ)
    (h : M ≤ N) : M.submatrix f g ≤ N.submatrix f g :=
  fun i j => h (f i) (g j)

private theorem Matrix.le_of_submatrix_le (e₁ : κ ≃ γ) (e₂ : ι ≃ δ) {M N : Matrix γ δ S}
    (h : M.submatrix e₁ e₂ ≤ N.submatrix e₁ e₂) : M ≤ N :=
  fun i j => by simpa using h (e₁.symm i) (e₂.symm j)

private theorem Matrix.fromRows_le {A₁ B₁ : Matrix κ δ S} {A₂ B₂ : Matrix ι δ S}
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) : fromRows A₁ A₂ ≤ fromRows B₁ B₂ := fun i j =>
  match i with
  | .inl k => h₁ k j
  | .inr k => h₂ k j

private theorem Matrix.fromCols_le {A₁ B₁ : Matrix γ κ S} {A₂ B₂ : Matrix γ ι S}
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) : fromCols A₁ A₂ ≤ fromCols B₁ B₂ := fun i j =>
  match j with
  | .inl k => h₁ i k
  | .inr k => h₂ i k

private theorem Matrix.reindex_one [DecidableEq κ] [DecidableEq γ] (e : κ ≃ γ) :
    reindex e e (1 : Matrix κ κ S) = 1 := by
  rw [reindex_apply, submatrix_one_equiv]

private theorem Matrix.reindex_add (e : κ ≃ γ) (X Y : Matrix κ κ S) :
    reindex e e (X + Y) = reindex e e X + reindex e e Y :=
  rfl

private theorem Matrix.reindex_mul [Fintype κ] [Fintype γ] (e : κ ≃ γ) (X Y : Matrix κ κ S) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

private theorem Matrix.reindex_unfold_left [Fintype κ] [Fintype γ] [DecidableEq κ]
    [DecidableEq γ] (e : κ ≃ γ) {M : Matrix γ γ S} {T : Matrix κ κ S}
    (h : T = 1 + reindex e.symm e.symm M * T) :
    reindex e e T = 1 + M * reindex e e T := by
  conv_lhs => rw [h]
  rw [reindex_add, reindex_mul, reindex_one, ← reindex_symm, Equiv.apply_symm_apply]

private theorem Matrix.reindex_unfold_right [Fintype κ] [Fintype γ] [DecidableEq κ]
    [DecidableEq γ] (e : κ ≃ γ) {M : Matrix γ γ S} {T : Matrix κ κ S}
    (h : T = 1 + T * reindex e.symm e.symm M) :
    reindex e e T = 1 + reindex e e T * M := by
  conv_lhs => rw [h]
  rw [reindex_add, reindex_mul, reindex_one, ← reindex_symm, Equiv.apply_symm_apply]

private theorem Matrix.reindex_mul_le {m : Type} [Fintype κ] [Fintype γ] (e : κ ≃ γ)
    {W : Matrix κ κ S} {N X : Matrix γ m S}
    (h : W * N.submatrix ⇑e id ≤ X.submatrix ⇑e id) :
    reindex e e W * N ≤ X := by
  refine le_of_submatrix_le e (Equiv.refl m) ?_
  rwa [Equiv.coe_refl, ← submatrix_mul_equiv (reindex e e W) N ⇑e e id, reindex_apply,
    submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]

private theorem Matrix.reindex_le_mul {m : Type} [Fintype κ] [Fintype γ] (e : κ ≃ γ)
    {W : Matrix κ κ S} {N X : Matrix m γ S}
    (h : N.submatrix id ⇑e * W ≤ X.submatrix id ⇑e) :
    N * reindex e e W ≤ X := by
  refine le_of_submatrix_le (Equiv.refl m) e ?_
  rwa [Equiv.coe_refl, ← submatrix_mul_equiv N (reindex e e W) id e ⇑e, reindex_apply,
    submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]

end Plumbing

section OrderedPlumbing

variable [IsOrderedRing S] {γ δ ε : Type*}

private theorem Matrix.le_add_left (M N : Matrix γ δ S) : M ≤ N + M := fun i j => by
  simpa using add_le_add (ClosedSemiring.zero_le (N i j)) (le_refl (M i j))

private theorem Matrix.add_le_add {M N P Q : Matrix γ δ S} (h₁ : M ≤ N) (h₂ : P ≤ Q) :
    M + P ≤ N + Q :=
  fun i j => _root_.add_le_add (h₁ i j) (h₂ i j)

private theorem Matrix.mul_le_mul_left [Fintype δ] (A : Matrix γ δ S) {X Y : Matrix δ ε S}
    (h : X ≤ Y) : A * X ≤ A * Y := by
  refine Matrix.le_def.mpr fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (h k j) (ClosedSemiring.zero_le _)

private theorem Matrix.mul_le_mul_right [Fintype δ] {X Y : Matrix γ δ S} (h : X ≤ Y)
    (A : Matrix δ ε S) : X * A ≤ Y * A := by
  refine Matrix.le_def.mpr fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (h i k) (ClosedSemiring.zero_le _)

end OrderedPlumbing

section ScalarStar

variable {m : Type}

private theorem Matrix.scalarStar_unfold_left (D : Matrix (Fin 1) (Fin 1) S) :
    scalarStar D = 1 + D * scalarStar D := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [scalarStar, of_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Fin.sum_univ_one]
  exact ClosedSemiring.kstar_eq_one_add_mul_kstar (D 0 0)

private theorem Matrix.scalarStar_unfold_right (D : Matrix (Fin 1) (Fin 1) S) :
    scalarStar D = 1 + scalarStar D * D := by
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim i 0
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simp only [scalarStar, of_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Fin.sum_univ_one]
  exact ClosedSemiring.kstar_eq_one_add_kstar_mul (D 0 0)

private theorem Matrix.scalarStar_ind_left (d : Matrix (Fin 1) (Fin 1) S) :
    ∀ N X : Matrix (Fin 1) m S, N + d * X ≤ X → scalarStar d * N ≤ X := by
  intro N X h
  refine Matrix.le_def.mpr fun i j => ?_
  obtain rfl : i = 0 := Subsingleton.elim i 0
  have h' := Matrix.le_def.mp h 0 j
  simp only [scalarStar, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one, of_apply]
    at h' ⊢
  exact ClosedSemiring.kstar_induction_left _ _ _ h'

private theorem Matrix.scalarStar_ind_right (d : Matrix (Fin 1) (Fin 1) S) :
    ∀ N X : Matrix m (Fin 1) S, N + X * d ≤ X → N * scalarStar d ≤ X := by
  intro N X h
  refine Matrix.le_def.mpr fun i j => ?_
  obtain rfl : j = 0 := Subsingleton.elim j 0
  have h' := Matrix.le_def.mp h i 0
  simp only [scalarStar, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_one, of_apply]
    at h' ⊢
  exact ClosedSemiring.kstar_induction_right _ _ _ h'

end ScalarStar

section Blocks

variable {p q : Type*} [Fintype p] [Fintype q]
variable {A : Matrix p p S} {B : Matrix p q S} {C : Matrix q p S} {D : Matrix q q S}
variable {Fs : Matrix p p S} {Ds : Matrix q q S}

private theorem Matrix.fromBlocks_star_unfold_left [DecidableEq p] [DecidableEq q]
    {M' : Matrix (p ⊕ q) (p ⊕ q) S} (hM : M' = fromBlocks A B C D)
    (hFs : Fs = 1 + (A + B * Ds * C) * Fs) (hDs : Ds = 1 + D * Ds) :
    fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds)
      = 1 + M' * fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds) := by
  subst hM
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_add, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hFs]
    congr 1
    simp only [Matrix.add_mul, Matrix.mul_assoc]
  · rw [zero_add]
    conv_lhs => rw [hFs]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
    abel
  · rw [zero_add]
    conv_lhs => rw [hDs]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  · nth_rewrite 1 2 [hDs]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
    abel

private theorem Matrix.fromBlocks_star_unfold_right [DecidableEq p] [DecidableEq q]
    {M' : Matrix (p ⊕ q) (p ⊕ q) S} (hM : M' = fromBlocks A B C D)
    (hFs : Fs = 1 + Fs * (A + B * Ds * C)) (hDs : Ds = 1 + Ds * D) :
    fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds)
      = 1 + fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds) * M' := by
  subst hM
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_add, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [hFs]
    congr 1
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  · rw [zero_add]
    nth_rewrite 1 [hDs]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
  · rw [zero_add]
    conv_lhs => rw [hFs]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
    abel
  · nth_rewrite 1 3 [hDs]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]
    abel

variable [IsOrderedRing S] {m : Type}

private theorem Matrix.fromBlocks_star_ind_left
    (hFs : ∀ N X : Matrix p m S, N + (A + B * Ds * C) * X ≤ X → Fs * N ≤ X)
    (hDs : ∀ N X : Matrix q m S, N + D * X ≤ X → Ds * N ≤ X)
    {N X : Matrix (p ⊕ q) m S} (h : N + fromBlocks A B C D * X ≤ X) :
    fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds) * N ≤ X := by
  obtain ⟨N₁, N₂, rfl⟩ : ∃ N₁ N₂, N = fromRows N₁ N₂ := ⟨_, _, (fromRows_toRows N).symm⟩
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromRows X₁ X₂ := ⟨_, _, (fromRows_toRows X).symm⟩
  rw [fromBlocks_mul_fromRows] at h ⊢
  have H1 : N₁ + (A * X₁ + B * X₂) ≤ X₁ := fun i j => h (.inl i) j
  have H2 : N₂ + (C * X₁ + D * X₂) ≤ X₂ := fun i j => h (.inr i) j
  rw [← add_assoc] at H2
  have S1 : Ds * (N₂ + C * X₁) ≤ X₂ := hDs _ _ H2
  have S4 : Fs * (N₁ + B * (Ds * N₂)) ≤ X₁ := by
    refine hFs _ _ ?_
    have key : N₁ + B * (Ds * N₂) + (A + B * Ds * C) * X₁
        = N₁ + A * X₁ + B * (Ds * (N₂ + C * X₁)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [key]
    calc N₁ + A * X₁ + B * (Ds * (N₂ + C * X₁))
        ≤ N₁ + A * X₁ + B * X₂ := Matrix.add_le_add le_rfl (Matrix.mul_le_mul_left B S1)
      _ = N₁ + (A * X₁ + B * X₂) := add_assoc _ _ _
      _ ≤ X₁ := H1
  refine fromRows_le ?_ ?_
  · calc Fs * N₁ + Fs * B * Ds * N₂
        = Fs * (N₁ + B * (Ds * N₂)) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ ≤ X₁ := S4
  · calc Ds * C * Fs * N₁ + (Ds + Ds * C * Fs * B * Ds) * N₂
        = Ds * N₂ + Ds * (C * (Fs * (N₁ + B * (Ds * N₂)))) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
      _ ≤ Ds * N₂ + Ds * (C * X₁) :=
        Matrix.add_le_add le_rfl (Matrix.mul_le_mul_left Ds (Matrix.mul_le_mul_left C S4))
      _ = Ds * (N₂ + C * X₁) := by rw [Matrix.mul_add]
      _ ≤ X₂ := S1

private theorem Matrix.fromBlocks_star_ind_right
    (hFs : ∀ N X : Matrix m p S, N + X * (A + B * Ds * C) ≤ X → N * Fs ≤ X)
    (hDs : ∀ N X : Matrix m q S, N + X * D ≤ X → N * Ds ≤ X)
    {N X : Matrix m (p ⊕ q) S} (h : N + X * fromBlocks A B C D ≤ X) :
    N * fromBlocks Fs (Fs * B * Ds) (Ds * C * Fs) (Ds + Ds * C * Fs * B * Ds) ≤ X := by
  obtain ⟨N₁, N₂, rfl⟩ : ∃ N₁ N₂, N = fromCols N₁ N₂ := ⟨_, _, (fromCols_toCols N).symm⟩
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromCols X₁ X₂ := ⟨_, _, (fromCols_toCols X).symm⟩
  rw [fromCols_mul_fromBlocks] at h ⊢
  have H1 : N₁ + (X₁ * A + X₂ * C) ≤ X₁ := fun i j => h i (.inl j)
  have H2 : N₂ + (X₁ * B + X₂ * D) ≤ X₂ := fun i j => h i (.inr j)
  rw [← add_assoc] at H2
  have S1 : (N₂ + X₁ * B) * Ds ≤ X₂ := hDs _ _ H2
  have S4 : (N₁ + N₂ * Ds * C) * Fs ≤ X₁ := by
    refine hFs _ _ ?_
    have key : N₁ + N₂ * Ds * C + X₁ * (A + B * Ds * C)
        = N₁ + X₁ * A + (N₂ + X₁ * B) * Ds * C := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [key]
    calc N₁ + X₁ * A + (N₂ + X₁ * B) * Ds * C
        ≤ N₁ + X₁ * A + X₂ * C := Matrix.add_le_add le_rfl (Matrix.mul_le_mul_right S1 C)
      _ = N₁ + (X₁ * A + X₂ * C) := add_assoc _ _ _
      _ ≤ X₁ := H1
  refine fromCols_le ?_ ?_
  · calc N₁ * Fs + N₂ * (Ds * C * Fs)
        = (N₁ + N₂ * Ds * C) * Fs := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ ≤ X₁ := S4
  · calc N₁ * (Fs * B * Ds) + N₂ * (Ds + Ds * C * Fs * B * Ds)
        = N₂ * Ds + (N₁ + N₂ * Ds * C) * Fs * (B * Ds) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
      _ ≤ N₂ * Ds + X₁ * (B * Ds) :=
        Matrix.add_le_add le_rfl (Matrix.mul_le_mul_right S4 (B * Ds))
      _ = (N₂ + X₁ * B) * Ds := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ ≤ X₂ := S1

end Blocks

theorem Matrix.cstar_unfold_left {n : ℕ} (M : Matrix (Fin n) (Fin n) S) :
    cstar M = 1 + M * cstar M := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    exact reindex_unfold_left finSumFinEquiv
      (fromBlocks_star_unfold_left (fromBlocks_toBlocks _).symm (ih _)
        (scalarStar_unfold_left _))

theorem Matrix.cstar_unfold_right {n : ℕ} (M : Matrix (Fin n) (Fin n) S) :
    cstar M = 1 + cstar M * M := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    exact reindex_unfold_right finSumFinEquiv
      (fromBlocks_star_unfold_right (fromBlocks_toBlocks _).symm (ih _)
        (scalarStar_unfold_right _))

theorem Matrix.cstar_ind_left [IsOrderedRing S] {n : ℕ} {m : Type}
    (T : Matrix (Fin n) (Fin n) S) (N X : Matrix (Fin n) m S) (h : N + T * X ≤ X) :
    cstar T * N ≤ X := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
    refine reindex_mul_le finSumFinEquiv ?_
    have h' : N.submatrix ⇑finSumFinEquiv id
        + reindex finSumFinEquiv.symm finSumFinEquiv.symm T * X.submatrix ⇑finSumFinEquiv id
        ≤ X.submatrix ⇑finSumFinEquiv id := by
      rw [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv T X _ finSumFinEquiv id]
      exact submatrix_le_submatrix ⇑finSumFinEquiv id h
    rw [← fromBlocks_toBlocks (reindex finSumFinEquiv.symm finSumFinEquiv.symm T)] at h'
    exact fromBlocks_star_ind_left (fun N X => ih _ N X) (scalarStar_ind_left _) h'

theorem Matrix.cstar_ind_right [IsOrderedRing S] {n : ℕ} {m : Type}
    (T : Matrix (Fin n) (Fin n) S) (N X : Matrix m (Fin n) S) (h : N + X * T ≤ X) :
    N * cstar T ≤ X := by
  induction n with
  | zero => exact fun i j => j.elim0
  | succ n ih =>
    refine reindex_le_mul finSumFinEquiv ?_
    have h' : N.submatrix id ⇑finSumFinEquiv
        + X.submatrix id ⇑finSumFinEquiv * reindex finSumFinEquiv.symm finSumFinEquiv.symm T
        ≤ X.submatrix id ⇑finSumFinEquiv := by
      rw [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv X T id finSumFinEquiv _]
      exact submatrix_le_submatrix id ⇑finSumFinEquiv h
    rw [← fromBlocks_toBlocks (reindex finSumFinEquiv.symm finSumFinEquiv.symm T)] at h'
    exact fromBlocks_star_ind_right (fun N X => ih _ N X) (scalarStar_ind_right _) h'

noncomputable instance {n : ℕ} [IsOrderedRing S] :
    ClosedSemiring (Matrix (Fin n) (Fin n) S) where
  toPartialOrder := Matrix.instPartialOrder
  kstar := Matrix.cstar
  kstar_eq_one_add_mul_kstar := Matrix.cstar_unfold_left
  kstar_eq_one_add_kstar_mul := Matrix.cstar_unfold_right
  kstar_induction_left := Matrix.cstar_ind_left
  kstar_induction_right := Matrix.cstar_ind_right

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
  zero_add a := max_eq_right zero_le
  add_zero a := max_eq_left zero_le
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
