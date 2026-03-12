module

import Mathlib.Data.Finset.Attr
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Tactic.SetLike

public import Atfp.Chapter3

@[expose] public section

universe u

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
