module

public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Order.OrderIsoNat

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

theorem iterate_bot_isFixedPt_exists {L : Type u} [SemilatticeSup L] [OrderBot L]
    [WellFoundedGT L]
    (f : L →o L) :
    ∃ n, Function.IsFixedPt f (f^[n] ⊥) := by
  have incr : ∀ n, f^[n] ⊥ ≤ f^[n + 1] ⊥ :=
    fun n => Monotone.iterate f.monotone n bot_le
  let chain : ℕ →o L :=
    ⟨fun n => f^[n] ⊥, fun a b hab => by
      induction hab with
      | refl => exact le_rfl
      | step h ih => exact ih.trans (incr _)⟩
  have ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition chain
  have hfix : f^[n] ⊥ = f^[n + 1] ⊥ := hn (n + 1) (Nat.le_succ n)
  rw [Function.iterate_succ_apply'] at hfix
  exact ⟨n, hfix.symm⟩

theorem iterate_bot_const {L : Type u} [SemilatticeSup L] [OrderBot L]
    (f : L →o L) {n : ℕ} (hfp : Function.IsFixedPt f (f^[n] ⊥)) (m : ℕ) (hm : n ≤ m) :
    f^[m] ⊥ = f^[n] ⊥ := by
  induction hm with
  | refl => rfl
  | step hm ih =>
    rw [Function.iterate_succ_apply', ih]
    exact hfp

theorem iterate_bot_isFixedPt {L : Type u} [SemilatticeSup L] [OrderBot L]
    (f : L →o L) {n : ℕ} (hfp : Function.IsFixedPt f (f^[n] ⊥)) (m : ℕ) (hm : n ≤ m) :
    Function.IsFixedPt f (f^[m] ⊥) := by
  change f (f^[m] ⊥) = f^[m] ⊥
  rw [iterate_bot_const f hfp m hm, hfp, ← iterate_bot_const f hfp m hm]

theorem iterate_bot_stabilize {L : Type u} [SemilatticeSup L] [OrderBot L]
    [Finite L]
    (f : L →o L) (n : ℕ) (hn : Nat.card L ≤ n) :
    Function.IsFixedPt f (f^[n] ⊥) := by
  have : WellFoundedGT L := Finite.to_wellFoundedGT
  by_contra hnfp
  have incr : ∀ i, f^[i] ⊥ ≤ f^[i + 1] ⊥ :=
    fun i => Monotone.iterate f.monotone i bot_le
  have hne : ∀ i, i ≤ n → f^[i] ⊥ ≠ f^[i + 1] ⊥ := by
    intro i hi heq
    have hfp : Function.IsFixedPt f (f^[i] ⊥) := by
      change f (f^[i] ⊥) = f^[i] ⊥
      have := (Function.iterate_succ_apply' (⇑f) i ⊥).symm
      rw [this]; exact heq.symm
    exact hnfp (iterate_bot_isFixedPt f hfp n hi)
  have hlt : ∀ i, i ≤ n → f^[i] ⊥ < f^[i + 1] ⊥ :=
    fun i hi => lt_of_le_of_ne (incr i) (hne i hi)
  have hsmono : StrictMono (fun i : Fin (Nat.card L + 1) => f^[i.val] ⊥) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Fin.lt_def] at hab
    suffices ∀ (a b : ℕ), a < b → b < Nat.card L + 1 → f^[a] ⊥ < f^[b] ⊥ from
      this a b hab hb
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hab'
      · exact hlt a (by omega)
      · exact lt_trans (ih hab' (by omega)) (hlt b (by omega))
  have hinj := hsmono.injective
  have : Nat.card L + 1 ≤ Nat.card L := by
    rw [← Nat.card_fin (Nat.card L + 1)]
    exact Nat.card_le_card_of_injective _ hinj
  omega

theorem iterate_bot_le_fixedPt {L : Type u} [SemilatticeSup L] [OrderBot L]
    (f : L →o L) (x : L) (hx : Function.IsFixedPt f x) (n : ℕ) :
    f^[n] ⊥ ≤ x := by
  have : ∀ m, f^[m] ⊥ ≤ f^[m] x :=
    fun m => Monotone.iterate f.monotone m bot_le
  have hxconst : ∀ m, f^[m] x = x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      exact hx
  simp only [hxconst] at this
  exact this n
