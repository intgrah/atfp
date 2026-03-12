module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open CategoryTheory Limits

section Section1

universe u

/-! Lemma 6.1.1 -/

#check colimit.desc_extend

/-! Definition 6.1.2 -/

#check PreservesColimitsOfShape ℕ

open Endofunctor (Algebra)

/-! Theorem 6.1.3 -/

noncomputable section Adámek

variable {𝓒 : Type u} [Category.{u} 𝓒] [HasInitial 𝓒] (F : 𝓒 ⥤ 𝓒)

def chain.obj : ℕ → 𝓒
  | 0 => ⊥_ 𝓒
  | i + 1 => F.obj (obj i)

def chain.step : ∀ n, (obj F n ⟶ obj F (n + 1))
  | 0 => initial.to (F.obj (⊥_ 𝓒))
  | i + 1 => F.map (step i)

def chain : ℕ ⥤ 𝓒 := Functor.ofSequence (chain.step F)

variable {F : 𝓒 ⥤ 𝓒}

open Functor.OfSequence (map map_id map_comp map_le_succ) in
lemma chain.map_succ {i j : ℕ} (h : i ≤ j) :
    (chain F).map ⟨⟨Nat.succ_le_succ h⟩⟩ = F.map ((chain F).map ⟨⟨h⟩⟩) := by
  let g := step F
  change map (fun n => F.map (g n)) i j h = F.map (map g i j h)
  induction j, h using Nat.le_induction with
  | base => simp [map_id]
  | succ j hij ih =>
    calc map (fun n => F.map (g n)) i (j + 1) _
      _ = map (fun n => F.map (g n)) i j hij ≫ map (fun n => F.map (g n)) j (j + 1) _ :=
          map_comp _ i j _ hij _
      _ = map (fun n => F.map (g n)) i j hij ≫ F.map (g j) := by rw [map_le_succ]
      _ = F.map (map g i j hij) ≫ F.map (g j) := by rw [ih]
      _ = F.map (map g i j hij ≫ g j) := (F.map_comp _ _).symm
      _ = F.map (map g i j hij ≫ map g j (j + 1) (Nat.le_succ j)) := by rw [map_le_succ]
      _ = F.map (map g i (j + 1) _) := by rw [← map_comp]

variable [PreservesColimitsOfShape ℕ F] [HasColimitsOfShape ℕ 𝓒]

-- Write μ F for the ω-colimit of this diagram
def μ (F : 𝓒 ⥤ 𝓒) := colimit (chain F)

-- TODO break down into smaller definitions and lemmas
set_option backward.isDefEq.respectTransparency false in
def μ_iso : True := by
  let D : ℕ ⥤ 𝓒 := chain F
  let ccμF : Cocone D := colimit.cocone D
  have hccμF : IsColimit ccμF := colimit.isColimit D
  -- and ι i : D.obj i ⟶ μ F for the injections.
  let ι i : D.obj i ⟶ μ F := colimit.ι D i
  -- Now, we show that μ F ≅ F.obj (μ F).
  -- Next, we consider the diagram obtained by applying `F` to this diagram:
  let FD := D ⋙ F
  -- Since `F` preserves colimits, this means that `⟨F.obj (μ F), fun i => F.map (ι i)⟩`
  let ccFμF : Cocone FD := F.mapCocone ccμF
  -- is the ω-colimit of this diagram.
  let hccFμF : IsColimit ccFμF := isColimitOfPreserves F hccμF
  -- Next, construct the cocone `⟨μF, fun i => ι (i+1)⟩` over the second diagram.
  -- The universal property of `F.obj (μ F)` gives us a map
  let in' : F.obj (μ F) ⟶ μ F := hccFμF.desc ⟨μ F, fun i => ι (i + 1), ?naturality⟩
  case naturality =>
    intro i j f
    calc F.map (D.map f) ≫ ι (j + 1)
      _ = F.map (D.map ⟨⟨f.le⟩⟩) ≫ ι (j + 1) := rfl
      _ = D.map ⟨⟨Nat.succ_le_succ f.le⟩⟩ ≫ ι (j + 1) := by rw [chain.map_succ]
      _ = D.map ⟨⟨Nat.succ_le_succ f.le⟩⟩ ≫ ccμF.ι.app (j + 1) := rfl
      _ = ccμF.ι.app (i + 1) := ccμF.w _
      _ = ι (i + 1) := rfl
      _ = ι (i + 1) ≫ 𝟙 (μ F) := (Category.comp_id _).symm
  -- such that
  have hin : ∀ i, F.map (ι i) ≫ in' = ι (i + 1) := hccFμF.fac _
  -- Next, construct the cocone
  let c : ∀ i, D.obj i ⟶ F.obj (μ F)
    | 0 => initial.to (F.obj (μ F))
    | i + 1 => F.map (ι i)
  let ccFμF' : Cocone D := ⟨F.obj (μ F), c, ?naturality⟩
  case naturality =>
    rintro (_ | i) (_ | j) f
    · apply initial.hom_ext
    · apply initial.hom_ext
    · exact absurd f.le (Nat.not_succ_le_zero _)
    · let h := Nat.le_of_succ_le_succ f.le
      calc D.map f ≫ F.map (ι j)
        _ = D.map ⟨⟨f.le⟩⟩ ≫ F.map (ι j) := rfl
        _ = F.map (D.map ⟨⟨h⟩⟩) ≫ F.map (ι j) := by rw [chain.map_succ h]
        _ = F.map (D.map ⟨⟨h⟩⟩ ≫ ι j) := F.map_comp _ _ |>.symm
        _ = F.map (D.map ⟨⟨h⟩⟩ ≫ ccμF.ι.app j) := rfl
        _ = F.map (ccμF.ι.app i) := congrArg F.map (ccμF.w _)
        _ = F.map (ι i) := rfl
        _ = F.map (ι i) ≫ 𝟙 (F.obj (μ F)) := (Category.comp_id _).symm
  -- By the universal property of `μF`, we have a map
  let out : μ F ⟶ F.obj (μ F) := hccμF.desc ccFμF'
  -- with the property that
  have hout : ∀ i, ι i ≫ out = c i := hccμF.fac ccFμF'
  -- Unrolling the definition of `c i`, we get that
  have hout' {i} : ι (i + 1) ≫ out = F.map (ι i) := hout (i + 1)
  -- Putting the two together, we get the equations
  have h₁ {k} : ι (k + 1) ≫ out ≫ in' = ι (k + 1) :=
    calc ι (k + 1) ≫ out ≫ in'
      _ = (ι (k + 1) ≫ out) ≫ in' := Category.assoc _ _ _ |>.symm
      _ = F.map (ι k) ≫ in' := congrArg (· ≫ in') hout'
      _ = ι (k + 1) := hin k
  have h₂ {n} : F.map (ι n) ≫ in' ≫ out = F.map (ι n) :=
    calc F.map (ι n) ≫ in' ≫ out
      _ = (F.map (ι n) ≫ in') ≫ out := Category.assoc _ _ _ |>.symm
      _ = (ι (n + 1)) ≫ out := congrArg (· ≫ out) (hin n)
      _ = F.map (ι n) := hout (n + 1)
  -- The universal property of ω-colimits lets us conclude that
  have h₃ : in' ≫ out = 𝟙 (F.obj (μ F)) := by
    apply hccFμF.hom_ext
    intro i
    calc F.map (ι i) ≫ in' ≫ out
      _ = F.map (ι i) := h₂
      _ = F.map (ι i) ≫ 𝟙 (F.obj (μ F)) := (Category.comp_id _).symm
  -- The universal property of ω-colimits plus initiality of `⊥_ 𝓒` lets us conclude that
  have h₄ : out ≫ in' = 𝟙 (μ F) := by
    apply hccμF.hom_ext
    intro
    | 0 =>
      calc ι 0 ≫ out ≫ in'
        _ = (ι 0 ≫ out) ≫ in' := (Category.assoc _ _ _).symm
        _ = c 0 ≫ in' := congrArg (· ≫ in') (hout 0)
        _ = ι 0 := initial.hom_ext _ _
        _ = ι 0 ≫ 𝟙 (μ F) := (Category.comp_id _).symm
    | k + 1 =>
      calc ι (k + 1) ≫ out ≫ in'
        _ = ι (k + 1) := h₁
        _ = ι (k + 1) ≫ 𝟙 (μ F) := (Category.comp_id _).symm
  -- Hence they form an isomorphism.
  have : μ F ≅ F.obj (μ F) := ⟨out, in', h₄, h₃⟩
  -- Now, we need to show that `⟨μ F, in'⟩` is an initial F-algebra.
  have h : IsInitial (C := Algebra F) ⟨μ F, in'⟩ := by
    apply IsInitial.ofUniqueHom ?existence ?uniqueness
    all_goals
      -- Suppose that `⟨A, α⟩` is an F-algebra.
      intro ⟨A, α⟩
      -- To establish initiality, we need to show that there is a
      -- unique algebra map `αFold : ⟨μ F, in'⟩ ⟶ ⟨A, α⟩`.
      -- We establish existence as follows:
      -- We now recursively define maps `f n : D.obj n ⟶ A` as follows.
      let f : ∀ n, D.obj n ⟶ A :=
        Nat.rec (initial.to A) (fun n fn => F.map fn ≫ α)
      -- We want to show that these maps make `A` into a cocone over the ω-colimit diagram.
      let ccA : Cocone D := ⟨A, f, ?ht⟩
      case ht =>
        intro x y ⟨⟨hxy⟩⟩
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        -- It suffices to show the following family of diagrams commute:
        suffices triangle : ∀ n, f n = chain.step F n ≫ f (n + 1) by
          induction y, hxy using Nat.le_induction with
          | base =>
            calc D.map (𝟙 x) ≫ f x
              _ = 𝟙 (D.obj x) ≫ f x := by rw [D.map_id]
              _ = f x := Category.id_comp (f x)
          | succ k hxk ih =>
            calc D.map ⟨⟨hxk.step⟩⟩ ≫ f (k + 1)
              _ = D.map (⟨⟨hxk⟩⟩ ≫ ⟨⟨k.le_succ⟩⟩) ≫ f (k + 1) := rfl
              _ = D.map ⟨⟨hxk⟩⟩ ≫ D.map ⟨⟨k.le_succ⟩⟩ ≫ f (k + 1) := by
                rw [D.map_comp, Category.assoc]
              _ = D.map ⟨⟨hxk⟩⟩ ≫ chain.step F k ≫ f (k + 1) := by
                rw [show D.map ⟨⟨k.le_succ⟩⟩ = chain.step F k from
                  Functor.ofSequence_map_homOfLE_succ _ k]
              _ = D.map ⟨⟨hxk⟩⟩ ≫ f k := by rw [triangle k]
              _ = f x := ih
        intro n
        show f n = chain.step F n ≫ f (n + 1)
        -- Using the definition of f (n + 1), this is equivalent to showing:
        change f n = chain.step F n ≫ F.map (f n) ≫ α
        induction n with
        | zero => exact initial.to_comp _ |>.symm
        | succ n ih =>
          calc f (n + 1)
            _ = F.map (f n) ≫ α := rfl
            _ = F.map (chain.step F n ≫ F.map (f n) ≫ α) ≫ α := by rw [← ih]
            _ = F.map (chain.step F n ≫ f (n + 1)) ≫ α := rfl
            _ = (F.map (chain.step F n) ≫ F.map (f (n + 1))) ≫ α := by rw [F.map_comp]
            _ = F.map (chain.step F n) ≫ F.map (f (n + 1)) ≫ α := Category.assoc _ _ _
            _ = chain.step F (n + 1) ≫ F.map (f (n + 1)) ≫ α := rfl
      let αFold : μ F ⟶ A := hccμF.desc ccA
    case existence =>
      have hαFold : ∀ j, ι j ≫ αFold = f j := hccμF.fac ccA
      -- To show that this map is an F-algebra homomorphism,
      change Algebra.Hom ⟨μ F, in'⟩ ⟨A, α⟩
      refine ⟨αFold, ?compat⟩
      -- We need to show that
      change F.map αFold ≫ α = in' ≫ αFold
      -- First, note that applying `F` to the `f i` yields a cocone over the second diagram
      let ccFA : Cocone FD := F.mapCocone ccA
      -- whose colimit is `F.obj (μ F)`.
      have : IsColimit (ccFμF : Cocone FD) := hccFμF
      have : ccFμF.pt = F.obj (μ F) := rfl
      -- Since `F` preserves ω-colimits,
      -- `F.map αFold : F.obj (μ F) ⟶ F.obj A` is the mediating morphism.
      have hdccFA : hccFμF.desc ccFA = F.map αFold :=
        preserves_desc_mapCocone F D ccμF ccA hccμF
      -- Therefore, the mediating morphism of the cocone
      let naturality i j g : FD.map g ≫ F.map (f j) ≫ α = (F.map (f i) ≫ α) ≫ 𝟙 A :=
        calc F.map (D.map g) ≫ (F.map (f j) ≫ α)
          _ = (F.map (D.map g) ≫ F.map (f j)) ≫ α := by rw [Category.assoc]
          _ = F.map (D.map g ≫ f j) ≫ α := by rw [F.map_comp]
          _ = F.map (f i) ≫ α := by rw [ccA.w]
          _ = (F.map (f i) ≫ α) ≫ 𝟙 A := Category.comp_id _ |>.symm
      let ccA' : Cocone FD := ⟨A, fun i => F.map (f i) ≫ α, naturality⟩
      -- must equal `F.map αFold ≫ α`.
      have hdccA' : hccFμF.desc ccA' = F.map αFold ≫ α := by
        rw [← hdccFA]
        apply hccFμF.hom_ext
        intro
        rw [hccFμF.fac, IsColimit.fac_assoc]
        rfl
      -- Observe that the cocone `ccA'` is equal to
      let ccA'' : Cocone FD := ⟨A, fun i => f (i + 1), naturality⟩
      have : ccA' = ccA'' := rfl
      -- Thus we can extend it to a cocone over the original diagram.
      have hext : ∀ i, ccA.ι.app (i + 1) = ccA''.ι.app i := fun i => rfl
      -- Therefore
      have : hccFμF.desc ccA'' = in' ≫ αFold := by
        apply hccFμF.hom_ext
        intro i
        calc F.map (ι i) ≫ hccFμF.desc ccA''
          _ = ccA''.ι.app i := hccFμF.fac ccA'' i
          _ = f (i + 1) := rfl
          _ = ι (i + 1) ≫ αFold := (hαFold (i + 1)).symm
          _ = (F.map (ι i) ≫ in') ≫ αFold := by rw [← hin i]
          _ = F.map (ι i) ≫ in' ≫ αFold := Category.assoc _ _ _
      change F.map αFold ≫ α = in' ≫ αFold
      rw [← hdccA', ← this]
    -- Now, we need to establish uniqueness.
    case uniqueness =>
      -- Suppose there is another `h : μ F ⟶ A` such that `F.map h ≫ α = in' ≫ h`.
      intro ⟨h, hh⟩
      -- Observe that this means
      have h₅ : h = out ≫ F.map h ≫ α := by
        rw [hh, ← Category.assoc, h₄, Category.id_comp]
      -- Now define
      let h_ n : D.obj n ⟶ A := ι n ≫ h
      -- We can show by induction that `h n = f n`.
      have h_f {n} : h_ n = f n := by
        induction n with
        | zero =>
          -- Observe that
          calc h_ 0
            _ = ι 0 ≫ h := rfl
            _ = initial.to (μ F) ≫ h := congrArg (· ≫ h) (initial.hom_ext _ _)
            _ = initial.to A := initial.to_comp h
            _ = f 0 := rfl
        | succ k ih =>
          show h_ (k + 1) = f (k + 1)
          calc h_ (k + 1)
            _ = ι (k + 1) ≫ h := rfl
            _ = ι (k + 1) ≫ out ≫ F.map h ≫ α := by rw [← h₅]
            _ = F.map (ι k) ≫ F.map h ≫ α := by rw [← Category.assoc, hout']
            _ = F.map (ι k ≫ h) ≫ α := by rw [← Category.assoc, F.map_comp]
            _ = F.map (h_ k) ≫ α := rfl
            _ = F.map (f k) ≫ α := by rw [ih]
            _ = f (k + 1) := rfl
      ext
      -- Then the uniqueness of the mediating morphism means `h = αFold`.
      change h = αFold
      exact hccμF.uniq ccA h fun j => h_f
  exact trivial

end Adámek

/-! Theorem 6.1.7 -/

#check Algebra.Initial.strInv
#check Algebra.Initial.str_isIso

end Section1
