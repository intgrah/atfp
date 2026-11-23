module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Limits.Final
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
    simp [map_comp _ i j (j + 1) hij (Nat.le_succ j), map_le_succ, ih]

private theorem predSucc : GaloisConnection Nat.pred Nat.succ :=
  fun _ _ => Nat.pred_le_iff

private def succFunctor : ℕ ⥤ ℕ := predSucc.monotone_u.functor

private instance : succFunctor.Final :=
  Functor.final_of_adjunction predSucc.adjunction

private def chain.tailIso (F : 𝓒 ⥤ 𝓒) : chain F ⋙ F ≅ succFunctor ⋙ chain F :=
  NatIso.ofComponents (fun i => Iso.refl ((chain F).obj (i + 1))) (by
    intro i j f
    exact (Category.comp_id (F.map ((chain F).map f))).trans
      ((chain.map_succ (F := F) f.le).symm.trans
        (Category.id_comp ((chain F).map (homOfLE (Nat.succ_le_succ f.le)))).symm))

variable [PreservesColimitsOfShape ℕ F] [HasColimitsOfShape ℕ 𝓒]

abbrev μ (F : 𝓒 ⥤ 𝓒) := colimit (chain F)

private def μTail (F : 𝓒 ⥤ 𝓒) : Cocone (chain F ⋙ F) :=
  (Cocone.precompose (chain.tailIso F).hom).obj ((colimit.cocone (chain F)).whisker succFunctor)

private def μTailIsColimit (F : 𝓒 ⥤ 𝓒) : IsColimit (μTail F) :=
  (IsColimit.precomposeHomEquiv (chain.tailIso F) _).symm
    ((Functor.Final.isColimitWhiskerEquiv succFunctor _).symm (colimit.isColimit (chain F)))

variable (F)

@[no_expose]
def μ_iso : μ F ≅ F.obj (μ F) :=
  (μTailIsColimit F).coconePointUniqueUpToIso (isColimitOfPreserves F (colimit.isColimit (chain F)))

abbrev μAlgebra : Algebra F :=
  ⟨μ F, (μ_iso F).inv⟩

variable {F}

@[reassoc]
lemma μAlgebra_ι_succ (i : ℕ) :
    F.map (colimit.ι (chain F) i) ≫ (μAlgebra F).str = colimit.ι (chain F) (i + 1) := by
  exact (IsColimit.comp_coconePointUniqueUpToIso_inv
    (μTailIsColimit F) (isColimitOfPreserves F (colimit.isColimit (chain F))) i).trans
    (Category.id_comp _)

private def chain.algebraLeg (A : Algebra F) : ∀ n, obj F n ⟶ A.a
  | 0 => initial.to A.a
  | n + 1 => F.map (algebraLeg A n) ≫ A.str

private abbrev chain.algebraCocone (A : Algebra F) : Cocone (chain F) :=
  ⟨A.a, NatTrans.ofSequence (algebraLeg A) (by
    intro n
    change (Functor.ofSequence (chain.step F)).map (homOfLE (Nat.le_add_right n 1)) ≫
      algebraLeg A (n + 1) = algebraLeg A n ≫ 𝟙 A.a
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    induction n with
    | zero => exact initial.hom_ext _ _
    | succ n ih =>
      change F.map (chain.step F n) ≫ F.map (algebraLeg A (n + 1)) ≫ A.str =
        F.map (algebraLeg A n) ≫ A.str
      rw [← F.map_comp_assoc, ih])⟩

private def μFold (A : Algebra F) : μAlgebra F ⟶ A where
  f := colimit.desc (chain F) (chain.algebraCocone A)
  h := by
    apply (isColimitOfPreserves F (colimit.isColimit (chain F))).hom_ext
    intro i
    let d : μ F ⟶ A.a := colimit.desc (chain F) (chain.algebraCocone A)
    change F.map (colimit.ι (chain F) i) ≫ F.map d ≫ A.str =
      F.map (colimit.ι (chain F) i) ≫ (μAlgebra F).str ≫ d
    rw [← F.map_comp_assoc, colimit.ι_desc, μAlgebra_ι_succ_assoc]
    exact (colimit.ι_desc (chain.algebraCocone A) (i + 1)).symm

variable (F) in
@[no_expose]
def μ_isInitial : IsInitial (μAlgebra F) :=
  IsInitial.ofUniqueHom μFold (by
    intro A f
    apply Algebra.Hom.ext
    apply colimit.hom_ext
    intro n
    change colimit.ι (chain F) n ≫ f.f =
      colimit.ι (chain F) n ≫ colimit.desc (chain F) (chain.algebraCocone A)
    rw [colimit.ι_desc]
    induction n with
    | zero => exact initial.hom_ext _ _
    | succ n ih =>
      exact (congrArg (· ≫ f.f) (μAlgebra_ι_succ n).symm).trans (by
        change (F.map (colimit.ι (chain F) n) ≫ (μAlgebra F).str) ≫ f.f =
          F.map ((chain.algebraCocone A).ι.app n) ≫ A.str
        rw [Category.assoc, ← f.h, ← F.map_comp_assoc, ih]))

end Adámek

/-! Theorem 6.1.7 -/

#check Algebra.Initial.strInv
#check Algebra.Initial.str_isIso

end Section1
