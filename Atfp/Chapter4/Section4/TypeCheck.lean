module

public import Atfp.Chapter4.Section4.Datafun

namespace Datafun

deriving instance DecidableEq for FinTy
deriving instance DecidableEq for Ty

def Ty.asLatTy : Ty → Option LatTy
  | .unit => some .unit
  | .prod A B =>
    match A.asLatTy, B.asLatTy with
    | some L₁, some L₂ => some (.prod L₁ L₂)
    | _, _ => none
  | .powerset T => some (.powerset T)
  | .arr _ _ => none
  | .coprod _ _ => none
  | .discrete _ => none

theorem Ty.asLatTy_sound {A : Ty} {L : LatTy} (h : A.asLatTy = some L) : L.toTy = A := by
  induction A generalizing L with
  | unit => simp [asLatTy] at h; subst h; rfl
  | prod A B ihA ihB =>
    simp only [asLatTy] at h
    split at h <;> simp at h
    rename_i L₁ L₂ h₁ h₂
    subst h
    simp [LatTy.toTy, ihA h₁, ihB h₂]
  | powerset T => simp [asLatTy] at h; subst h; rfl
  | arr _ _ => simp [asLatTy] at h
  | coprod _ _ => simp [asLatTy] at h
  | discrete _ => simp [asLatTy] at h

def Ty.asFinTy : Ty → Option FinTy
  | .unit => some .unit
  | .prod A B =>
    match A.asFinTy, B.asFinTy with
    | some T₁, some T₂ => some (.prod T₁ T₂)
    | _, _ => none
  | .coprod A B =>
    match A.asFinTy, B.asFinTy with
    | some T₁, some T₂ => some (.coprod T₁ T₂)
    | _, _ => none
  | .powerset T => some (.powerset T)
  | .discrete A =>
    match A.asFinTy with
    | some T => some (.discrete T)
    | none => none
  | .arr _ _ => none

theorem Ty.asFinTy_sound {A : Ty} {T : FinTy} (h : A.asFinTy = some T) : T.toTy = A := by
  induction A generalizing T with
  | unit => simp [asFinTy] at h; subst h; rfl
  | prod A B ihA ihB =>
    simp only [asFinTy] at h
    split at h <;> simp at h
    rename_i T₁ T₂ h₁ h₂
    subst h
    simp [FinTy.toTy, ihA h₁, ihB h₂]
  | coprod A B ihA ihB =>
    simp only [asFinTy] at h
    split at h <;> simp at h
    rename_i T₁ T₂ h₁ h₂
    subst h
    simp [FinTy.toTy, ihA h₁, ihB h₂]
  | powerset T => simp [asFinTy] at h; subst h; rfl
  | discrete A ih =>
    simp only [asFinTy] at h
    split at h <;> simp at h
    rename_i T' h'
    subst h
    simp [FinTy.toTy, ih h']
  | arr _ _ => simp [asFinTy] at h

public def typeCheck (Γ : Ctx) : (e : Tm) → Option (Σ A : Ty, Γ ⊢ e : A)
  | .var x =>
    match h : Γ[x]? with
    | some (.none, A) => some ⟨A, .var x A h⟩
    | some (.D, A) => some ⟨A, .dvar x A h⟩
    | none => none
  | .unit => some ⟨1, .unit_intro⟩
  | .prod e₁ e₂ => do
    let ⟨A₁, h₁⟩ ← typeCheck Γ e₁
    let ⟨A₂, h₂⟩ ← typeCheck Γ e₂
    some ⟨.prod A₁ A₂, .prod_intro e₁ e₂ A₁ A₂ h₁ h₂⟩
  | .fst e => do
    let ⟨A, h⟩ ← typeCheck Γ e
    match A, h with
    | .prod A₁ A₂, h => some ⟨A₁, .prod_elim₁ e A₁ A₂ h⟩
    | _, _ => none
  | .snd e => do
    let ⟨A, h⟩ ← typeCheck Γ e
    match A, h with
    | .prod A₁ A₂, h => some ⟨A₂, .prod_elim₂ e A₁ A₂ h⟩
    | _, _ => none
  | .abs A e => do
    let ⟨B, h⟩ ← typeCheck ((.none, A) :: Γ) e
    some ⟨.arr A B, .abs_intro e A B h⟩
  | .app e₁ e₂ => do
    let ⟨A₁, h₁⟩ ← typeCheck Γ e₁
    match A₁, h₁ with
    | .arr A B, h₁ => do
      let ⟨A₂, h₂⟩ ← typeCheck Γ e₂
      if heq : A = A₂ then
        some ⟨B, .abs_elim e₁ e₂ A B h₁ (heq ▸ h₂)⟩
      else none
    | _, _ => none
  | .inl _ => none
  | .inr _ => none
  | .case e e₁ e₂ => do
    let ⟨A, h⟩ ← typeCheck Γ e
    match A, h with
    | .coprod A₁ A₂, h => do
      let ⟨C₁, h₁⟩ ← typeCheck ((.none, A₁) :: Γ) e₁
      let ⟨C₂, h₂⟩ ← typeCheck ((.none, A₂) :: Γ) e₂
      if heq : C₁ = C₂ then
        some ⟨C₁, .coprod_elim e e₁ e₂ A₁ A₂ C₁ h h₁ (heq ▸ h₂)⟩
      else none
    | _, _ => none
  | .bot L => some ⟨L.toTy, .bot_intro L⟩
  | .sup L e₁ e₂ => do
    let ⟨A₁, h₁⟩ ← typeCheck Γ e₁
    let ⟨A₂, h₂⟩ ← typeCheck Γ e₂
    if hA : A₁ = L.toTy then
      if hB : A₂ = L.toTy then
        some ⟨L.toTy, .sup_intro e₁ e₂ L (hA ▸ h₁) (hB ▸ h₂)⟩
      else none
    else none
  | .for e₁ e₂ => do
    let ⟨A₁, h₁⟩ ← typeCheck Γ e₁
    match A₁, h₁ with
    | .powerset T, h₁ => do
      let ⟨A₂, h₂⟩ ← typeCheck ((.D, T.toTy) :: Γ) e₂
      match hL : A₂.asLatTy with
      | some L =>
        some ⟨L.toTy, .for_intro e₁ e₂ T L h₁ (Ty.asLatTy_sound hL ▸ h₂)⟩
      | none => none
    | _, _ => none
  | .one e => do
    let ⟨A, h⟩ ← typeCheck [Γ]ᵈ e
    match hT : A.asFinTy with
    | some T =>
      some ⟨.powerset T, .one_intro e T (Ty.asFinTy_sound hT ▸ h)⟩
    | none => none
  | .disc e => do
    let ⟨A, h⟩ ← typeCheck [Γ]ᵈ e
    some ⟨.discrete A, .disc_intro e A h⟩
  | .let e₁ e₂ => do
    let ⟨A₁, h₁⟩ ← typeCheck Γ e₁
    match A₁, h₁ with
    | .discrete A, h₁ => do
      let ⟨C, h₂⟩ ← typeCheck ((.D, A) :: Γ) e₂
      some ⟨C, .disc_elim e₁ e₂ A C h₁ h₂⟩
    | _, _ => none
  | .fix L e => do
    let ⟨A, h⟩ ← typeCheck ((.none, L.toTy) :: [Γ]ᵈ) e
    if hA : A = L.toTy then
      some ⟨L.toTy, .fix_intro e L (hA ▸ h)⟩
    else none

end Datafun
