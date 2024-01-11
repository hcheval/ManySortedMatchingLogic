
import ManySortedMatchingLogic.PropositionalProofs

variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

open Pattern

namespace Proof

  section FirstOrder
    namespace Proof
    variable {Γ : Set <| Pattern sgn}
    variable {φ ψ χ θ : Pattern sgn} {x y : EVar S}
      {s : S}
      (wsφ : WellSorted φ s := by simp_all)
      (wsψ : WellSorted ψ s := by simp_all)
      (wsχ : WellSorted χ s := by simp_all)
      (wsθ : WellSorted θ s := by simp_all)

    attribute [simp] universal

    def implExistSelf : Γ ⊢ φ ⇒ ∃∃ x φ :=
      let l₁ : Γ ⊢ φ[x ⇐ᵉ x] ⇒ ∃∃ x φ := existQuan (wsφ := wsφ) <| substitutable_evar_same _ _
      by rw [Pattern.subst_var_var_eq_self_evar] at l₁ ; exact l₁

    def existSelfImpl (not_fv : ¬φ.FreeEVar x) : Γ ⊢ ∃∃ x φ ⇒ φ :=
      let l₁ : Γ ⊢ φ ⇒ φ := (implSelf (s := s))
      existGen not_fv l₁

    def pushExistInConj (not_fv : ¬ψ.FreeEVar x) : Γ ⊢ ∃∃ x (φ ⋀ ψ) ⇒ ∃∃ x φ ⋀ ψ :=
      let l₁ : Γ ⊢ φ ⇒ ∃∃ x φ := implExistSelf (s := s)
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ x φ ⋀ ψ := (conjIntroHypConcLeft (s := s)) l₁
      existGen (by aesop?) l₂

    def univQuan (sfi : SubstitutableEVarForIn x y φ)
      : Γ ⊢ ∀∀ x φ ⇒ φ[x ⇐ᵉ y] :=
      let l₁ : Γ ⊢ ∀∀ x φ ⇒ ∼∼φ[x ⇐ᵉ y] := (negImplIntro (s := s)) <| existQuan (s := s) (φ := ∼φ) (by aesop?)
      (syllogism (s := s)) l₁ (doubleNegElim (s := s) (wsφ := by simp_all))

    def univGen (not_fv : ¬φ.FreeEVar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ∀∀ x ψ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ ∼ψ ⇒ ∼φ := (negImplIntro (s := s)) l₁
      let l₃ : Γ ⊢ ∃∃ x (∼ψ) ⇒ ∼φ := existGen (by aesop?) l₂
      let l₄ : Γ ⊢ ∼∼φ ⇒ ∼(∃∃ x (∼ψ)) := (negImplIntro (s := s)) l₃
      let l₅ : Γ ⊢ ∼∼φ ⇒ (∀∀ x ψ) := l₄
      (syllogism (s := s)) (doubleNegIntro (s := s)) l₅

    def univGeneralization : Γ ⊢ φ → Γ ⊢ ∀∀  x φ :=
      fun l₁ : Γ ⊢ φ =>
      let l₁ : Γ ⊢ ⊤ ⇒ φ := toRule (tautology (s := s) (by intros _ _ _ _ _; simp?;) (by simp_all)) l₁
      let l₂ : Γ ⊢ ⊤ ⇒ ∀∀ x φ := (univGen (s := s)) (by simp [*] at *) l₁
      toRule (topImplSelfImplSelf (s := s)) l₂

    def pushConjInExist (not_fv : ¬ψ.FreeEVar x) : Γ ⊢ ∃∃ x φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) :=
      let l₁ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (implExistSelf (s := s))
      let l₂ : Γ ⊢ φ ⇒ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (exportation (s := s)) l₁
      let l₃ : Γ ⊢ ∃∃ x φ ⇒ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (existGen) (by aesop?) l₂
      let l₄ : Γ ⊢  ∃∃ x φ ⋀ ψ ⇒ ∃∃ x (φ ⋀ ψ) := (importation (s := s)) l₃
      l₄

    end Proof
  end FirstOrder
