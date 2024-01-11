import ManySortedMatchingLogic.Proof

variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

open Pattern

section Propositional

  variable {Γ : Set <| Pattern sgn}
  variable
    {φ ψ χ θ : Pattern sgn}
    {s : S}
    (wsφ : WellSorted φ s := by simp_all)
    (wsψ : WellSorted ψ s := by simp_all)
    (wsχ : WellSorted χ s := by simp_all)
    (wsθ : WellSorted θ s := by simp_all)

  namespace Proof

    def weakeningDisj
      : Γ ⊢ φ ⇒ φ ⋁ ψ := tautology (s := s)
      (by
        intros M _ f _ m
        simp_rw [Morphism.morphism_impl, Morphism.morphism_disj]
        exact .inl
      )
      (by simp_all)

    def weakeningConj
      : Γ ⊢ φ ⋀ ψ ⇒ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_conj]
      exact And.left
      )
      (by simp_all)

    def contractionDisj
      : Γ ⊢ φ ⋁ φ ⇒ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_disj]
      intros h
      exact Or.elim h id id
      )
      (by simp_all)

    def contractionConj
      : Γ ⊢ φ ⇒ φ ⋀ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_conj]
      intros h
      exact .intro h h
      )
      (by simp_all)

    def permutationDisj
      : Γ ⊢ φ ⋁ ψ ⇒ ψ ⋁ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_disj]
      exact Or.comm.1
      )
      (by simp_all)

    def permutationConj
      : Γ ⊢ φ ⋀ ψ ⇒ ψ ⋀ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_conj]
      exact And.comm.1
      )
      (by simp_all)

    def exFalso
      : Γ ⊢ ⊥ ⇒ φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_impl, Morphism.morphism_false]
      exact False.elim
      )
      (by simp_all)

    def excluddedMiddle
      : Γ ⊢ φ ⋁ ∼φ := tautology (s := s)
      ( by
      intros M _ f _ m
      simp_rw [Morphism.morphism_disj, Morphism.morphism_neg]
      exact Classical.em _
      )
      (by simp_all)

    /--
      The same as `modusPonens`, but with the premises in a different order.
    -/
    def toRule (prf : Γ ⊢ φ ⇒ ψ) : Γ ⊢ φ → Γ ⊢ ψ :=
      fun prf' => modusPonens prf' prf

    /--
      `toRule` applied twice. Turns an implication with two hypotheses into a rule with two premises.
    -/
    def toRule2 (prf : Γ ⊢ φ ⇒ ψ ⇒ χ) : Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ χ :=
      fun prf' prf'' => toRule (toRule prf prf') prf''

    def syllogism : Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ ⇒ χ → Γ ⊢ φ ⇒ χ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto ) (by simp_all)
      toRule2 thm

    def importation : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⋀ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⋀ ψ ⇒ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)
      toRule thm

    def exportation : Γ ⊢ φ ⋀ ψ ⇒ χ → Γ ⊢ φ ⇒ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⋀ ψ ⇒ χ) ⇒ (φ ⇒ ψ ⇒ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)
      toRule thm

    def expansion : Γ ⊢ φ ⇒ ψ → Γ ⊢ χ ⋁ φ ⇒ χ ⋁ ψ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (χ ⋁ φ ⇒ χ ⋁ ψ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)
      toRule thm

    def disjIntroLeft
      : Γ ⊢ φ ⇒ φ ⋁ ψ :=
      weakeningDisj (s := s)

    def disjIntroRight
      : Γ ⊢ φ ⇒ ψ ⋁ φ :=
      (syllogism (s := s)) (disjIntroLeft (s := s)) (permutationDisj (s := s))

    def disjImpl
      : Γ ⊢ (φ ⇒ ψ) ⋁ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋁ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def disjImpl2
      : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋁ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ ⇒ χ ⋁ θ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def disjIntroAtHyp
      : Γ ⊢ φ ⇒ χ → Γ ⊢ ψ ⇒ χ → Γ ⊢ φ ⋁ ψ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ χ =>
      let l₂ : Γ ⊢ χ ⋁ φ ⇒ χ ⋁ χ := (expansion (s := s)) l₁
      let l₃ : Γ ⊢ χ ⋁ χ ⇒ χ := contractionDisj (s := s)
      fun l₄ : Γ ⊢ ψ ⇒ χ =>
      let l₅ : Γ ⊢ φ ⋁ χ ⇒ χ ⋁ φ := permutationDisj (s := s)
      let l₆ : Γ ⊢ χ ⋁ φ ⇒ χ := (syllogism (s := s)) l₂ l₃
      let l₇ : Γ ⊢ φ ⋁ ψ ⇒ φ ⋁ χ := (expansion (s := s)) l₄
      let l₈ : Γ ⊢ φ ⋁ χ ⇒ χ := (syllogism (s := s)) l₅ l₆
      (syllogism (s := s)) l₇ l₈

    def conjElimLeft
      : Γ ⊢ φ ⋀ ψ ⇒ φ := weakeningConj (s := s)

    def conjElimRight
      : Γ ⊢ φ ⋀ ψ ⇒ ψ := (syllogism (s := s)) (permutationConj (s := s)) (conjElimLeft (s := s))

    def conjIntro
      : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def implProjLeft
      : Γ ⊢ φ ⇒ (ψ ⇒ φ) :=
      (exportation (s := s)) (weakeningConj (s := s))

    def implProjRight
      : Γ ⊢ φ ⇒ ψ ⇒ ψ :=
      (exportation (s := s)) (conjElimRight (s := s))

    def implSelf
      : Γ ⊢ φ ⇒ φ :=
      (syllogism (s := s)) (contractionConj (s := s)) (weakeningConj (s := s))

    def extraPremise
      : Γ ⊢ φ → Γ ⊢ ψ ⇒ φ := fun p =>
      modusPonens p (implProjLeft (s := s))

    def conjIntroRule
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ χ → Γ ⊢ φ ⇒ ψ ⋀ χ :=
      let l₁ : Γ ⊢ ψ ⋀ χ ⇒ ψ ⋀ χ := implSelf (s := s)
      let l₂ : Γ ⊢ ψ ⇒ χ ⇒ ψ ⋀ χ := (exportation (s := s)) l₁
      fun l₃ : Γ ⊢ φ ⇒ ψ =>
      let l₄ : Γ ⊢ φ ⇒ χ ⇒ ψ ⋀ χ := (syllogism (s := s)) l₃ l₂
      let l₅ : Γ ⊢ χ ⋀ φ ⇒ φ ⋀ χ := permutationConj (s := s)
      let l₆ : Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ := (importation (s := s)) l₄
      let l₇ : Γ ⊢ χ ⋀ φ ⇒ ψ ⋀ χ := (syllogism (s := s)) l₅ l₆
      fun l₈ : Γ ⊢ φ ⇒ χ =>
      let l₉ : Γ ⊢ χ ⇒ (φ ⇒ ψ ⋀ χ) := (exportation (s := s)) l₇
      let l₁₀ : Γ ⊢ φ ⇒ φ ⇒ ψ ⋀ χ := (syllogism (s := s)) l₈ l₉
      let l₁₁ : Γ ⊢ φ ⋀ φ ⇒ ψ ⋀ χ := (importation (s := s)) l₁₀
      (syllogism (s := s)) (contractionConj (s := s)) l₁₁

    def conjIntroHypConcLeft
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ φ ⋀ χ ⇒ χ := conjElimRight (s := s)
      let l₃ : Γ ⊢ φ ⋀ χ ⇒ ψ := (syllogism (s := s)) (conjElimLeft (s := s)) l₁
      (conjIntroRule (s := s)) l₃ l₂


    def modusPonensExtraHyp : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ :=
      fun l₁ l₂ => (syllogism (s := s)) ((conjIntroRule (s := s)) (implSelf (s := s)) l₁) ((importation (s := s)) l₂)

    -- bad name
    def modusPonensThm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ) ⋀ φ ⇒ χ :=
      let ψ' := (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ)
      let φ' := ψ' ⋀ φ
      let l₁ : Γ ⊢ φ' ⇒ ψ' := (conjElimLeft (s := s))
      let l₂ : Γ ⊢ ψ' ⇒ φ ⇒ ψ := conjElimRight (s := s)
      let l₃ : Γ ⊢ φ' ⇒ φ := conjElimRight (s := s)
      let l₄ : Γ ⊢ φ' ⇒ φ ⇒ ψ := (syllogism (s := s)) l₁ l₂
      let l₅ : Γ ⊢ φ' ⇒ ψ := (modusPonensExtraHyp (s := s)) l₃ l₄
      let l₆ : Γ ⊢ ψ' ⇒ φ ⇒ ψ ⇒ χ := conjElimLeft (s := s)
      let l₇ : Γ ⊢ φ' ⇒ φ ⇒ ψ ⇒ χ := (syllogism (s := s)) l₁ l₆
      let l₈ : Γ ⊢ φ' ⇒ ψ ⇒ χ := (modusPonensExtraHyp (s := s)) l₃ l₇
      let l₉ : Γ ⊢ φ' ⇒ χ := (modusPonensExtraHyp (s := s)) l₅ l₈
      l₉

    def implDistribLeft : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ χ) :=
      (exportation (s := s)) <| (exportation (s := s)) (modusPonensThm (s := s))

    def implDistribRight : Γ ⊢ ((φ ⇒ ψ) ⇒ (φ ⇒ χ)) ⇒ (φ ⇒ ψ ⇒ χ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def syllogismExtraHyp : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ ⇒ θ → Γ ⊢ φ ⇒ ψ ⇒ θ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) := (toRule) (implDistribLeft (s := s)) l₁
      fun l₃ : Γ ⊢ φ ⇒ χ ⇒ θ =>
      let l₄ : Γ ⊢ (φ ⇒ χ) ⇒ (φ ⇒ θ) := (toRule) (implDistribLeft (s := s)) l₃
      let l₅ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ θ) := (syllogism (s := s)) l₂ l₄
      let l₆ : Γ ⊢ φ ⇒ ψ ⇒ θ := (toRule) (implDistribRight (s := s)) l₅
      l₆

    def permuteHyps : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ ψ ⇒ φ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ χ := (importation (s := s)) l₁
      let l₃ : Γ ⊢ ψ ⋀ φ ⇒ χ := (syllogism (s := s)) (permutationConj (s := s)) l₂
      (exportation (s := s)) l₃


    def disjIntroAtHypThm : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ (φ ⋁ ψ ⇒ χ) :=
      let l₁ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ φ ⇒ χ := (conjElimLeft (s := s))
      let l₂ : Γ ⊢ φ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps (s := s)) l₁
      let l₃ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ ψ ⇒ χ := conjElimRight (s := s)
      let l₄ : Γ ⊢ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps (s := s)) l₃
      let l₅ : Γ ⊢ φ ⋁ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (disjIntroAtHyp (s := s)) l₂ l₄
      (permuteHyps (s := s)) l₅

    def conjIntroAtConclThm : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) :=
      let l₁ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ φ := conjElimRight (s := s)
      let l₂ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ ψ) := (syllogism (s := s)) (conjElimLeft (s := s)) (conjElimLeft (s := s))
      let l₃ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ := (modusPonensExtraHyp (s := s)) l₁ l₂
      let l₄ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ χ) := (syllogism (s := s)) (conjElimLeft (s := s)) (conjElimRight (s := s))
      let l₅ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ χ := (modusPonensExtraHyp (s := s)) l₁ l₄
      let l₆ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ ⋀ χ := (conjIntroRule (s := s)) l₃ l₅
      (exportation (s := s)) <| (exportation (s := s)) l₆


    def negImplIntro : Γ ⊢ φ ⇒ ψ → Γ ⊢ ∼ψ ⇒ ∼φ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (∼ψ ⇒ ∼φ) := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)
      (toRule) thm

    def negConjAsImpl : Γ ⊢ ∼(φ ⋀ ψ) ⇒ φ ⇒ ∼ψ := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)



    def doubleNegIntro : Γ ⊢ φ ⇒ ∼∼φ := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def doubleNegElim : Γ ⊢ ∼∼φ ⇒ φ := tautology (s := s) (by intros _ _ _ _ _; simp?; tauto) (by simp_all)

    def topImplSelfImplSelf : Γ ⊢ (⊤ ⇒ φ) ⇒ φ := tautology (s := s) (by intros _ _ _ _ _; simp?) (by simp_all)


  end Proof
end Propositional
