import ManySortedMatchingLogic.MixPattern

set_option autoImplicit false

open Classical

open Pattern

variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

abbrev Premises (sgn : Signature Symbol S) := Set <| Σ s : S, WSPattern sgn s

inductive Proof (Γ : Premises sgn) : {s : S} → WSPattern sgn s → Type _ where
| premise {φ} : ⟨_, φ⟩ ∈ Γ →
  Proof Γ φ
| modusPonens {φ ψ} :
  Proof Γ φ → Proof Γ (φ ⇒ ψ) → Proof Γ ψ
| existQuan {φ} {x} {y} : SubstitutableEVarForIn x y φ →
  Proof Γ ((φ.substEVar x y) ⇒ ∃∃ _ x φ)
| existGen {φ ψ} {x} : ¬FreeEVar x ψ →
  Proof Γ (φ ⇒ ψ) → Proof Γ ((∃∃ _ x φ) ⇒ ψ)
| propagationDisj {s t} {C : AppContext sgn s t} {φ ψ : Pattern sgn (.base s)} :
  Proof Γ (C.insert (φ ⋁ ψ) ⇒ C.insert φ ⋁ C.insert ψ)
| propagationExist {s t r} {C : AppContext sgn s t} {x : EVar} {φ : Pattern sgn (.base s)} :
  ¬FreeEVar x (C.insert (∃∃ r x φ)) →
  Proof Γ (C.insert (∃∃ r x φ) ⇒ ∃∃ r x (C.insert φ))
| framing {s t} {C : AppContext sgn s t} {φ ψ : Pattern sgn (.base s)} :
  Proof Γ (φ ⇒ ψ) → Proof Γ (C.insert φ ⇒ C.insert ψ)
| singleton {s t : 𝓢} {C₁ C₂ : NestedContext sgn s t} {x : EVar} {φ : Pattern sgn (.base s)} :
  Proof Γ <| ∼(C₁.insert (x ⋀ φ) ⋀ C₂.insert (x ⋀ ∼φ))
| existence {s t : 𝓢} {x} :
  Proof Γ (∃∃ (.base s) x (.evar (.base t) x))
| substitution {φ} {ψ} {X} : SubstitutableSVarForIn X ψ φ →
  Proof Γ φ → Proof Γ (φ.substSVar X ψ)
| prefixpoint {φ} {X} : ¬NegativeOcc X φ → SubstitutableSVarForIn X (μ X φ) φ →
  Proof Γ ((φ.substSVar X (μ X φ)) ⇒ μ X φ)
| knasterTarski {φ ψ} {X} : SubstitutableSVarForIn X ψ φ →
  Proof Γ ((φ.substSVar X ψ) ⇒ ψ) → Proof Γ (μ X φ ⇒ ψ)
-- | cast {s t : 𝓢} {φ : Pattern sgn s} {ψ : Pattern sgn t} : HEq φ ψ → Proof Γ φ → Proof Γ ψ

macro "arrow_precedence" : prec => `(prec| 24)
infix:(arrow_precedence + 1) " ⊢ " => Proof

/-- To be used for obvious propositional tautologies, until they are proved -/
macro "tautology" : term => `(term| sorry)

section Propositional

  variable {sgn : Signature 𝓢} {Γ : Premises sgn}
  variable {s : 𝓢} {φ ψ χ θ : Pattern sgn (.base s)}

  namespace Proof

    def weakeningDisj
      : Γ ⊢ φ ⇒ φ ⋁ ψ := tautology

    def weakeningConj
      : Γ ⊢ φ ⋀ ψ ⇒ φ := tautology

    def contractionDisj
      : Γ ⊢ φ ⋁ φ ⇒ φ := tautology

    def contractionConj
      : Γ ⊢ φ ⇒ φ ⋀ φ := tautology

    def permutationDisj
      : Γ ⊢ φ ⋁ ψ ⇒ ψ ⋁ φ := tautology

    def permutationConj
      : Γ ⊢ φ ⋀ ψ ⇒ ψ ⋀ φ := tautology

    def exFalso
      : Γ ⊢ ⊥ ⇒ φ := tautology

    def excluddedMiddle
      : Γ ⊢ φ ⋁ ∼φ := tautology


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
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := tautology
      toRule2 thm

    def importation : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⋀ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⋀ ψ ⇒ χ) := tautology
      toRule thm

    def exportation : Γ ⊢ φ ⋀ ψ ⇒ χ → Γ ⊢ φ ⇒ ψ ⇒ χ :=
      let thm : Γ ⊢ (φ ⋀ ψ ⇒ χ) ⇒ (φ ⇒ ψ ⇒ χ) := tautology
      toRule thm

    def expansion : Γ ⊢ φ ⇒ ψ → Γ ⊢ χ ⋁ φ ⇒ χ ⋁ ψ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (χ ⋁ φ ⇒ χ ⋁ ψ) := tautology
      toRule thm

    def disjIntroLeft
      : Γ ⊢ φ ⇒ φ ⋁ ψ :=
      weakeningDisj

    def disjIntroRight
      : Γ ⊢ φ ⇒ ψ ⋁ φ :=
      (syllogism) disjIntroLeft permutationDisj

    def disjImpl
      : Γ ⊢ (φ ⇒ ψ) ⋁ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋁ χ) := tautology

    def disjImpl2
      : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋁ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ ⇒ χ ⋁ θ) := tautology

    def disjIntroAtHyp
      : Γ ⊢ φ ⇒ χ → Γ ⊢ ψ ⇒ χ → Γ ⊢ φ ⋁ ψ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ χ =>
      let l₂ : Γ ⊢ χ ⋁ φ ⇒ χ ⋁ χ := (expansion) l₁
      let l₃ : Γ ⊢ χ ⋁ χ ⇒ χ := contractionDisj
      fun l₄ : Γ ⊢ ψ ⇒ χ =>
      let l₅ : Γ ⊢ φ ⋁ χ ⇒ χ ⋁ φ := permutationDisj
      let l₆ : Γ ⊢ χ ⋁ φ ⇒ χ := (syllogism) l₂ l₃
      let l₇ : Γ ⊢ φ ⋁ ψ ⇒ φ ⋁ χ := (expansion) l₄
      let l₈ : Γ ⊢ φ ⋁ χ ⇒ χ := (syllogism) l₅ l₆
      (syllogism) l₇ l₈

    def conjElimLeft
      : Γ ⊢ φ ⋀ ψ ⇒ φ := weakeningConj

    def conjElimRight
      : Γ ⊢ φ ⋀ ψ ⇒ ψ := (syllogism) permutationConj conjElimLeft

    def conjIntro
      : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) := tautology

    def implProjLeft
      : Γ ⊢ φ ⇒ (ψ ⇒ φ) :=
      (exportation) weakeningConj

    def implProjRight
      : Γ ⊢ φ ⇒ ψ ⇒ ψ :=
      (exportation) conjElimRight

    def implSelf
      : Γ ⊢ φ ⇒ φ :=
      (syllogism) contractionConj weakeningConj

    def extraPremise
      : Γ ⊢ φ → Γ ⊢ ψ ⇒ φ := fun p =>
      modusPonens p implProjLeft

    def conjIntroRule
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ χ → Γ ⊢ φ ⇒ ψ ⋀ χ :=
      let l₁ : Γ ⊢ ψ ⋀ χ ⇒ ψ ⋀ χ := implSelf
      let l₂ : Γ ⊢ ψ ⇒ χ ⇒ ψ ⋀ χ := (exportation) l₁
      fun l₃ : Γ ⊢ φ ⇒ ψ =>
      let l₄ : Γ ⊢ φ ⇒ χ ⇒ ψ ⋀ χ := (syllogism) l₃ l₂
      let l₅ : Γ ⊢ χ ⋀ φ ⇒ φ ⋀ χ := permutationConj
      let l₆ : Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ := (importation) l₄
      let l₇ : Γ ⊢ χ ⋀ φ ⇒ ψ ⋀ χ := (syllogism) l₅ l₆
      fun l₈ : Γ ⊢ φ ⇒ χ =>
      let l₉ : Γ ⊢ χ ⇒ (φ ⇒ ψ ⋀ χ) := (exportation) l₇
      let l₁₀ : Γ ⊢ φ ⇒ φ ⇒ ψ ⋀ χ := (syllogism) l₈ l₉
      let l₁₁ : Γ ⊢ φ ⋀ φ ⇒ ψ ⋀ χ := (importation) l₁₀
      (syllogism) contractionConj l₁₁

    def conjIntroHypConcLeft
      : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⋀ χ ⇒ ψ ⋀ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ φ ⋀ χ ⇒ χ := conjElimRight
      let l₃ : Γ ⊢ φ ⋀ χ ⇒ ψ := (syllogism) conjElimLeft l₁
      (conjIntroRule) l₃ l₂


    def modusPonensExtraHyp : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ :=
      fun l₁ l₂ => (syllogism) ((conjIntroRule) implSelf l₁) ((importation) l₂)

    -- bad name
    def modusPonensThm : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ) ⋀ φ ⇒ χ :=
      let ψ' := (φ ⇒ ψ ⇒ χ) ⋀ (φ ⇒ ψ)
      let φ' := ψ' ⋀ φ
      let l₁ : Γ ⊢ φ' ⇒ ψ' := conjElimLeft
      let l₂ : Γ ⊢ ψ' ⇒ φ ⇒ ψ := conjElimRight
      let l₃ : Γ ⊢ φ' ⇒ φ := conjElimRight
      let l₄ : Γ ⊢ φ' ⇒ φ ⇒ ψ := (syllogism) l₁ l₂
      let l₅ : Γ ⊢ φ' ⇒ ψ := (modusPonensExtraHyp) l₃ l₄
      let l₆ : Γ ⊢ ψ' ⇒ φ ⇒ ψ ⇒ χ := conjElimLeft
      let l₇ : Γ ⊢ φ' ⇒ φ ⇒ ψ ⇒ χ := (syllogism) l₁ l₆
      let l₈ : Γ ⊢ φ' ⇒ ψ ⇒ χ := (modusPonensExtraHyp) l₃ l₇
      let l₉ : Γ ⊢ φ' ⇒ χ := (modusPonensExtraHyp) l₅ l₈
      l₉

    def implDistribLeft : Γ ⊢ (φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ χ) :=
      (exportation) $ (exportation) modusPonensThm

    def implDistribRight : Γ ⊢ ((φ ⇒ ψ) ⇒ (φ ⇒ χ)) ⇒ (φ ⇒ ψ ⇒ χ) := tautology

    def syllogismExtraHyp : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ φ ⇒ χ ⇒ θ → Γ ⊢ φ ⇒ ψ ⇒ θ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) := toRule implDistribLeft l₁
      fun l₃ : Γ ⊢ φ ⇒ χ ⇒ θ =>
      let l₄ : Γ ⊢ (φ ⇒ χ) ⇒ (φ ⇒ θ) := toRule implDistribLeft l₃
      let l₅ : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ θ) := (syllogism) l₂ l₄
      let l₆ : Γ ⊢ φ ⇒ ψ ⇒ θ := toRule implDistribRight l₅
      l₆

    def permuteHyps : Γ ⊢ φ ⇒ ψ ⇒ χ → Γ ⊢ ψ ⇒ φ ⇒ χ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ ⇒ χ =>
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ χ := (importation) l₁
      let l₃ : Γ ⊢ ψ ⋀ φ ⇒ χ := (syllogism) permutationConj l₂
      (exportation) l₃


    def disjIntroAtHypThm : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ (φ ⋁ ψ ⇒ χ) :=
      let l₁ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ φ ⇒ χ := conjElimLeft
      let l₂ : Γ ⊢ φ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps) l₁
      let l₃ : Γ ⊢ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ ψ ⇒ χ := conjElimRight
      let l₄ : Γ ⊢ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (permuteHyps) l₃
      let l₅ : Γ ⊢ φ ⋁ ψ ⇒ (φ ⇒ χ) ⋀ (ψ ⇒ χ) ⇒ χ := (disjIntroAtHyp) l₂ l₄
      (permuteHyps) l₅

    def conjIntroAtConclThm : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ χ) ⇒ (φ ⇒ ψ ⋀ χ) :=
      let l₁ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ φ := conjElimRight
      let l₂ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ ψ) := (syllogism) conjElimLeft conjElimLeft
      let l₃ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ := (modusPonensExtraHyp) l₁ l₂
      let l₄ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ (φ ⇒ χ) := (syllogism) conjElimLeft conjElimRight
      let l₅ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ χ := (modusPonensExtraHyp) l₁ l₄
      let l₆ : Γ ⊢ ((φ ⇒ ψ) ⋀ (φ ⇒ χ)) ⋀ φ ⇒ ψ ⋀ χ := (conjIntroRule) l₃ l₅
      (exportation) $ (exportation) l₆


    def negImplIntro : Γ ⊢ φ ⇒ ψ → Γ ⊢ ∼ψ ⇒ ∼φ :=
      let thm : Γ ⊢ (φ ⇒ ψ) ⇒ (∼ψ ⇒ ∼φ) := tautology
      toRule thm

    def negConjAsImpl : Γ ⊢ ∼(φ ⋀ ψ) ⇒ φ ⇒ ∼ψ := tautology



    def doubleNegIntro : Γ ⊢ φ ⇒ ∼∼φ := tautology

    def doubleNegElim : Γ ⊢ ∼∼φ ⇒ φ := tautology

    def topImplSelfImplSelf : Γ ⊢ (⊤ ⇒ φ) ⇒ φ := tautology


  end Proof
end Propositional



  section FirstOrder
    namespace Proof
    variable {sgn : Signature 𝓢} {Γ : Premises sgn}
    variable {s t : 𝓢} {φ ψ χ θ : Pattern sgn (.base s)} {x y : EVar}

    def implExistSelf : Γ ⊢ φ ⇒ ∃∃ (.base t) x φ :=
      let l₁ : Γ ⊢ φ[x ⇐ᵉ x] ⇒ ∃∃ t x φ := existQuan <| substitutable_evar_same _ _
      by rw [Pattern.subst_var_var_eq_self_evar] at l₁ ; exact l₁

    def existSelfImpl (not_fv : ¬φ.FreeEVar x) : Γ ⊢ ∃∃ (.base t) x φ ⇒ φ :=
      let l₁ : Γ ⊢ φ ⇒ φ := (implSelf)
      existGen not_fv l₁

    def pushExistInConj (not_fv : ¬ψ.FreeEVar x) : Γ ⊢ ∃∃ (.base t) x (φ ⋀ ψ) ⇒ ∃∃ (.base t) x φ ⋀ ψ :=
      let l₁ : Γ ⊢ φ ⇒ ∃∃ t x φ := implExistSelf
      let l₂ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ t x φ ⋀ ψ := (conjIntroHypConcLeft) l₁
      existGen (by aesop?) l₂

    def univQuan (sfi : SubstitutableEVarForIn x y φ)
      : Γ ⊢ ∀∀ (.base t) x φ ⇒ φ[x ⇐ᵉ y] :=
      let l₁ : Γ ⊢ ∀∀ t x φ ⇒ ∼∼φ[x ⇐ᵉ y] := (negImplIntro) <| @existQuan _ _ _ _ _ _ (∼φ) _ _ (by aesop?)
      (syllogism) l₁ (doubleNegElim)

    def univGen (not_fv : ¬φ.FreeEVar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ ⇒ ∀∀ (.base t) x ψ :=
      fun l₁ : Γ ⊢ φ ⇒ ψ =>
      let l₂ : Γ ⊢ ∼ψ ⇒ ∼φ := (negImplIntro) l₁
      let l₃ : Γ ⊢ ∃∃ t x (∼ψ) ⇒ ∼φ := existGen (by aesop?) l₂
      let l₄ : Γ ⊢ ∼∼φ ⇒ ∼(∃∃ t x (∼ψ)) := (negImplIntro) l₃
      let l₅ : Γ ⊢ ∼∼φ ⇒ (∀∀ t x ψ) := l₄
      (syllogism) (doubleNegIntro) l₅

    def univGeneralization : Γ ⊢ φ → Γ ⊢ ∀∀  (.base t) x φ :=
      fun l₁ : Γ ⊢ φ =>
      let l₁ : Γ ⊢ ⊤ ⇒ φ := toRule tautology l₁
      let l₂ : Γ ⊢ ⊤ ⇒ ∀∀ t x φ := (univGen) (by simp [*] at *) l₁
      toRule (topImplSelfImplSelf) l₂

    def pushConjInExist (not_fv : ¬ψ.FreeEVar x) : Γ ⊢ ∃∃ (.base t) x φ ⋀ ψ ⇒ ∃∃ (.base t) x (φ ⋀ ψ) :=
      let l₁ : Γ ⊢ φ ⋀ ψ ⇒ ∃∃ _ x (φ ⋀ ψ) := (implExistSelf)
      let l₂ : Γ ⊢ φ ⇒ ψ ⇒ ∃∃ _ x (φ ⋀ ψ) := (exportation) l₁
      let l₃ : Γ ⊢ ∃∃ _ x φ ⇒ ψ ⇒ ∃∃ _ x (φ ⋀ ψ) := (existGen) (by aesop) l₂
      let l₄ : Γ ⊢  ∃∃ _ x φ ⋀ ψ ⇒ ∃∃ _ x (φ ⋀ ψ) := (importation) l₃
      l₄

    end Proof
  end FirstOrder



section ContextReasoning
  namespace Proof

  variable {sgn : Signature 𝓢} {Γ : Premises sgn}

  def NestedContext.framing {s t : 𝓢} {C : NestedContext sgn s t} {φ ψ : Pattern sgn (.base s)} :
    Γ ⊢ φ ⇒ ψ → Γ ⊢ C[φ] ⇒ C[ψ] :=
    fun l₁ : Γ ⊢ φ ⇒ ψ =>
    match C with
    | .empty => l₁
    | .nest Cσ C' =>
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[ψ] := framing l₁
      let l₃ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[ψ]) := Proof.framing l₂
      l₃

  def NestedContext.propagationBottom {s t : 𝓢} {C : NestedContext sgn s t} : Γ ⊢ C[⊥] ⇒ ⊥ :=
    let x : EVar := ⟨0⟩
    let l₁ : Γ ⊢ ⊥ ⇒ .evar _ x ⋀ ⊥ := exFalso
    let l₂ : Γ ⊢ ⊥ ⇒ .evar _ x ⋀ ∼⊥ := exFalso
    let l₃ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] := NestedContext.framing l₁
    let l₄ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ∼⊥] := NestedContext.framing l₂
    let l₅ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥] := conjIntroRule l₃ l₄
    let l₆ : Γ ⊢ ∼(C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥]) := singleton
    syllogism l₅ l₆


  def NestedContext.propagationDisj {s t : 𝓢} {C : NestedContext sgn s t} {φ ψ : Pattern sgn (.base s)}:
    Γ ⊢ C.insert (φ ⋁ ψ) ⇒ C.insert φ ⋁ C.insert ψ :=
    match C with
    | .empty => implSelf
    | .nest Cσ C' =>
      let l₁ : Γ ⊢ C'[φ ⋁ ψ] ⇒ C'[φ] ⋁ C'[ψ] := propagationDisj
      let l₂ : Γ ⊢ Cσ.insert (C'[φ ⋁ ψ]) ⇒ Cσ.insert (C'[φ] ⋁ C'[ψ]) := Proof.framing l₁
      let l₂ : Γ ⊢ (C'.nest Cσ)[φ ⋁ ψ] ⇒ Cσ.insert (C'[φ] ⋁ C'[ψ]) := by exact l₂ -- this is actually definitionally (as witnessed in `Context.nest_insert`) but doesn't work without `by exact`???
        -- rw [Context.nest_insert] -- this is actually
        -- exact l₂
      let l₃ : Γ ⊢ Cσ.insert (C'[φ] ⋁ C'[ψ]) ⇒ (Cσ.insert (C'[φ])) ⋁ (Cσ.insert (C'[ψ])) := Proof.propagationDisj
      (syllogism) l₂ l₃

  def NestedContext.propagationDisjR {s t : 𝓢} {C : NestedContext sgn s t} {φ ψ : Pattern sgn (.base s)} :
    Γ ⊢ C[φ] ⋁ C[ψ] ⇒ C[φ ⋁ ψ] :=
    match C with
    | .empty => implSelf
    | .nest Cσ C' =>
      let l₁ : Γ ⊢ C'[φ] ⋁ C'[ψ] ⇒ C'[φ ⋁ ψ] := propagationDisjR
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[φ ⋁ ψ] := (syllogism) disjIntroLeft l₁
      let l₃ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[φ ⋁ ψ]) := Proof.framing l₂
      let l₄ : Γ ⊢ (C'.nest Cσ)[φ] ⇒ (C'.nest Cσ)[φ ⋁ ψ] :=
      by
        rw [NestedContext.nest_insert]
        rw [NestedContext.nest_insert]
        exact l₃
      let l₂' : Γ ⊢ C'[ψ] ⇒ C'[φ ⋁ ψ] := (syllogism) (disjIntroRight) l₁
      let l₃' : Γ ⊢ Cσ.insert (C'[ψ]) ⇒ Cσ.insert (C'[φ ⋁ ψ]) := Proof.framing l₂'
      let l₄' : Γ ⊢ (C'.nest Cσ)[ψ] ⇒ (C'.nest Cσ)[φ ⋁ ψ] := l₃'
      (disjIntroAtHyp) l₄ l₄'

    def NestedContext.propagationExist {s t r : 𝓢} {C : NestedContext sgn s t} {φ : Pattern sgn s} {x : EVar} (hnfv : ¬C.FreeEVar x) :
      Γ ⊢ (C[∃∃ r x φ]) ⇒ (∃∃ r x (C [φ])) :=
      match h:C with
      | .empty => implSelf
      | .nest Cσ C' =>
        have not_fvχ : ¬Cσ.FreeEVar x := by aesop?
        let l₁ : Γ ⊢ (C'[∃∃ r x φ]) ⇒ (∃∃ r x (C'[φ])) := propagationExist (by aesop?)
        let l₂ : Γ ⊢ Cσ.insert (C'[∃∃ r x φ]) ⇒ Cσ.insert (∃∃ r x (C'[φ])) := Proof.framing l₁
        let l₃ : Γ ⊢ Cσ.insert (∃∃ r x (C'[φ])) ⇒ (∃∃ r x (Cσ.insert <| C'[φ])) := Proof.propagationExist (by
          have : ¬Cσ.FreeEVar x := by aesop?
          apply AppContext.insert_not_free_evar
          . aesop -- exists_binds
          . assumption
        )
        let l₄ : Γ ⊢ Cσ.insert (C'[∃∃ r x φ]) ⇒ (∃∃ r x (Cσ.insert <| C'[φ])) := (syllogism) l₂ l₃
        l₄


    def NestedContext.propagationExistR {s t r : 𝓢} {C : NestedContext sgn s t} {φ : Pattern sgn s} {x : EVar} (hnfv : ¬C.FreeEVar x) :
      Γ ⊢ (∃∃ r x (C [φ])) ⇒ (C[∃∃ r x φ]) :=
      match h:C with
      | .empty => implSelf
      | .nest Cσ C' =>
        have not_fvEφ : ¬(∃∃ r x φ).FreeEVar x := by aesop?
        have not_fvCEφ : ¬((C'.nest Cσ)[∃∃ r x φ]).FreeEVar x := by
          -- rw [AppContext.no_free_occ_evar_insert]
          -- exact And.intro not_fvEφ not_fv
          rw [NestedContext.nest_insert]
          apply AppContext.insert_not_free_evar
          . simp at hnfv
            push_neg at hnfv
            sorry
          . aesop
        let l₁ : Γ ⊢ (∃∃ r x (C'[φ])) ⇒ (C'[∃∃ r x φ]) := propagationExistR (C := C') (by aesop?)
        let l₂ : Γ ⊢ C'[φ][x ⇐ᵉ x] ⇒ ∃∃ r x (C'[φ]) := existQuan <| Pattern.substitutable_evar_same _ _
        let l₃ : Γ ⊢ C'[φ][x ⇐ᵉ x] ⇒ C'[∃∃ r x φ] := syllogism l₂ l₁
        -- let l₄ : Γ ⊢ (C'.substEvar x x)[φ[x ⇐ᵉ x]] ⇒ C'[∃∃ r x φ] := by
        --   rw [AppContext.subst_evar_insert] at l₃ ; exact l₃
        -- let l₄ : Γ ⊢ C'[φ[x ⇐ᵉ .evar x]] ⇒ C'[∃∃ x φ] := by rw [AppContext.subst_var_var_eq_self_evar] at l₄ ; exact l₄
        let l₅ : Γ ⊢ C'[φ] ⇒ C'[∃∃ r x φ] := by rw [Pattern.subst_var_var_eq_self_evar] at l₃ ; exact l₃ -- why did I do it so convoluted in the other formalization?
        let l₆ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[∃∃ r x φ]) := Proof.framing l₅
        let l₇ : Γ ⊢ (C'.nest Cσ)[φ] ⇒ (C'.nest Cσ)[∃∃ r x φ] := by simpa [*]
        let l₉ : Γ ⊢ ∃∃ r x ((C'.nest Cσ)[φ]) ⇒ (C'.nest Cσ)[∃∃ r x φ] := existGen not_fvCEφ l₇
        l₉

  end Proof
end ContextReasoning

namespace Proof

@[simp]
noncomputable def size {Γ : Premises sgn} {s : 𝓢} {φ : Pattern sgn s} : Proof Γ φ → ℕ
-- | cast _ _ => 0
| premise _ => 1
| modusPonens prf₁ prf₂ => prf₁.size + prf₂.size + 1
| existQuan _ => 1
| existGen _ prf => prf.size + 1
| existence => 1
| singleton => 1
| propagationDisj => 1
| propagationExist _ => 1
| framing prf => prf.size + 1
| substitution _ prf => prf.size + 1
| prefixpoint _ _ => 1
| knasterTarski _ prf => prf.size + 1
