import ManySortedMatchingLogic.ProofIntrinsic

set_option autoImplicit false

def defined {𝓢 : Type} {s t : 𝓢} : Symbol 𝓢 where
  name := "defined"
  domain := s
  target := t


notation "⌈" φ "⌉" => Pattern.application (Pattern.symbol defined) φ
notation "⌈" φ "⌉|" s ";" t "|" => Pattern.application (Pattern.symbol <| @defined _ s t) φ

def HasDefined {𝓢} (sgn : Signature 𝓢) := ∀ {s t : 𝓢}, @defined _ s t ∈ sgn

def total {𝓢} {sgn : Signature 𝓢} {s t : 𝓢} (φ : Pattern sgn s) : Pattern sgn t := ∼⌈∼φ⌉
notation "⌊" φ "⌋" => total φ
notation "⌊" φ "⌋|" s ";" t "|" => @total _ _ s t φ


def definedness {𝓢} {sgn : Signature 𝓢} (hasDefined : HasDefined sgn) {s t : 𝓢} {x : EVar} : Pattern sgn s :=
  ⌈.evar t x⌉

def HasDefinedness {𝓢} {sgn : Signature 𝓢} (hasDefined : HasDefined sgn) {s t : 𝓢} {x : EVar} (Γ : Premises sgn) :=
  ⟨_, ⌈.evar t x⌉|t;s|⟩ ∈ Γ

def AppContext.Defined {𝓢 : Type} (sgn : Signature 𝓢) (s t : 𝓢) : AppContext sgn s t :=
  fun φ : Pattern sgn s => ⟨⌈φ⌉, sorry⟩

def NestedContext.Defined {𝓢 : Type} (sgn : Signature 𝓢) (s t : 𝓢) : NestedContext sgn s t :=
  □.nest (AppContext.Defined sgn s t)

theorem context_defined_insert {𝓢 : Type} {sgn : Signature 𝓢} {s t : 𝓢} {φ : Pattern sgn s} : (NestedContext.Defined sgn s t)[φ] = ⌈φ⌉|s;t| := by
  rfl

section
  open Proof
  variable {𝓢 : Type} [DecidableEq 𝓢] {sgn : Signature 𝓢} (hasDefined : HasDefined sgn)
    {Γ : Premises sgn} (hasDefinedness : ∀ {s t : 𝓢}, ⟨_, ⌈.evar x⌉|s;t|⟩ ∈ Γ)

    def definednessPropagationDisj {s t : 𝓢} {φ ψ : Pattern sgn s} :
      Γ ⊢ ⌈φ ⋁ ψ⌉|s;t| ⇒ ⌈φ⌉|s;t| ⋁ ⌈ψ⌉|s;t| :=
        NestedContext.propagationDisj (C := NestedContext.Defined sgn s t)

    def definednessPropagationDisjR {s t : 𝓢} {φ ψ : Pattern sgn s} :
      Γ ⊢ ⌈φ⌉|s;t| ⋁ ⌈ψ⌉|s;t| ⇒ ⌈φ ⋁ ψ⌉|s;t| :=
      let l₁ : Γ ⊢ (NestedContext.Defined sgn s t)[φ] ⋁ (NestedContext.Defined sgn s t)[ψ] ⇒ (NestedContext.Defined sgn s t)[φ ⋁ ψ] :=
        NestedContext.propagationDisjR (C := NestedContext.Defined sgn s t)
      -- Context.propagationDisjR (C := Context.Defined)
      l₁

    def definedFraming {s t : 𝓢} {φ ψ : Pattern sgn s} :
      Γ ⊢ φ ⇒ ψ → Γ ⊢ ⌈φ⌉|s;t| ⇒ ⌈ψ⌉|s;t| :=
      fun l₁ =>
      let l₂ := NestedContext.framing (C := NestedContext.Defined sgn s t) l₁
      l₂

    def ctxImplDefinedAux1 {s t : 𝓢} {C : NestedContext sgn s t} {φ : Pattern sgn s} (x : EVar) :
      Γ ⊢ C.insert (x ⋀ φ) ⇒ ⌈φ⌉ :=
    let l₁ : Γ ⊢ ⌈.evar _ x⌉|s;t| := .premise hasDefinedness
    let l₂ : Γ ⊢ ⌈.evar _ x⌉ ⋁ ⌈φ⌉ := modusPonens l₁ (disjIntroLeft)
    let l₃ : Γ ⊢ ⌈.evar _ x ⋁ φ⌉ := toRule (definednessPropagationDisjR) l₂
    let l₄ : Γ ⊢ ⌈(.evar _ x ⋀ ∼φ) ⋁ φ⌉ :=
      let l₁' : Γ ⊢ .evar _ x ⋁ φ ⇒ (.evar _ x ⋀ ∼φ) ⋁ φ := tautology
      let l₂' : Γ ⊢ ⌈.evar _ x ⋁ φ⌉|s;t| ⇒ ⌈(.evar _ x ⋀ ∼φ) ⋁ φ⌉|s;t| := definedFraming l₁'
      toRule l₂' l₃
    let l₅ : Γ ⊢ ⌈.evar _ x ⋀ ∼φ⌉|s;t| ⋁ ⌈φ⌉ := toRule (definednessPropagationDisj) l₄
    let l₆ : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈.evar _ x ⋀ ∼φ⌉ :=
      let l₁' : Γ ⊢ ∼(C[x ⋀ φ] ⋀ ⌈.evar _ x ⋀ ∼φ⌉) := (Proof.singleton (C₁ := C) (C₂ := NestedContext.Defined sgn s t))
      let l₂' : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈.evar _ x ⋀ ∼φ⌉ := toRule (negConjAsImpl) l₁'
      l₂'
    let l₇ : Γ ⊢ ∼⌈.evar _ x ⋀ ∼φ⌉ ⇒ ⌈φ⌉ := l₅
    let l₈ : Γ ⊢ C[.evar _ x ⋀ φ] ⇒ ⌈φ⌉ := (syllogism) l₆ l₇
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ := l₈
    l₉


  def ctxImplDefined {s t : 𝓢} {C : NestedContext sgn s t} {φ : Pattern sgn s} :
    Γ ⊢ C[φ] ⇒ ⌈φ⌉|s;t| :=
    let x : EVar := sorry
    have not_fv_φ : ¬φ.FreeEVar x := sorry
    -- have not_fv_C : ¬C.FreeEVar x := sorry
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉ := (ctxImplDefinedAux1) x
    let l₁₀ : Γ ⊢ ∃∃ s x (C[x ⋀ φ]) ⇒ ⌈φ⌉ := existGen sorry l₉
    let l₁₁ : Γ ⊢ φ ⇒ (∃∃ s x (x)) ⋀ φ :=
      let l₁' : Γ ⊢ φ ⇒ φ := (implSelf)
      let l₂' : Γ ⊢ ∃∃ s x (x) := existence
      let l₃' : Γ ⊢ φ ⇒ ∃∃ s x x := (extraPremise) l₂'
      let l₄' : Γ ⊢ φ ⇒ (∃∃ s x x) ⋀ φ := (conjIntroRule) l₃' l₁'
      l₄'
    let l₁₂ : Γ ⊢ φ ⇒ ∃∃ s x (x ⋀ φ) := (syllogism) l₁₁ ((Proof.pushConjInExist) not_fv_φ)
    let l₁₃ : Γ ⊢ C[φ] ⇒ C[(∃∃ s x (x ⋀ φ))] := (NestedContext.framing) l₁₂
    let l₁₄ : Γ ⊢ C[(∃∃ s x (x ⋀ φ))] ⇒ ⌈φ⌉ :=
      let l₁' : Γ ⊢ C[(∃∃ s x (x ⋀ φ))] ⇒ ∃∃ s x (C[x ⋀ φ]) := NestedContext.propagationExist sorry
      (syllogism) l₁' l₁₀
    let l₁₅ : Γ ⊢ C[φ] ⇒ ⌈φ⌉ := (syllogism) l₁₃ l₁₄
    l₁₅

  def implDefined {s : 𝓢} {φ : Pattern sgn s} : Γ ⊢ φ ⇒ ⌈φ⌉|s;s| := ctxImplDefined (C := .empty)

  def totalImpl {s : 𝓢} {φ : Pattern sgn s} : Γ ⊢ ⌊φ⌋ ⇒ φ :=
    let l₁ : Γ ⊢ ∼φ ⇒ ⌈∼φ⌉ := implDefined
    let l₂ : Γ ⊢ ∼⌈∼φ⌉ ⇒ ∼∼φ := (negImplIntro) l₁
    let l₃ : Γ ⊢ ⌊φ⌋ ⇒ ∼∼φ := l₂
    (syllogism) l₃ (doubleNegElim)

end
