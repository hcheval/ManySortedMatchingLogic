import ManySortedMatchingLogic.ContextProofs

set_option autoImplicit false

inductive Defined where
| defined


#synth OfNat (Fin 2) 5

def SgnDef {S} : Signature (Defined × S × S) S where
  arity := fun _ => 1
  target := fun (_, _, t) => t
  domain := fun ⟨_, s, _⟩ => fun _ => s

def Pattern.defined {S} (s t : S) (φ : Pattern (@SgnDef S)) : Pattern (@SgnDef S) :=
  (.defined, s, t) ⬝ (fun (i : Fin 1) => match i with | 0 => φ)

-- notation "⌈" φ "⌉" => Pattern.application (Pattern.symbol defined) φ
notation "⌈" φ "⌉|" s ";" t "|" => Pattern.defined s t φ

-- def HasDefined {𝓢} (sgn : Signature 𝓢) := ∀ {s t : 𝓢}, @defined _ s t ∈ sgn

def total {S} (s t : S) (φ) := ∼⌈∼φ⌉|s;t|
-- notation "⌊" φ "⌋" => total φ
notation "⌊" φ "⌋|" s ";" t "|" => @total _ s t φ


def definedness {S} {s t : S} {x : EVar S} : Pattern (@SgnDef S) :=
  ⌈.evar x⌉|t;s|

-- def HasDefinedness {S} {s t : S} {x : EVar S} (Γ : Set <| Pattern (@SgnDef S)) :=
--   ⟨_, ⌈.evar t x⌉|t;s|⟩ ∈ Γ

notation "◫" => 100

def AppContext.Defined {S : Type} (s t : S) : AppContext (@SgnDef S) where
  symbol := (.defined, s, t)
  hole := (0 : Fin 1)
  args := fun (i : Fin 1) => match i with | 0 => SVar.mk ◫ s
  args_well_sorted := fun (i : Fin 1) => match i with | 0 => by intros; contradiction
  -- fun φ : Pattern (@SgnDef S) => ⟨⌈φ⌉|s;t|, sorry⟩

def NestedContext.Defined {S : Type} (s t : S) : NestedContext (@SgnDef S) :=
  (□ s).nest (AppContext.Defined s t)

theorem context_defined_insert {S : Type} {s t : S} {φ : Pattern (@SgnDef S)} : (NestedContext.Defined s t)[φ] = ⌈φ⌉|s;t| := by
  simp? [AppContext.Defined, AppContext.insert, Function.update, Pattern.defined]
  ext (i : Fin 1)
  fin_cases i
  rfl

theorem NestedContext.defined_hole_sort {S : Type} {s t : S} : (NestedContext.Defined s t).holeSort = s := by
  rfl

theorem NestedContext.defined_well_sorted {S : Type} {s t : S} : (NestedContext.Defined s t).WellSorted t := by
  dsimp [Defined]
  apply NestedContext.WellSorted.nest (s := s) ?_ ?_
  . -- simp [AppContext.Defined, AppContext.target]
    rfl
  . apply NestedContext.WellSorted.empty
  . rfl






section
  open Proof Pattern
  #check Proof.NestedContext.propagationDisj
  variable {S : Type} [DecidableEq S]
    {Γ : Set <| Pattern (@SgnDef S)}
    (hasDefinedness : ∀ {s t : S} {x : EVar S}, ⌈.evar x⌉|s;t| ∈ Γ)

    def definednessPropagationDisj {s t : S} {φ ψ : Pattern (@SgnDef S)}
      (wsφ : WellSorted φ s)
      (wsψ : WellSorted ψ s)
    :
      Γ ⊢ ⌈φ ⋁ ψ⌉|s;t| ⇒ ⌈φ⌉|s;t| ⋁ ⌈ψ⌉|s;t| := by
        rw [← context_defined_insert, ← context_defined_insert, ← context_defined_insert]
        have : (NestedContext.Defined s t).WellSorted t := NestedContext.defined_well_sorted
        apply NestedContext.propagationDisj (s := s) (t := t) (compat := NestedContext.defined_hole_sort) (wsφ := wsφ) (wsψ := wsψ) (wsC := NestedContext.defined_well_sorted) (C := NestedContext.Defined s t)

    -- #exit
    def definednessPropagationDisjR {s t : S} {φ ψ : Pattern (@SgnDef S)}
      (wsφ : WellSorted φ s)
      (wsψ : WellSorted ψ s)
    :
      Γ ⊢ ⌈φ⌉|s;t| ⋁ ⌈ψ⌉|s;t| ⇒ ⌈φ ⋁ ψ⌉|s;t| := by
      rw [← context_defined_insert, ← context_defined_insert, ← context_defined_insert]
      let l₁ : Γ ⊢ (NestedContext.Defined s t)[φ] ⋁ (NestedContext.Defined s t)[ψ] ⇒ (NestedContext.Defined s t)[φ ⋁ ψ] :=
        NestedContext.propagationDisjR (s := s) (t := t) (compat := NestedContext.defined_hole_sort) (C := NestedContext.Defined s t) (wsφ := wsφ) (wsψ := wsψ) (wsC := NestedContext.defined_well_sorted)
      exact l₁
      -- Context.propagationDisjR (C := Context.Defined)
      -- l₁
  -- #exit
    def definedFraming {s t : S} {φ ψ : Pattern (@SgnDef S)}
      (wsφ : WellSorted φ s)
      (wsψ : WellSorted ψ s)
    :
      Γ ⊢ φ ⇒ ψ → Γ ⊢ ⌈φ⌉|s;t| ⇒ ⌈ψ⌉|s;t| := by
      intros l₁
      rw [← context_defined_insert, ← context_defined_insert]
      let l₂ := NestedContext.framing (s := s) (t := t) (compat := NestedContext.defined_hole_sort) (C := NestedContext.Defined s t) (wsφ := wsφ) (wsψ := wsψ) (wsC := NestedContext.defined_well_sorted) l₁
      exact l₂

-- #exit
    def ctxImplDefinedAux1 {s t : S} {C : NestedContext (@SgnDef S)} {φ : Pattern (@SgnDef S)} (x : EVar S) :
      Γ ⊢ C.insert (x ⋀ φ) ⇒ ⌈φ⌉|s;t| :=
    let l₁ : Γ ⊢ ⌈.evar x⌉|s;t| := .premise _ hasDefinedness
    let l₂ : Γ ⊢ ⌈.evar x⌉|s;t| ⋁ ⌈φ⌉|s;t| := modusPonens l₁ (disjIntroLeft)
    let l₃ : Γ ⊢ ⌈.evar x ⋁ φ⌉|s;t| := toRule (definednessPropagationDisjR) l₂
    let l₄ : Γ ⊢ ⌈(.evar x ⋀ ∼φ) ⋁ φ⌉|s;t| :=
      let l₁' : Γ ⊢ .evar x ⋁ φ ⇒ (.evar x ⋀ ∼φ) ⋁ φ := tautology
      let l₂' : Γ ⊢ ⌈.evar x ⋁ φ⌉|s;t| ⇒ ⌈(.evar _ x ⋀ ∼φ) ⋁ φ⌉|s;t| := definedFraming l₁'
      toRule l₂' l₃
    let l₅ : Γ ⊢ ⌈.evar x ⋀ ∼φ⌉|s;t| ⋁ ⌈φ⌉|s;t| := toRule (definednessPropagationDisj) l₄
    let l₆ : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈.evar x ⋀ ∼φ⌉|s;t| :=
      let l₁' : Γ ⊢ ∼(C[x ⋀ φ] ⋀ ⌈.evar x ⋀ ∼φ⌉|s;t|) := (Proof.singleton (C₁ := C) (C₂ := NestedContext.Defined s t))
      let l₂' : Γ ⊢ C[x ⋀ φ] ⇒ ∼⌈.evar x ⋀ ∼φ⌉|s;t| := toRule (negConjAsImpl) l₁'
      l₂'
    let l₇ : Γ ⊢ ∼⌈.evar x ⋀ ∼φ⌉|s;t| ⇒ ⌈φ⌉|s;t| := l₅
    let l₈ : Γ ⊢ C[.evar x ⋀ φ] ⇒ ⌈φ⌉|s;t| := (syllogism) l₆ l₇
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉|s;t| := l₈
    l₉

-- #exit

  def ctxImplDefined {s t : S} {C : NestedContext (@SgnDef S)} {φ : Pattern (@SgnDef S)} :
    Γ ⊢ C[φ] ⇒ ⌈φ⌉|s;t| :=
    let x : EVar S := sorry
    have not_fv_φ : ¬φ.FreeEVar x := sorry
    -- have not_fv_C : ¬C.FreeEVar x := sorry
    let l₉ : Γ ⊢ C[x ⋀ φ] ⇒ ⌈φ⌉|s;t| := (ctxImplDefinedAux1) x
    let l₁₀ : Γ ⊢ ∃∃ x (C[x ⋀ φ]) ⇒ ⌈φ⌉|s;t| := existGen sorry l₉
    let l₁₁ : Γ ⊢ φ ⇒ (∃∃ x (x)) ⋀ φ :=
      let l₁' : Γ ⊢ φ ⇒ φ := (implSelf)
      let l₂' : Γ ⊢ ∃∃ x (x) := existence
      let l₃' : Γ ⊢ φ ⇒ ∃∃ x x := (extraPremise) l₂'
      let l₄' : Γ ⊢ φ ⇒ (∃∃ x x) ⋀ φ := (conjIntroRule) l₃' l₁'
      l₄'
    let l₁₂ : Γ ⊢ φ ⇒ ∃∃ x (x ⋀ φ) := (syllogism) l₁₁ ((Proof.pushConjInExist) not_fv_φ)
    let l₁₃ : Γ ⊢ C[φ] ⇒ C[(∃∃ x (x ⋀ φ))] := (NestedContext.framing) l₁₂
    let l₁₄ : Γ ⊢ C[(∃∃ x (x ⋀ φ))] ⇒ ⌈φ⌉ :=
      let l₁' : Γ ⊢ C[(∃∃ x (x ⋀ φ))] ⇒ ∃∃ x (C[x ⋀ φ]) := NestedContext.propagationExist sorry
      (syllogism) l₁' l₁₀
    let l₁₅ : Γ ⊢ C[φ] ⇒ ⌈φ⌉ := (syllogism) l₁₃ l₁₄
    l₁₅

  def implDefined {s : S} {φ : Pattern (@SgnDef S)} : Γ ⊢ φ ⇒ ⌈φ⌉|s;s| := ctxImplDefined (C := .empty s)

  def totalImpl {s : S} {φ : Pattern (@SgnDef S)} : Γ ⊢ ⌊φ⌋|s;s| ⇒ φ :=
    let l₁ : Γ ⊢ ∼φ ⇒ ⌈∼φ⌉|s;s| := implDefined
    let l₂ : Γ ⊢ ∼⌈∼φ⌉|s;s| ⇒ ∼∼φ := (negImplIntro) l₁
    let l₃ : Γ ⊢ ⌊φ⌋|s;s| ⇒ ∼∼φ := l₂
    (syllogism) l₃ (doubleNegElim)

end
