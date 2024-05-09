import ManySortedMatchingLogic.Pattern
import ManySortedMatchingLogic.Tautology

set_option autoImplicit false

open Pattern

variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

inductive Proof (Γ : Set <| Pattern sgn) :
  Pattern sgn → Type where
| premise {φ : Pattern sgn} {s : S}
  (wsφ : WellSorted φ s) :
  φ ∈ Γ → Proof Γ φ

| tautology {φ : Pattern sgn} {s : S}
  (is_tauto : Tautology φ)
  (wsφ : WellSorted φ s) :
  Proof Γ φ

| modusPonens {φ ψ : Pattern sgn} :
  Proof Γ φ → Proof Γ (φ ⇒ ψ) → Proof Γ ψ

| existQuan {φ} {x} {y} {s} : SubstitutableEVarForIn x y φ →
  (wsφ : WellSorted φ s := by simp_all) →
  Proof Γ ((φ.substEVar x y) ⇒ ∃∃ x φ)

| existGen {φ ψ} {x} : ¬FreeEVar x ψ →
  Proof Γ (φ ⇒ ψ) → Proof Γ ((∃∃ x φ) ⇒ ψ)

| propagationDisj {C : AppContext sgn} {φ ψ : Pattern sgn} {s} :
  (wsφ : WellSorted φ s := by simp_all) → (wsψ : WellSorted ψ s := by simp_all) → C.holeSort = s →
  Proof Γ (C.insert (φ ⋁ ψ) ⇒ C.insert φ ⋁ C.insert ψ)

| propagationExist {C : AppContext sgn} {x : EVar S} {φ : Pattern sgn} {s} :
  (wsφ : WellSorted φ s := by simp_all) → C.holeSort = s →
  ¬FreeEVar x (C.insert (∃∃ x φ)) →
  Proof Γ (C.insert (∃∃ x φ) ⇒ ∃∃ x (C.insert φ))

| framing {C : AppContext sgn} {φ ψ : Pattern sgn} {s} :
  (wsφ : WellSorted φ s := by simp_all) → (wsψ : WellSorted ψ s := by simp_all) → C.holeSort = s →
  Proof Γ (φ ⇒ ψ) → Proof Γ (C.insert φ ⇒ C.insert ψ)

| singleton {C₁ C₂ : NestedContext sgn} {x : EVar S} {φ : Pattern sgn} :
  Proof Γ <| ∼(C₁.insert (x ⋀ φ) ⋀ C₂.insert (x ⋀ ∼φ))

| existence {x} :
  Proof Γ (∃∃ x (.evar x))

| substitution {φ} {ψ} {X} : SubstitutableSVarForIn X ψ φ →
  WellSorted ψ X.sort →
  Proof Γ φ → Proof Γ (φ.substSVar X ψ)

| prefixpoint {φ} {X} : ¬NegativeOcc X φ → SubstitutableSVarForIn X (μ X φ) φ →
  Proof Γ ((φ.substSVar X (μ X φ)) ⇒ μ X φ)

| knasterTarski {φ ψ} {X} : SubstitutableSVarForIn X ψ φ →
  Proof Γ ((φ.substSVar X ψ) ⇒ ψ) → Proof Γ (μ X φ ⇒ ψ)

macro "arrow_precedence" : prec => `(prec| 24)
infix:(arrow_precedence + 1) " ⊢ " => Proof

-- macro "tautology" : term => `(term| sorry)

-- def Proof.wellSorted {Γ : Set <| Pattern sgn} {φ : Pattern sgn} (proof : Proof Γ φ) : {s : S // WellSorted φ s} :=
--   match proof with
--   | modusPonens prf₁ prf₂ ws₁ ws₂ =>
--     let ⟨s, hs⟩ := prf₁.wellSorted
--     ⟨s, _⟩
--   | _ => _
