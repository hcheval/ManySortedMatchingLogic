import ManySortedMatchingLogic.Pattern

set_option autoImplicit false

variable {Symbol S : Type} {sgn : Signature Symbol S} {M : Type}

@[simp]
def FalseMorphism (f : Pattern sgn → Set M) : Prop :=
  ∀ m : M, f ⊥ m ↔ False

@[simp]
def ImplMorphism (f : Pattern sgn → Set M) : Prop :=
  ∀ (φ ψ : Pattern sgn) (m : M), f (φ ⇒ ψ) m ↔ f φ m → f ψ m

class Morphism (f : Pattern sgn → Set M) : Prop where
  morphism_false : ∀ m : M, f ⊥ m ↔ False
  morphism_impl : ∀ (φ ψ : Pattern sgn) (m : M), f (φ ⇒ ψ) m ↔ f φ m → f ψ m

attribute [simp] Morphism.morphism_false
attribute [simp] Morphism.morphism_impl

namespace Morphism

  attribute [simp] Pattern.top Pattern.negation Pattern.conjunction Pattern.disjunction in
  section
    variable {f : Pattern sgn → Set M} [Morphism f] (φ ψ : Pattern sgn)

    @[simp] theorem morphism_true : ∀ m : M, f ⊤ m ↔ True := by intros m ; simp?

    @[simp] theorem morphism_neg : ∀ m : M, f (∼φ) m ↔ ¬(f φ) m := by intros m ; simp?

    @[simp] theorem morphism_disj : ∀ m : M, f (φ ⋁ ψ) m ↔ f φ m ∨ f ψ m := by intros m ; simp? ; tauto

    @[simp] theorem morphism_conj : ∀ m : M, f (φ ⋀ ψ) m ↔ f φ m ∧ f ψ m :=
      by intros m ; simp? ; tauto


    -- @[simp] theorem morphism_equiv : ∀ m : M, f (φ ⇔ ψ) m ↔ (f φ m ↔ f ψ m) := by
    --   intros m
    --   have : ∀ p q : Prop, ((((p → q) → False) → False) → (q → p) → False) → False ↔ (p ↔ q) := by
    --     intros p q
    --     have :  ∀ p, p → False ↔ ¬p := fun _ => Iff.rfl
    --     repeat rw [this]
    --     simp
    --     apply Iff.intro
    --     . intros h ; exact Iff.intro h.1 h.2
    --     . intros h ; exact And.intro h.1 h.2
    --   simp [Pattern.equivalence, this]



  end
end Morphism

def Tautology (φ : Pattern sgn) : Prop :=
  ∀ {M : Type} [Inhabited M] (f : Pattern sgn → Set M) [Morphism f], ∀ m : M, f φ m

macro "unfold_tautology" : tactic =>
  `(tactic| simp_rw [Morphism.morphism_conj, Morphism.morphism_disj, Morphism.morphism_impl, Morphism.morphism_neg, Morphism.morphism_equiv, Morphism.morphism_true])
macro "unfold_tautology!" : tactic =>
  `(tactic| try intros _ _ _ _ _ ; unfold_tautology)
