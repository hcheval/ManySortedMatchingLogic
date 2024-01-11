import ManySortedMatchingLogic.ProofIntrinsic
import ManySortedMatchingLogic.Definedness

variable {𝓢 : Type} [DecidableEq 𝓢]
variable {sgn : Signature 𝓢}

namespace Proof

open Pattern

/--
  Returns `true` iff a proof uses the the `knasterTarksi` rule.
-/
@[simp]
def usesKnasterTarski {Γ : Premises sgn} {s : 𝓢} {φ : Pattern sgn s} (prf : Proof Γ φ) : Prop :=
match prf with
-- The Axioms
| premise _
| existQuan _ | existence | singleton
| propagationDisj | propagationExist _ |  prefixpoint _ _
  => False
  -- Binary rules
| modusPonens prf₁ prf₂
  => prf₁.usesKnasterTarski ∨ prf₂.usesKnasterTarski
-- Unary rules
| existGen _ prf | framing prf
| substitution _ prf
  => prf.usesKnasterTarski
| knasterTarski _ _ => True
-- | cast _ _ => False


set_option pp.all false
  def deductionTheoremFramingAux1 {t s : 𝓢} {ψ : Pattern sgn t} {χ₁ χ₂ : Pattern sgn s} :
    Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ → Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ :=
    fun l₁ :  Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ =>
    let l₁' : Γ ⊢ ⌈∼ψ⌉|t;s| ⋁ ∼⌈∼ψ⌉ := excluddedMiddle  -- why is it not inferred?????????????
    let l₂' : Γ ⊢ ⌈∼ψ⌉|t;s| ⋁ (χ₁ ⇒ χ₂) := l₁
    let l₃' : Γ ⊢ ⌈∼ψ⌉|t;s| ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) :=
      let l₁'' : Γ ⊢ ⌈∼ψ⌉|t;s| ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (disjIntroRight)
      let l₂'' : Γ ⊢ ⌈∼ψ⌉|t;s| ⋀ χ₁ ⇒ ⌈∼ψ⌉ := (conjElimLeft)
      let l₃'' : Γ ⊢ ⌈∼ψ⌉|t;s| ⋀ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (syllogism) l₂'' l₁''
      let l₄'' : Γ ⊢ ⌈∼ψ⌉|t;s| ⇒ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (exportation) l₃''
      l₄''
    let l₄' : Γ ⊢ ∼⌈∼ψ⌉|t;s| ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉|t;s|) :=
      let l₁'' : Γ ⊢ (⌊ψ⌋|t;s| ⇒ χ₁ ⇒ χ₂) ⋁ (⌊ψ⌋|t;s| ⇒ χ₁ ⇒ ⌈∼ψ⌉|t;s|) := toRule (disjIntroLeft) l₁
      let l₂'' : Γ ⊢ (⌊ψ⌋|t;s| ⇒ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉|t;s|) := toRule (disjImpl2) l₁''
      l₂''
    let l₅' : Γ ⊢ ⌈∼ψ⌉|t;s| ⋁ ∼⌈∼ψ⌉ ⇒ (χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉) := (disjIntroAtHyp) l₃' l₄'
    let l₆' : Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉|t;s| := modusPonens l₁' l₅'
    l₆'

  def deductionTheoremFramingAux  {s t r: 𝓢} {C : AppContext sgn t r} {ψ : Pattern sgn s} {χ₁ χ₂ : Pattern sgn t} :
    Γ ⊢ ⌊ψ⌋|s;t| ⇒ χ₁ ⇒ χ₂ → Γ ⊢ ⌊ψ⌋|s;r| ⇒ C.insert χ₁ ⇒ C.insert χ₂ :=
    fun l₁ :  Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ =>
    let l₂ : Γ ⊢ χ₁ ⇒ χ₂ ⋁ ⌈∼ψ⌉ := (deductionTheoremFramingAux1) l₁
    let l₃ : Γ ⊢ C.insert (⌈∼ψ⌉) ⇒ ⌈∼ψ⌉ :=
      let l₃_aux := ctxImplDefined (Γ := Γ) (φ := ∼ψ) (C := (NestedContext.Defined sgn _ _).nest C)
      l₃_aux -- defeq
    let l₄ : Γ ⊢ C.insert χ₁ ⇒ C.insert (χ₂ ⋁ ⌈∼ψ⌉) := (framing) l₂
    let l₅ : Γ ⊢ C.insert χ₁ ⇒ C.insert χ₂ ⋁ C.insert ⌈∼ψ⌉ := (syllogism) l₄ (propagationDisj)
    let l₆ : Γ ⊢ C.insert χ₂ ⋁ C.insert ⌈∼ψ⌉ ⇒ C.insert χ₂ ⋁ ⌈∼ψ⌉ := (expansion) l₃
    let l₇ : Γ ⊢ C.insert χ₁ ⇒ C.insert χ₂ ⋁ ⌈∼ψ⌉ := (syllogism) l₅ l₆
    let l₈ : Γ ⊢ ⌊ψ⌋|s;r| ⇒ C.insert χ₁ ⇒ C.insert χ₂ :=
      let l₁' : Γ ⊢ C.insert χ₁ ⇒ ⌈∼ψ⌉|s;r| ⋁ C.insert χ₂ := (syllogism) l₇ (permutationDisj)
      let l₂' : Γ ⊢ C.insert χ₁ ⇒ ∼⌈∼ψ⌉|s;r| ⇒ C.insert χ₂ := l₁'
      let l₃' : Γ ⊢ ∼⌈∼ψ⌉|s;r| ⇒ C.insert χ₁ ⇒ C.insert χ₂ := (permuteHyps) l₂'
      let l₄' : Γ ⊢ ⌊ψ⌋|s;r| ⇒ C.insert χ₁ ⇒ C.insert χ₂ := l₃'
      l₄'
    l₈



example {α β : Type} (a : α) (b : β) (h : HEq a b) ()
#check heq_eq_eq
-- open Classical in
noncomputable def deductionTheorem {Γ : Premises sgn} {s s' : 𝓢} {φ : Pattern sgn s} {ψ : Pattern sgn s'}
  (hψ_mu : MuClosed ψ) (hψ_exist : ExistClosed ψ)
  (proof : Γ ∪ {⟨_, ψ⟩} ⊢ φ)
  (no_kt : ¬proof.usesKnasterTarski)
  : Γ ⊢ ⌊ψ⌋ ⇒ φ :=
  match proof with
| premise hmem =>
if hmem_φ_Γ : ⟨_, φ⟩ ∈ Γ then
    let p₁ : Γ ⊢ φ := .premise hmem_φ_Γ
    (extraPremise) p₁
  else
    have h_φ_eq_ψ : HEq φ ψ := by aesop
    let l : Γ ⊢ ⌊ψ⌋ ⇒ ψ := (totalImpl)
    have : HEq (⌊ψ⌋ ⇒ φ) (⌊ψ⌋ ⇒ ψ) := by sorry
    sorry
| existQuan sfi => extraPremise (existQuan sfi)
| existence => extraPremise existence
| singleton => extraPremise <| singleton
| propagationDisj => extraPremise <| propagationDisj
| propagationExist not_fv  => extraPremise <| propagationExist not_fv
| prefixpoint wf sfi => extraPremise <| prefixpoint wf sfi
| @modusPonens _ _ _ _ _ χ χ' prf₁ prf₂ =>
  let prf₁' := prf₁.deductionTheorem hψ_mu hψ_exist (by aesop?)
  let prf₂' := prf₂.deductionTheorem hψ_mu hψ_exist (by aesop?)
  modusPonensExtraHyp prf₁' prf₂'
| @framing _ _ _ _ _ _ C χ₁ χ₂ prf =>
  let l₁ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ := prf.deductionTheorem hψ_mu hψ_exist (by aesop?)
  deductionTheoremFramingAux l₁
| @existGen _ _ _ _ _ _ χ₁ χ₂ x not_fv prf =>
  let l₁ : Γ ⊢ ⌊ψ⌋ ⇒ χ₁ ⇒ χ₂ := prf.deductionTheorem hψ_mu hψ_exist (by aesop?)
  let l₂ : Γ ⊢ χ₁ ⇒ ⌊ψ⌋ ⇒ χ₂ := permuteHyps l₁
  let l₃ : Γ ⊢ ∃∃ _ x χ₁ ⇒ ⌊ψ⌋ ⇒ χ₂ := existGen (by aesop?) l₂
  let l₄ : Γ ⊢ ⌊ψ⌋ ⇒ ∃∃ _ x χ₁ ⇒ χ₂ := permuteHyps l₃
  l₄
| knasterTarski _ prf => False.elim (by aesop?)
| @substitution _ _ _ _ _ _ χ₁ χ₂ X sfi prf =>
  let l₁ := prf.deductionTheorem hψ_mu hψ_exist (by aesop?)
  let l₂ : Γ ⊢ (⌊ψ⌋ ⇒ χ₁).substSVar X χ₂ := @substitution _ _ _ _ _ _ _ _ X (by simp [*] at * ; exact substitutable_svar_of_not_free_occ <| hψ_mu _) l₁
  have : (⌊ψ⌋ ⇒ χ₁).substSVar X χ₂ = ⌊ψ⌋.substSVar X χ₂ ⇒ χ₁.substSVar X χ₂ := by rfl
  let l₃ := this ▸ l₂
  have : ⌊ψ⌋.substSVar X χ₂ = ⌊ψ⌋ := Pattern.subst_not_free_svar _ (by aesop)
  let l₄ := this ▸ l₃
  l₄
