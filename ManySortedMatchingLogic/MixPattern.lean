import Mathlib

set_option autoImplicit false

structure EVar (S : Type) where
  name : Nat
  sort : S
  deriving DecidableEq

structure SVar (S : Type) where
  name : Nat
  sort : S
  deriving DecidableEq

structure Signature (Symbol : Type) (S : Type) where
  domain : Symbol → (Nat → S)
  target : Symbol → S
  arity : Nat

-- structure Context (S : Type) where
--   evar : EVar → S
--   svar : SVar → S

-- namespace Context

--   variable {S : Type}

--   @[simp]
--   def evarUpdate (x : EVar S) (s : S) :=
--     {ctx with evar := Function.update ctx.evar x s}

--   @[simp]
--   def svarUpdate (X : SVar S) (s : S) :=
--     {ctx with svar := Function.update ctx.svar X s}

-- end Context

inductive Pattern {Symbol : Type} {S : Type} (sgn : Signature Symbol S) : Type where
| evar : EVar S → Pattern sgn
| svar : SVar S → Pattern sgn
| implication : Pattern sgn → Pattern sgn → Pattern sgn
| application : Symbol → (Nat → Pattern sgn) → Pattern sgn
| existential : EVar S → Pattern sgn → Pattern sgn
| mu : SVar S → Pattern sgn → Pattern sgn
| bottom : Pattern sgn

section
  namespace Pattern

  variable {Symbol S : Type} {sgn : Signature Symbol S}

  infixr:60 (priority := high) " ⇒ " => implication

  infixl:65 " ⬝ " => application

  notation "∃∃ " => existential

  notation "μ " => mu

  -- def bottom {sort : S} (X : SVar S := ⟨0, sort⟩) : Pattern sgn := μ X (.svar X)

  notation (priority := high) "⊥" => bottom

  variable (φ ψ : Pattern sgn)

  @[match_pattern] def negation := φ ⇒ ⊥
  prefix:70 "∼" => negation

  def top : Pattern sgn := ∼⊥
  notation "⊤" => top

  /-- Disjunction of two patterns. -/
  @[match_pattern] def disjunction := ∼φ ⇒ ψ
  /-- Notation for `Pattern.disjunction -/
  infixl:65 " ⋁ " => disjunction

  /-- Conjunction of two patterns. -/
  @[match_pattern] def conjunction := ∼(∼φ ⋁ ∼ψ)
  /-- Notation for `Pattern.conjunction` -/
  infixl:65 " ⋀ " => conjunction

  @[match_pattern] def universal (x : EVar S) (φ : Pattern sgn) := ∼(∃∃ x (∼φ))
  /-- Notation for `Pattern.universal` -/
  notation "∀∀ " => universal

  instance : Coe (EVar S) (Pattern sgn) where
    coe := Pattern.evar

  instance : Coe (SVar S) (Pattern sgn) where
    coe := Pattern.svar

  end Pattern
end




section
  namespace Pattern

  variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

  @[simp]
  def substEVar (φ : Pattern sgn) (x : EVar S) (z : EVar S) :  Pattern sgn :=
    match φ with
    | .evar y =>
      if x = y then
        .evar x
      else
        .evar y
    | .svar X => .svar X
    | σ ⬝ args =>
      σ ⬝ (fun i => (args i).substEVar x z)
    | φ₁ ⇒ φ₂ =>
      φ₁.substEVar x z ⇒ φ₂.substEVar x z
    | ∃∃ y φ =>
      if x = y then
        ∃∃ y φ
      else
        ∃∃ y (φ.substEVar x z)
    | μ X φ => μ X (φ.substEVar x z)
    | ⊥ => ⊥
  notation φ "[" x " ⇐ᵉ " y "]" => substEVar φ x y



  @[simp]
  def substSVar (φ : Pattern sgn) (X : SVar S) (χ : Pattern sgn) : Pattern sgn :=
    match φ with
    | .evar x => .evar x
    | .svar Y =>
      if X = Y then
        χ
      else
        .svar Y
    | σ ⬝ args =>
      σ ⬝ (fun i => (args i).substSVar X χ)
    | φ₁ ⇒ φ₂ =>
      φ₁.substSVar X χ ⇒ φ₂.substSVar X χ
    | μ Y φ =>
      if X = Y then
        μ Y φ
      else
        μ Y (φ.substSVar X χ)
    | ∃∃ x φ =>
      ∃∃ x (φ.substSVar X χ)
    | ⊥ => ⊥
  notation φ "[" X " ⇐ˢ " ψ "]" => substSVar φ X ψ


  @[simp]
  def FreeEVar : EVar S → Pattern sgn → Prop :=
    fun x φ => match φ with
    | .svar _ => False
    | .evar y => x = y
    | φ₁ ⇒ φ₂ => FreeEVar x φ₁ ∨ FreeEVar x φ₂
    | σ ⬝ args => ∃ i, FreeEVar x (args i)
    -- | σ ⬝ args => ∃ i, FreeEVar x (σ ⬝ args)
    | ∃∃ y φ' => x ≠ y ∧ FreeEVar x φ'
    | μ _ φ' => FreeEVar x φ'
    | ⊥ => False

  @[simp]
  def FreeSVar : SVar S → Pattern sgn → Prop :=
    fun X φ => match φ with
    | .svar Y => X = Y
    | .evar _ => False
    | φ₁ ⇒ φ₂ => FreeSVar X φ₁ ∨ FreeSVar X φ₂
    | σ ⬝ args => ∃ i, FreeSVar X (args i)
    -- | σ ⬝ args => ∃ i, FreeSVar X (σ ⬝ args)
    | ∃∃ _ φ' => FreeSVar X φ'
    | μ Y φ' => X ≠ Y ∧ FreeSVar X φ'
    | ⊥ => False

  def svarCount (φ : Pattern sgn) (X : SVar S) : Nat := sorry

  open Classical in
  @[simp]
  def SubstitutableEVarForIn (x : EVar S) (z : EVar S) : Pattern sgn → Prop :=
    fun φ => match φ with
    | ∃∃ y φ' =>
      if (∃∃ y φ').FreeEVar x then
        z ≠ y ∧ SubstitutableEVarForIn x z φ'
      else
        True
    | μ _ φ => SubstitutableEVarForIn x z φ
    | σ ⬝ args => ∀ i, SubstitutableEVarForIn x z (args i)
    | φ₁ ⇒ φ₂ => SubstitutableEVarForIn x z φ₁ ∧ SubstitutableEVarForIn x z φ₂
    | _ => True

  open Classical in
  @[simp]
  def SubstitutableSVarForIn (X : SVar S) (χ : Pattern sgn) : Pattern sgn → Prop :=
    fun φ => match φ with
    | ∃∃ y φ' => SubstitutableSVarForIn X χ φ'
    | μ Y φ' =>
      if (μ Y φ').FreeSVar X then
        ¬χ.FreeSVar Y ∧ SubstitutableSVarForIn X χ φ'
      else
        True
    | σ ⬝ args => ∀ i, SubstitutableSVarForIn X χ (args i)
    | φ₁ ⇒ φ₂ => SubstitutableSVarForIn X χ φ₁ ∧ SubstitutableSVarForIn X χ φ₂
    | _ => True

  end Pattern
end





variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

inductive Pattern.WellSorted : Pattern sgn → S → Prop where
| evar {s} {x} : x.sort = s → WellSorted (.evar x) s
| svar {s} {X} : X.sort = s → WellSorted (.svar X) s
| implication {s} {φ ψ} : WellSorted φ s → WellSorted ψ s → WellSorted (φ ⇒ ψ) s
| application {σ} {args} {s} : (∀ i, WellSorted (args i) (sgn.domain σ i)) → WellSorted (.application σ args) s
| existential {t : S} {x : EVar S} {φ : Pattern sgn} :
  WellSorted φ t → WellSorted (∃∃ x φ) t
| mu {s} {X} {φ} : WellSorted φ s → WellSorted (μ X φ) s
| bottom {s} : WellSorted ⊥ s




section SubstitutabilityProofs
  namespace Pattern

  theorem substitutable_evar_of_not_free_occ {x : EVar S} {φ : Pattern sgn} :
    ¬FreeEVar x φ → SubstitutableEVarForIn x x φ := by
    intros hnfv
    induction φ
    all_goals (aesop)



  theorem substitutable_evar_same (x : EVar S) (φ : Pattern sgn) : SubstitutableEVarForIn x x φ := by
    induction φ with
    | evar y =>
      by_cases h : x = y
      . simp [*] at *
      . simp [*] at *
    | existential y φ' ih =>
      by_cases h : (∃∃ y φ').FreeEVar x
      . by_cases h' : y = x
        . aesop
        . aesop
      . apply substitutable_evar_of_not_free_occ h
    | _ => simp [*] at *

  @[simp]
  theorem subst_var_var_eq_self_evar (φ : Pattern sgn) (x : EVar S) : φ.substEVar x x = φ := by
    induction φ with
    | evar y =>
      by_cases h : x = y <;> simp [*]
    | _ => simp [*]

    done


  theorem substitutable_svar_of_not_free_occ {φ : Pattern sgn} {ψ : Pattern sgn} {X : SVar S} :
    ¬φ.FreeSVar X → SubstitutableSVarForIn X ψ φ := by
    intros h
    induction φ with
    | mu Y φ' ih =>
      -- simp at *
      -- specialize ih h
      by_cases h' : X = Y
      . simp [*]
      . aesop
    | implication φ₁ φ₂ ih₁ ih₂ =>
      aesop
    | application σ φ ih =>
      aesop
    | existential y φ' ih =>
      simp [*] at * -- why is simp
      simp [*] at *
    | _ => simp

  -- theorem substitutable_svar_into_closed {φ ψ : Pattern 𝕊} {X : SVar} : φ.muClosed → ψ.substitutableForSvarIn X φ :=
  --   fun h => substitutable_svar_of_not_free_occ <| h _

  -- theorem substitutable_svar_of_closed {φ ψ : Pattern 𝕊} {X : SVar} : ψ.muClosed ∧ ψ.existClosed → ψ.substitutableForSvarIn X φ := by
  --   intros h
  --   cases h with | intro h₁ h₂ =>
  --   induction φ with
  --   | mu Y φ' ih =>
  --     by_cases h' : X = Y
  --     . simp [*]
  --     . specialize h₁ Y
  --       simp [*]
  --   | existential y φ' ih =>
  --     specialize h₂ y
  --     by_cases h' : φ'.isFreeSvar X
  --     . simp [*] at *
  --     . simp [*] at *
  --   | _ => simp [*] at *



  theorem substitutable_svar_of_mu {φ : Pattern sgn} {ψ : Pattern sgn} {X Y : SVar S} :
    X ≠ Y → SubstitutableSVarForIn X ψ (μ Y φ) → SubstitutableSVarForIn X ψ φ :=
  by
    intros h
    by_cases h' : (μ Y φ).FreeSVar X
    . intros
      aesop?
      -- simp_all only [ne_eq, isFreeSvar, ite_false, substitutableForSvarIn, Bool.not_eq_true, Bool.decide_and,
      --   Bool.decide_coe, ite_true, Bool.and_eq_true, decide_eq_true_eq]
    . induction φ with
      | mu Z φ' ih =>
        intros h''
        by_cases hXY : X = Y <;> by_cases hYZ : Y = Z
        . simp [*] at *
        . simp [*] at *
        . by_cases hfv : FreeSVar X φ'
          . simp [*] at *
            -- simp only [*,, isFreeSvar, ite_eq_right_iff, Bool.not_eq_true, not_forall, exists_prop,
            -- and_true, Bool.decide_and, Bool.decide_coe, Bool.and_eq_true, decide_eq_true_eq, ne_eq, not_false_eq_true, IsEmpty.forall_iff, ite_false, and_self, forall_true_left] at *
            -- why is `simp` not idempotent? -- why is `simp` not idempotent?
            aesop
          . simp [*] at *
        . by_cases hfv : FreeSVar X φ'
          . simp [*] at *
            simp [*] at *
          . simp [*] at *
      | implication φ₁ φ₂ ih₁ =>
        -- simp? [*] at *

        -- specialize ih₁ h'.1
        -- specialize ih₂ h'.2
        by_cases hfv : FreeSVar X ψ
        . rename_i s_1
          intro a
          aesop?
          -- apply And.intro
          -- · apply ih₁
          --   apply Aesop.BuiltinRules.not_intro
          --   intro a
          --   simp_all only [not_true, implies_true, SubstitutableSVarForIn._eq_5, IsEmpty.forall_iff, true_or]
          -- · apply ih₂
          --   apply Aesop.BuiltinRules.not_intro
          --   intro a
          --   simp_all only [not_true, implies_true, SubstitutableSVarForIn._eq_5, IsEmpty.forall_iff, or_true]
        . aesop
      | application σ φ ih =>
        aesop?
      | existential x φ' ih =>
        -- simp only [*, substitutableForSvarIn, isFreeSvar, ite_false, Bool.not_eq_true, Bool.decide_and, Bool.decide_coe,
        --   ite_eq_right_iff, Bool.and_eq_true, decide_eq_true_eq, h] at *
        -- specialize ih h'
        by_cases hfv : FreeSVar X ψ
        . aesop
        . aesop
      | _ => simp [*] at *


#check cast_eq

  @[simp]
  theorem subst_var_var_eq_self_svar (φ : Pattern sgn) (X : SVar S) : φ.substSVar X (.svar X) = φ := by
    induction φ with
    | svar Y =>
      by_cases h' : X = Y <;> simp [*]
    | _ => simp [*]

  @[simp]
  theorem subst_not_free_svar {φ : Pattern sgn} {X : SVar S} (ψ : Pattern sgn) (not_fv : ¬φ.FreeSVar X) : φ.substSVar X ψ = φ := by
    induction φ
    all_goals aesop
    -- | svar r Y =>
    --   -- by_cases h : r = t
    --   aesop
    -- | mu Y φ' ih =>
    --   by_cases h : X = Y
    --   . aesop
    --   . aesop
    -- | implication φ' φ'' ih' ih'' | application φ' φ'' ih' ih'' =>
    --   aesop
    -- | existential _ φ' ih' =>
    --   aesop
    -- | _ => simp [*]


  -- #check heq_of_cast_eq
  end Pattern
end SubstitutabilityProofs



section WellSortednessProofs

  open Pattern

  @[simp]
  lemma well_sorted_evar {x : EVar S} {s : S} : WellSorted (.evar x : Pattern sgn) s ↔ x.sort = s := by
    constructor
    . intros h ; cases h ; assumption
    . intros h ; constructor ; assumption

  @[simp]
  lemma well_sorted_svar {X : SVar S} {s : S} : WellSorted (.svar X : Pattern sgn) s ↔ X.sort = s := by
    constructor
    . intros h ; cases h ; assumption
    . intros h ; constructor ; assumption

  @[simp]
  lemma well_sorted_implication {φ ψ : Pattern sgn} {s} : WellSorted (φ ⇒ ψ) s ↔ WellSorted φ s ∧ WellSorted ψ s := by
    constructor
    . intros h ; cases h ; aesop
    . intros h ; constructor <;> aesop

  @[simp]
  lemma well_sorted_application {σ : Symbol} {args : Nat → Pattern sgn} {s : S} : WellSorted (σ ⬝ args) s ↔ ∀ i, WellSorted (args i) (sgn.domain σ i) := by
    constructor
    . intros h ; intros i ; cases h ; aesop
    . intros h ; constructor ; assumption

  @[simp]
  lemma well_sorted_existential {x : EVar S} {φ : Pattern sgn} {t : S} :  WellSorted (∃∃ x φ) t ↔ WellSorted φ t := by
    constructor
    . intros h ; cases h ; assumption
    . intros h ; apply WellSorted.existential h


  @[simp]
  lemma well_sorted_mu {X : SVar S} {φ : Pattern sgn} {s : S} :  WellSorted φ s ↔ WellSorted (μ X φ) s := by
    constructor
    . intros h ; constructor ; assumption
    . intros h ; cases h ; assumption

  @[simp]
  lemma well_sorted_bottom {s : S} : WellSorted (⊥ : Pattern sgn) s := by constructor


  lemma unique_sorted {φ : Pattern sgn} {s₁ s₂ : S} :
    WellSorted φ s₁ → WellSorted φ s₂ → s₁ = s₂ := by
    intros h₁ h₂
    induction φ with
    | application σ args ih =>
      -- specialize ih 0
      sorry

    | _ => sorry

  @[simp]
  lemma subst_evar_well_sorted (φ : Pattern sgn) (x : EVar S) (z : EVar S) (s : S) :
    WellSorted φ s → WellSorted (φ.substEVar x z) s := by
    intros h
    induction φ generalizing s with
    | evar y =>
      by_cases h' : x = y
      . aesop
      . aesop
    | svar Y =>
      aesop
    | implication φ₁ φ₂ ih₁ ih₂ =>
      aesop
    | application σ args ih =>
      aesop
    | existential y φ ih =>
      by_cases h' : x = y
      . aesop
      . rw [well_sorted_existential] at h
        specialize @ih
        have : Pattern.substEVar (∃∃ y φ) x z = ∃∃ y (Pattern.substEVar φ x z) := by simp [*]
        rw [this]
        constructor
        specialize ih _ h
        assumption
    | mu Y φ ih =>
      rw [← well_sorted_mu] at h
      constructor
      specialize @ih _ h
      assumption
    | bottom =>
      simpa

  lemma subst_svar_well_sorted {φ : Pattern sgn} (X : SVar S) {χ : Pattern sgn} {s t : S} :
    WellSorted φ s →
    WellSorted χ t →
    X.sort = t →
    Pattern.SubstitutableSVarForIn X χ φ →
    WellSorted (φ.substSVar X χ) s :=
  by
    intros h hχ hsub
    -- sorry
    induction φ generalizing s with
    | svar Y =>
      by_cases h' : X = Y
      . aesop
      . aesop
    | mu Y φ ih =>
      by_cases h' : X = Y
      . aesop
      . intros hsub
        by_cases h'' : φ.FreeSVar X
        . have : ¬Pattern.FreeSVar Y χ ∧ Pattern.SubstitutableSVarForIn X χ φ := by aesop
          rw [← well_sorted_mu] at h
          specialize ih h this.2
          simp only [Pattern.substSVar, ite_false, *]
          constructor
          assumption
        . have : ¬(μ Y φ).FreeSVar X := by aesop
          rw [Pattern.subst_not_free_svar _ this]
          exact h
    | application σ args ih =>
      intros hsub
      aesop
    | implication φ₁ φ₂ ih₁ ih₂ =>
      aesop
    | existential x φ' ih =>
      intros hsub
      rw [well_sorted_existential] at h
      specialize ih h hsub
      simp only [Pattern.substSVar]
      constructor
      assumption
    | evar =>
      aesop
    | bottom =>
      aesop


end WellSortednessProofs


mutual
  inductive NegativeOcc : SVar S → Pattern sgn → Prop where
  | implication_left {X} {φ₁ φ₂} :
    PositiveOcc X φ₁ → NegativeOcc X (φ₁ ⇒ φ₂)
  | implication_right {X} {φ₁ φ₂} :
    NegativeOcc X φ₂ → NegativeOcc X (φ₁ ⇒ φ₂)
  | application {X} {σ} {φ : Nat → Pattern sgn} {i} :
    NegativeOcc X (φ i) → NegativeOcc X (σ ⬝ φ)
  | existential {X} {y} {φ} :
    NegativeOcc X φ → NegativeOcc X (∃∃ y φ)
  | mu {X} {Y} {φ} :
    NegativeOcc X φ → X ≠ Y → NegativeOcc X (μ Y φ)

  inductive PositiveOcc : SVar S → Pattern sgn → Prop where
  | svar {X} :
    PositiveOcc X (.svar X)
  | implication_left {X} {φ₁ φ₂} :
    NegativeOcc X φ₁ → PositiveOcc X (φ₁ ⇒ φ₂)
  | implication_right {X} {φ₁ φ₂} :
    PositiveOcc X φ₂ → PositiveOcc X (φ₁ ⇒ φ₂)
  | application {X} {σ} {φ : Nat → Pattern sgn} {i} :
    PositiveOcc X (φ i) → PositiveOcc X (σ ⬝ φ)
  | existential {X} {y} {φ} :
    PositiveOcc X φ → PositiveOcc X (∃∃ y φ)
  | mu {X} {Y} {φ} :
    PositiveOcc X φ → X ≠ Y → PositiveOcc X (μ Y φ)
end







structure AppContext (sgn : Signature Symbol S) where
  hole : ℕ
  symbol : Symbol
  args : ℕ → Pattern sgn
  args_well_sorted : ∀ i, i ≠ hole → Pattern.WellSorted (args i) (sgn.domain symbol i)

def AppContext.holeSort (C : AppContext sgn) : S :=
  sgn.domain C.symbol C.hole

def AppContext.target (C : AppContext sgn) : S :=
  sgn.target C.symbol

def AppContext.insert (C : AppContext sgn) (φ : Pattern sgn) : Pattern sgn :=
  C.symbol ⬝ Function.update C.args C.hole φ

@[simp]
theorem AppContext.well_sorted_insert {C : AppContext sgn} {φ : Pattern sgn} {s t} : s = C.holeSort → Pattern.WellSorted φ s → Pattern.WellSorted (C.insert φ) t := by
  intros h h'
  constructor
  intros i
  by_cases h'' : i = C.hole
  . simp [Function.update, *]
    aesop
  . simp [Function.update, *]
    have := C.args_well_sorted i
    aesop

def AppContext.FreeEVar (C : AppContext sgn) (x : EVar S) : Prop :=
  ∃ i, i ≠ C.hole ∧ (C.args i).FreeEVar x

theorem AppContext.insert_not_free_evar {x : EVar S} {C : AppContext sgn} {φ : Pattern sgn} :
  ¬φ.FreeEVar x → ¬C.FreeEVar x → ¬(C.insert φ).FreeEVar x := by
  intros hφ hC
  unfold AppContext.FreeEVar at hC
  push_neg at hC
  intros h
  simp [AppContext.insert, Function.update] at h
  rcases h with ⟨i, h⟩
  specialize hC i
  by_cases h' : i = C.hole
  . simp_all
  . simp_all

theorem AppContext.insert_not_free_evar_mpr {x : EVar S} {C : AppContext sgn} {φ : Pattern sgn} :
  ¬(C.insert φ).FreeEVar x → ¬φ.FreeEVar x ∧ ¬C.FreeEVar x := by
  intros h
  constructor
  . intros h'
    simp [AppContext.insert, Function.update] at h
    specialize h C.hole
    simp at h
    contradiction
  . intros h'
    simp [AppContext.FreeEVar] at h'
    rcases h' with ⟨i, h'⟩
    simp [AppContext.insert, Function.update] at h
    specialize h i
    by_cases h'' : i = C.hole
    . simp_all
    . simp_all


def WSPattern (sgn : Signature Symbol S) (s : S) : Type := {φ : Pattern sgn // φ.WellSorted s}

def WSAppContext (sgn : Signature Symbol S) (s t : S) : Type := {C : AppContext sgn // C.holeSort = s ∧ C.target = t}

inductive NestedContext (sgn : Signature Symbol S) where
| empty (source : S) : NestedContext sgn
| nest : AppContext sgn → NestedContext sgn → NestedContext sgn

inductive NestedContext.WellSorted : NestedContext sgn → S → Prop where
| empty {s} : NestedContext.WellSorted (.empty s) s
| nest {Cσ} {C} {s t} : NestedContext.WellSorted C s → Cσ.holeSort = s → Cσ.target = t → NestedContext.WellSorted (.nest Cσ C) t

@[simp]
def NestedContext.insert (C : NestedContext sgn) (φ : Pattern sgn) : Pattern sgn :=
  match C with
  | .empty _ => φ
  | .nest Cσ C => Cσ.insert (C.insert φ)

theorem NestedContext.nest_insert (Cσ : AppContext sgn) (C : NestedContext sgn) (φ : Pattern sgn ) :
  (NestedContext.nest Cσ C).insert φ = Cσ.insert (C.insert φ) := rfl

/-- Notation for `Nested.insert`-/
notation C "[" φ "]" => NestedContext.insert C φ
/-- Notation for `Nested.empty` -/
notation "□" => NestedContext.empty

@[simp]
def NestedContext.FreeEVar (x : EVar S) (C : NestedContext sgn) : Prop :=
  match C with
  | .empty _ => False
  | .nest Cσ C => Cσ.FreeEVar x ∨ C.FreeEVar x

@[simp]
def NestedContext.holeSort (C : NestedContext sgn) : S :=
  match C with
  | .empty s  => s
  | .nest Cσ C => C.holeSort

@[simp]
def NestedContext.target (C : NestedContext sgn) : S :=
  match C with
  | .empty t => t
  | .nest Cσ C => Cσ.target

theorem NestedContext.well_sorted_insert (C : NestedContext sgn) (φ : Pattern sgn) {s t} :
  C.WellSorted t → φ.WellSorted s → C.holeSort = s → (C[φ]).WellSorted t := by
  intros wsC wsφ hole_sort
  induction wsC generalizing s with
  | empty =>
    simp_all
  | @nest Cσ C' s₁ s₂ wsC' h₁ h₂ ih =>
    specialize ih wsφ
    simp at hole_sort
    specialize ih hole_sort
    simp_all
    apply AppContext.well_sorted_insert (s := s₁) h₁.symm ih






-- structure AppContext (sgn : Signature Symbol S) where
--   hole : SVar S
--   pattern : Pattern sgn
--   is_linear : True
--   is_app : True

-- def AppContext.insert (C : AppContext sgn) (φ : Pattern sgn) : Pattern sgn := sorry
