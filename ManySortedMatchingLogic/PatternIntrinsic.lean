import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Classical
-- structure Arity (𝓢 : Type) where
--   arity : Nat
--   args : Fin arity → 𝓢
--   target : 𝓢

-- def Signature (𝕊 𝓢 : Type) := 𝕊 → Arity 𝓢

-- abbrev EVar {𝓢 : Type} (s : 𝓢) := String
-- abbrev SVar {𝓢 : Type} (s : 𝓢) := String


--  @[simp]
--   def getFresh : List ℕ → ℕ
--   | [] => 0
--   | .cons x xs => (max x (getFresh xs)) + 1

--   theorem lt_get_fresh {xs : List ℕ} {x : ℕ} (h : x ∈ xs) : x < getFresh xs := by
--     induction xs with
--     | nil => simp at h
--     | cons hd tl ih =>
--       cases h with
--       | head =>
--         dsimp
--         have : x ≤ max x (getFresh tl) := le_max_left x (getFresh tl)
--         exact Nat.lt_succ_of_le this
--       | tail _ hmem =>
--         dsimp
--         specialize ih hmem
--         have : getFresh tl ≤ max hd (getFresh tl) := le_max_right hd (getFresh tl)
--         have := le_trans (le_of_lt ih) this
--         exact Nat.lt_succ_of_le this




--   theorem get_fresh_is_fresh (xs : List ℕ) : getFresh xs ∉ xs :=
--     fun h => lt_irrefl _ $ lt_get_fresh h

--   theorem get_fresh_is_fresh' (xs : List ℕ) : ∀ x ∈ xs, getFresh xs ≠ x := by
--     intros x hmem h
--     have := get_fresh_is_fresh xs
--     subst h
--     contradiction




-- structure EVar {𝓢 : Type} (s : 𝓢) where
--   name : Nat
--   deriving DecidableEq


-- namespace EVar

--   def same {𝓢 : Type} {s t : 𝓢} (x : EVar s) (y : EVar t) : Prop :=
--     ∃ h : s = t, x = (cast (by rw [h]) y)


-- -- theorem EVar.eq_sorts_of_heq {x : EVar s} {y : EVar t} : HEq x y → s = t := by
-- --   intros h
-- --   have : EVar s = EVar t := by exact type_eq_of_heq h
-- --   cases x
-- --   cases y

-- end EVar

-- structure SVar {𝓢 : Type} (s : 𝓢) where
--   name : Nat
--   deriving DecidableEq

-- def SVar.same {𝓢 : Type} {s t : 𝓢} (X : SVar s) (Y : SVar t) : Prop :=
--   ∃ h : s = t, X = (cast (by rw [h]) Y)

-- #check HEq

structure EVar where
  name : ℕ
  deriving DecidableEq

structure SVar where
  name : ℕ
  deriving DecidableEq

inductive PSort (𝓢 : Type) where
| base : 𝓢 → PSort 𝓢
| arrow : PSort 𝓢 → PSort 𝓢 → PSort 𝓢
  deriving DecidableEq

infixr:65 "↣" => PSort.arrow

instance {𝓢 : Type} : Coe 𝓢 (PSort 𝓢) where
  coe := PSort.base

structure Symbol (𝓢 : Type) where
  name : String
  domain : 𝓢
  target : 𝓢


def NArySort {𝓢 : Type} (domain : List 𝓢) (target : 𝓢) : PSort 𝓢 :=
  (domain ++ [target]).foldr (init := .base <| (domain ++ [target]).head (by simp)) (fun s t => .base s ↣ t)

abbrev Signature (𝓢 : Type) := Set (Symbol 𝓢)


inductive Pattern {𝓢 : Type} (sgn : Signature 𝓢) : PSort 𝓢 → Type _ where
  | evar (s) : EVar → Pattern sgn s
  | svar (s) : SVar → Pattern sgn s
  | implication {s} : Pattern sgn s → Pattern sgn s → Pattern sgn s
  | symbol (σ : Symbol 𝓢) : Pattern sgn (σ.domain ↣ σ.target)
  | application {s t : PSort 𝓢} : Pattern sgn (s ↣ t) → Pattern sgn s → Pattern sgn t
  -- | application (σ : 𝕊) : ((i : Fin σ.arity) → Pattern sgn (σ.domain i)) → Pattern sgn (sgn.target σ)
  -- | application {arity : Nat} : 𝕊 → (Fin arity → Pattern sgn 𝓢) → Pattern sgn 𝓢
  | existential {s} (s' : PSort 𝓢) : EVar → Pattern sgn s → Pattern sgn s
  | mu {s} : SVar → Pattern sgn s → Pattern sgn s
  | bottom {s} : Pattern sgn s

namespace Pattern

section
  variable {𝕊 𝓢 : Type}

  infixr:60 (priority := high) " ⇒ " => implication

  infixl:80 " ⬝ " => application

  notation "μ" => mu

  notation "∃∃" => existential

  notation "⊥" => bottom

  variable {sgn : Signature 𝓢} {s t : PSort 𝓢} (φ ψ : Pattern sgn s)

  @[match_pattern] def negation := φ ⇒ ⊥
  prefix:70 "∼" => negation

  notation "⊤" => ∼⊥

  /-- Disjunction of two patterns. -/
  @[match_pattern] def disjunction := ∼φ ⇒ ψ
  /-- Notation for `Pattern.disjunction -/
  infixl:65 " ⋁ " => disjunction

  /-- Conjunction of two patterns. -/
  @[match_pattern] def conjunction := ∼(∼φ ⋁ ∼ψ)
  /-- Notation for `Pattern.conjunction` -/
  infixl:65 " ⋀ " => conjunction

  @[match_pattern] def universal (t : PSort 𝓢) (x : EVar) (φ : Pattern sgn s) := ∼(∃∃ t x (∼φ))
  /-- Notation for `Pattern.universal` -/
  notation "∀∀ " => universal

  instance : Coe (EVar) (Pattern sgn s) where
    coe := Pattern.evar s

  instance : Coe (SVar) (Pattern sgn s) where
    coe := Pattern.svar s

end

variable {𝕊 𝓢 : Type} [DecidableEq 𝓢] {sgn : Signature 𝓢}

-- def size {s : 𝓢} : Pattern sgn s → Nat
--   | .evar _ => 1
--   | .svar _ => 1
--   | φ₁ ⇒ φ₂ => φ₁.size + φ₂.size + 1
--   | .application σ arity s t args =>

-- def evars : ∀ {s : 𝓢}, Pattern sgn s → List (Σ t : 𝓢, EVar t) :=
--   fun φ => match φ with
--   | .evar x => [⟨_, x⟩]
--   | _ => _

@[simp]
def substEVar : ∀ {s : PSort 𝓢}, Pattern sgn s → EVar → EVar → Pattern sgn s :=
  @fun s φ x z => match φ with
  | .evar r y =>
    if x = y then
      .evar r x
    else
      .evar r y
  | .svar _ X => .svar _ X
  | φ₁ ⬝ φ₂ =>
    φ₁.substEVar x z ⬝ φ₂.substEVar x z
  | φ₁ ⇒ φ₂ =>
    φ₁.substEVar x z ⇒ φ₂.substEVar x z
  | ∃∃ r y φ =>
    if x = y then
      ∃∃ r y φ
    else
      ∃∃ r y (φ.substEVar x z)
  | μ X φ => μ X (φ.substEVar x z)
  | .bottom => ⊥
  | .symbol σ => .symbol σ

notation φ "[" x " ⇐ᵉ " y "]" => substEVar φ x y


@[simp]
def substSVar : ∀ {s t : PSort 𝓢}, Pattern sgn s → SVar → Pattern sgn t → Pattern sgn s :=
  @fun s t φ X χ => match φ with
  | .evar _ x => .evar _ x
  | .svar r Y =>
    if h : r = t ∧ X = Y then
      cast (by rw [h.1]) χ
    else
      .svar r Y
  | φ₁ ⬝ φ₂ =>
    φ₁.substSVar X χ ⬝ φ₂.substSVar X χ
  | φ₁ ⇒ φ₂ =>
    φ₁.substSVar X χ ⇒ φ₂.substSVar X χ
  | μ Y φ =>
    if X = Y then
      μ Y φ
    else
      μ Y (φ.substSVar X χ)
  | ∃∃ r x φ =>
    ∃∃ r x (φ.substSVar X χ)
  | .bottom => ⊥
  | .symbol σ => .symbol σ

notation φ "[" X " ⇐ˢ " ψ "]" => substSVar φ X ψ



-- inductive FreeEVar : ∀ {s : PSort 𝓢}, EVar → Pattern sgn s → Prop where
-- | evar {r} {x} : FreeEVar x (.evar r x)
-- | implication_left {x} {φ₁ φ₂} : FreeEVar x φ₁ → FreeEVar x (φ₁ ⇒ φ₂)
-- | implication_right {x} {φ₁ φ₂} : FreeEVar x φ₂ → FreeEVar x (φ₁ ⇒ φ₂)
-- | application_left {x} {φ₁ φ₂} : FreeEVar x φ₁ → FreeEVar x (φ₁ ⬝ φ₂)
-- | application_right {x} {φ₁ φ₂} : FreeEVar x φ₂ → FreeEVar x (φ₁ ⬝ φ₂)
-- | mu {x} {Y} {φ} : FreeEVar x φ → FreeEVar x (μ Y φ)
-- | existential {r} {x} {y} {φ} : FreeEVar x φ → x ≠ y → FreeEVar x (∃∃ r y φ)

@[simp]
def FreeEVar : ∀ {s}, EVar → Pattern sgn s → Prop :=
  fun x φ => match φ with
  | .evar r y => x = y
  | .svar _ _ => False
  | φ₁ ⇒ φ₂ => FreeEVar x φ₁ ∨ FreeEVar x φ₂
  | φ₁ ⬝ φ₂ => FreeEVar x φ₁ ∨ FreeEVar x φ₂
  -- | σ ⬝ args => ∃ i, FreeEVar x (σ ⬝ args)
  | ∃∃ r y φ' => x ≠ y ∧ FreeEVar x φ'
  | μ Y φ' => FreeEVar x φ'
  | .bottom => False
  | _ => False

  theorem exists_binds {s t : 𝓢} (φ : Pattern sgn s) (x : EVar) : ¬(∃∃ t x φ).FreeEVar x := by
    aesop


-- theorem free_evar_exist {t r : PSort 𝓢} {x : EVar} {y : EVar} {φ : Pattern sgn r} : FreeEVar x (∃∃ t y φ) ↔ FreeEVar x φ ∧ x ≠ y := by
--   constructor <;> (intros h ; cases h ; constructor <;> assumption)



-- theorem free_evar_implication {s t : PSort 𝓢} {x : EVar} {φ ψ : Pattern sgn t} : FreeEVar x (φ ⇒ ψ) ↔ FreeEVar x φ ∨ FreeEVar x ψ := by
--   constructor <;> intros h <;> cases h
--   . apply Or.inl ; assumption
--   . apply Or.inr ; assumption
--   . apply FreeEVar.implication_left ; assumption
--   . apply FreeEVar.implication_right ; assumption


-- theorem free_evar_application {t r : PSort 𝓢} {x : EVar} {φ : Pattern sgn (t ↣ r)} {ψ : Pattern sgn (t)} : FreeEVar x (φ ⬝ ψ) ↔ FreeEVar x φ ∨ FreeEVar x ψ := by
--   constructor <;> intros h <;> cases h
--   . apply Or.inl ; assumption
--   . apply Or.inr ; assumption
--   . apply FreeEVar.application_left ; assumption
--   . apply FreeEVar.application_right ; assumption

-- theorem free_evar_symbol {x : EVar} {σ : Symbol 𝓢} : ¬FreeEVar x (Pattern.symbol σ (sgn := sgn)) := by
--   intros h ; cases h

-- inductive FreeSVar : ∀ {s : PSort 𝓢}, SVar → Pattern sgn s → Prop where
-- | svar {r} {X} : FreeSVar X (.svar r X)
-- | implication_left {X} {φ₁ φ₂} : FreeSVar X φ₁ → FreeSVar X (φ₁ ⇒ φ₂)
-- | implication_right {X} {φ₁ φ₂} : FreeSVar X φ₂ → FreeSVar X (φ₁ ⇒ φ₂)
-- | application_left {X} {φ₁ φ₂} : FreeSVar X φ₁ → FreeSVar X (φ₁ ⬝ φ₂)
-- | application_right {X} {φ₁ φ₂} : FreeSVar X φ₂ → FreeSVar X (φ₁ ⬝ φ₂)
-- | existential {r} {X} {x} {φ} : FreeSVar X φ → FreeSVar X (∃∃ x r φ)
-- | mu {X} {Y} {φ} : FreeSVar X φ → X ≠ Y → FreeSVar X (μ Y φ)

@[simp]
def FreeSVar : ∀ {s}, SVar → Pattern sgn s → Prop :=
  fun X φ => match φ with
  | .svar r Y => X = Y
  | .evar _ _ => False
  | φ₁ ⇒ φ₂ => FreeSVar X φ₁ ∨ FreeSVar X φ₂
  | φ₁ ⬝ φ₂ => FreeSVar X φ₁ ∨ FreeSVar X φ₂
  -- | σ ⬝ args => ∃ i, FreeSVar X (σ ⬝ args)
  | ∃∃ r y φ' => FreeSVar X φ'
  | μ Y φ' => X ≠ Y ∧ FreeSVar X φ'
  | .bottom => False
  | _ => False

def countSVar {s} (X : SVar) : Pattern sgn s → ℕ
  | .svar _ Y => if Y = X then 1 else 0
  | .evar _ _ => 0
  | φ₁ ⇒ φ₂ => φ₁.countSVar X + φ₂.countSVar X
  | φ₁ ⬝ φ₂ => φ₁.countSVar X + φ₂.countSVar X
  | ∃∃ r y φ' => φ'.countSVar X
  | μ Y φ' => φ'.countSVar X
  | .bottom => 0
  | .symbol _ => 0

def MuClosed {s : PSort 𝓢} (φ : Pattern sgn s) : Prop :=
  ∀ X : SVar, ¬φ.FreeSVar X

def ExistClosed {s : PSort 𝓢} (φ : Pattern sgn s) : Prop :=
  ∀ x : EVar, ¬φ.FreeEVar x

-- inductive SubstitutableSVarForIn : ∀ {s t : PSort 𝓢} (X : SVar) (χ : Pattern sgn t), Pattern sgn s → Prop where
-- | evar {X} {χ} {y} :
--   SubstitutableSVarForIn X χ (.evar y)
-- | svar {X} {χ} {Y} :
--   SubstitutableSVarForIn X χ (.svar Y)
-- | mu {X} {χ} {Y} {φ} :
--   FreeSVar X (μ Y φ) → ¬FreeSVar Y χ → SubstitutableSVarForIn X χ φ → SubstitutableSVarForIn X χ (μ Y φ)
-- | mu_shadowing {X} {χ} {Y} {φ} :
--   ¬FreeSVar X (μ Y φ) → SubstitutableSVarForIn X χ (μ Y φ)
-- | existential {X} {χ} {y} {φ} :
--   FreeSVar X (∃∃ y φ) → ¬FreeEVar y χ → SubstitutableSVarForIn X χ φ → SubstitutableSVarForIn X χ (∃∃ y φ)
-- | existential_shadowing {X} {χ} {y} {φ} :
--   ¬FreeSVar X (∃∃ y φ) → SubstitutableSVarForIn X χ (∃∃ y φ)
-- | implication {X} {χ} {φ₁ φ₂} :
--   SubstitutableSVarForIn X χ φ₁ → SubstitutableSVarForIn X χ φ₂ → SubstitutableSVarForIn X χ (φ₁ ⇒ φ₂)
-- | application {X} {χ} {φ₁ φ₂} :
--   SubstitutableSVarForIn X χ φ₁ → SubstitutableSVarForIn X χ φ₂ → SubstitutableSVarForIn X χ (φ₁ ⬝ φ₂)

@[simp]
def SubstitutableSVarForIn : ∀ {s t : PSort 𝓢} (X : SVar) (χ : Pattern sgn t), Pattern sgn s → Prop :=
  fun X χ φ => match φ with
  | ∃∃ r y φ' => SubstitutableSVarForIn X χ φ'
  | μ Y φ' =>
    if (μ Y φ').FreeSVar X then
      ¬FreeSVar Y χ ∧ SubstitutableSVarForIn X χ φ'
    else
      True
  | φ₁ ⬝ φ₂ | φ₁ ⇒ φ₂ => SubstitutableSVarForIn X χ φ₁ ∧ SubstitutableSVarForIn X χ φ₂
  | _ => True

-- inductive SubstitutableEVarForIn : ∀ {s : PSort 𝓢} (x : EVar) (z : EVar), Pattern sgn s → Prop where
-- | evar {r} {x} {z} {y} :
--   SubstitutableEVarForIn x z (.evar r y)
-- | svar {r} {x} {z} {Y} :
--   SubstitutableEVarForIn x z (.svar r Y)
-- | existential {r} {x} {z} {s : PSort 𝓢} {s' : PSort 𝓢} {y : EVar} {φ : Pattern sgn s} :
--   y ≠ z → FreeEVar x (∃∃ r y φ) → SubstitutableEVarForIn x z φ → SubstitutableEVarForIn x z (∃∃ r y φ)
-- | existential_shadowing {x} {z} {y} {φ} :
--   ¬FreeEVar x (∃∃ _ y φ) → SubstitutableEVarForIn x z (∃∃ _ y φ)
-- | mu {x} {z} {Y} {φ} :
--   FreeEVar x (μ Y φ) → SubstitutableEVarForIn x z φ → SubstitutableEVarForIn x z (μ Y φ)
-- | mu_shadowing {x} {z} {Y} {φ} :
--   ¬FreeEVar x (μ Y φ) → SubstitutableEVarForIn x z (μ Y φ)
-- | implication {x} {z} {φ₁ φ₂} :
--   SubstitutableEVarForIn x z φ₁ → SubstitutableEVarForIn x z φ₂ → SubstitutableEVarForIn x z (φ₁ ⇒ φ₂)
-- | application {x} {z} {φ₁ φ₂} :
--   SubstitutableEVarForIn x z φ₁ → SubstitutableEVarForIn x z φ₂ → SubstitutableEVarForIn x z (φ₁ ⬝ φ₂)

@[simp]
def SubstitutableEVarForIn : ∀ {s : PSort 𝓢} (x : EVar) (z : EVar), Pattern sgn s → Prop :=
  fun x z φ => match φ with
  | ∃∃ r y φ' =>
    if (∃∃ r y φ').FreeEVar x then
      z ≠ y ∧ SubstitutableEVarForIn x z φ'
    else
      True
  | μ _ φ => SubstitutableEVarForIn x z φ
  | φ₁ ⬝ φ₂ | φ₁ ⇒ φ₂ => SubstitutableEVarForIn x z φ₁ ∧ SubstitutableEVarForIn x z φ₂
  | _ => True



mutual
  inductive NegativeOcc : ∀ {s : PSort 𝓢}, SVar → Pattern sgn s → Prop where
  | implication_left {X} {φ₁ φ₂} :
    PositiveOcc X φ₁ → NegativeOcc X (φ₁ ⇒ φ₂)
  | implication_right {X} {φ₁ φ₂} :
    NegativeOcc X φ₂ → NegativeOcc X (φ₁ ⇒ φ₂)
  | application_left {X} {φ₁ φ₂} :
    NegativeOcc X φ₁ → NegativeOcc X (φ₁ ⬝ φ₂)
  | application_right {X} {φ₁ φ₂} :
    NegativeOcc X φ₂ → NegativeOcc X (φ₁ ⬝ φ₂)
  | existential {X} {y} {φ} :
    NegativeOcc X φ → NegativeOcc X (∃∃ y _ φ)
  | mu {X} {Y} {φ} :
    NegativeOcc X φ → X ≠ Y → NegativeOcc X (μ Y φ)

  inductive PositiveOcc : ∀ {s : PSort 𝓢}, SVar → Pattern sgn s → Prop where
  | svar {X} :
    PositiveOcc X (.svar _ X)
  | implication_left {X} {φ₁ φ₂} :
    NegativeOcc X φ₁ → PositiveOcc X (φ₁ ⇒ φ₂)
  | implication_right {X} {φ₁ φ₂} :
    PositiveOcc X φ₂ → PositiveOcc X (φ₁ ⇒ φ₂)
  | application_left {X} {φ₁ φ₂} :
    PositiveOcc X φ₁ → PositiveOcc X (φ₁ ⬝ φ₂)
  | application_right {X} {φ₁ φ₂} :
    PositiveOcc X φ₂ → PositiveOcc X (φ₁ ⬝ φ₂)
  | existential {X} {y} {φ} :
    PositiveOcc X φ → PositiveOcc X (∃∃ y _ φ)
  | mu {X} {Y} {φ} :
    PositiveOcc X φ → X ≠ Y → PositiveOcc X (μ Y φ)
end

end Pattern


section SubstitutabilityProofs
  namespace Pattern

  variable {𝓢 : Type} [DecidableEq 𝓢] {sgn : Signature 𝓢} {s t : PSort 𝓢}

  theorem substitutable_evar_of_not_free_occ {x : EVar} {φ : Pattern sgn s}: ¬FreeEVar x φ → SubstitutableEVarForIn x x φ := by
    intros hnfv
    induction φ
    all_goals (aesop)



  theorem substitutable_evar_same (x : EVar) (φ : Pattern sgn s) : SubstitutableEVarForIn x x φ := by
    induction φ with
    | evar r y =>
      by_cases h : x = y
      . simp [*] at *
      . simp [*] at *
    | existential r y φ' ih =>
      by_cases h : (∃∃ r y φ').FreeEVar x
      . by_cases h' : y = x
        . aesop
        . aesop
      . apply substitutable_evar_of_not_free_occ h
    | _ => simp [*] at *

  @[simp]
  theorem subst_var_var_eq_self_evar (φ : Pattern sgn s) (x : EVar) : φ.substEVar x x = φ := by
    induction φ with
    | evar r y =>
      by_cases h : x = y <;> simp [*]
    | _ => simp [*]

    done


  theorem substitutable_svar_of_not_free_occ {φ : Pattern sgn s} {ψ : Pattern sgn t} {X : SVar} : ¬φ.FreeSVar X → SubstitutableSVarForIn X ψ φ := by
    intros h
    induction φ with
    | mu Y φ' ih =>
      -- simp at *
      -- specialize ih h
      by_cases h' : X = Y
      . simp [*]
      . aesop
    | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
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



  theorem substitutable_svar_of_mu {φ : Pattern sgn s} {ψ : Pattern sgn t} {X Y : SVar} : X ≠ Y → SubstitutableSVarForIn X ψ (μ Y φ) → SubstitutableSVarForIn X ψ φ := by
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
      | implication φ₁ φ₂ ih₁ ih₂ | application φ₁ φ₂ ih₁ ih₂ =>
        -- simp? [*] at *

        -- specialize ih₁ h'.1
        -- specialize ih₂ h'.2
        by_cases hfv : FreeSVar X ψ
        . rename_i s_1
          intro a
          simp_all only [ne_eq, FreeSVar, not_false_eq_true, true_and, SubstitutableSVarForIn, and_false, implies_true,
            FreeSVar._eq_8, not_true, SubstitutableSVarForIn._eq_5, and_self, ite_self, forall_true_left]
          apply And.intro
          · apply ih₁
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [not_true, implies_true, SubstitutableSVarForIn._eq_5, IsEmpty.forall_iff, true_or]
          · apply ih₂
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [not_true, implies_true, SubstitutableSVarForIn._eq_5, IsEmpty.forall_iff, or_true]
        . aesop
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
  theorem subst_var_var_eq_self_svar (φ : Pattern sgn s) (X : SVar) : φ.substSVar X (.svar t X) = φ := by
    induction φ with
    | svar r Y =>
      by_cases h : r = t
      . by_cases h' : X = Y <;> simp [*]
        subst h
        exact cast_eq _ _
      . simp [*]
    | _ => simp [*]

  @[simp]
  theorem subst_not_free_svar {φ : Pattern sgn s} {X : SVar} (ψ : Pattern sgn t) (not_fv : ¬φ.FreeSVar X) : φ.substSVar X ψ = φ := by
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


variable {𝓢 : Type} [DecidableEq 𝓢] {sgn : Signature 𝓢}

-- def IsAppSymbol {s : PSort 𝓢} : Pattern sgn s → Prop := fun φ => match φ with
--   | (.symbol σ) => True
--   | φ ⬝ ψ => IsAppSymbol φ
--   | _ => False

inductive IsAppSymbol : ∀ {s : PSort 𝓢}, Pattern sgn s → Prop where
| symbol {σ} : IsAppSymbol (.symbol σ)
| app {φ ψ} : IsAppSymbol φ → IsAppSymbol (φ ⬝ ψ)

def AppContext (sgn : Signature 𝓢) (s t : 𝓢) := Pattern sgn (.base s) → {φ : Pattern sgn (.base t) // IsAppSymbol φ}

-- structure AppContext (sgn : Signature 𝓢) (s t : 𝓢) where
--   box : SVar
--   pattern : Pattern sgn t
--   app_symbol : IsAppSymbol pattern
--   is_linear : pattern.countSVar box = 1


def AppContext.insert {sgn : Signature 𝓢} {s t : 𝓢} (C : AppContext sgn s t) (φ : Pattern sgn (.base s)) : Pattern sgn (.base t) :=
  C φ |>.1

def AppContext.is_app_symbol {sgn : Signature 𝓢} {s t : 𝓢} (C : AppContext sgn s t) (φ : Pattern sgn (.base s)) :
  IsAppSymbol (C.insert φ) := C φ |>.2

def AppContext.FreeEVar {s t : 𝓢} (x : EVar) (C : AppContext sgn s t) : Prop :=
  ∃ φ : Pattern sgn s, ¬φ.FreeEVar x ∧ (C.insert φ).FreeEVar x

theorem AppContext.insert_not_free_evar {s t : 𝓢} {x : EVar} {C : AppContext sgn s t} {φ : Pattern sgn s} :
  ¬φ.FreeEVar x → ¬C.FreeEVar x → ¬(C.insert φ).FreeEVar x := by
  intros hφ hC
  unfold AppContext.FreeEVar at hC
  push_neg at hC
  intros h
  specialize hC φ hφ
  contradiction

theorem AppContext.insert_not_free_evar_mpr {s t : 𝓢} {x : EVar} {C : AppContext sgn s t} {φ : Pattern sgn s} :
  ¬(C.insert φ).FreeEVar x → ¬φ.FreeEVar x ∧ ¬C.FreeEVar x := sorry

inductive NestedContext (sgn : Signature 𝓢) : 𝓢 → 𝓢 → Type _ where
| empty {s} : NestedContext sgn s s
| nest {s t r : 𝓢} (Cσ : AppContext sgn t r) (C : NestedContext sgn s t) : NestedContext sgn s r

-- -- seems dangerous
@[simp]
def NestedContext.insert {s t : 𝓢} (C : NestedContext sgn s t) (φ : Pattern sgn (.base s)) : Pattern sgn (.base t) :=
  match C with
  | .empty => φ
  | .nest Cσ C' => Cσ.insert (C'.insert φ)

theorem NestedContext.nest_insert {s t r : 𝓢} (Cσ : AppContext sgn t r) (C : NestedContext sgn s t) (φ : Pattern sgn (.base s)) :
  (NestedContext.nest Cσ C).insert φ = Cσ.insert (C.insert φ) := rfl

/-- Notation for `Nested.insert`-/
notation C "[" φ "]" => NestedContext.insert C φ
/-- Notation for `Nested.empty` -/
notation "□" => NestedContext.empty

@[simp]
def NestedContext.FreeEVar {s t : 𝓢} (x : EVar) (C : NestedContext sgn s t) : Prop :=
  match C with
  | .empty => False
  | .nest Cσ C => Cσ.FreeEVar x ∨ C.FreeEVar x


@[simp]
theorem no_free_occ_evar_insert {s t : 𝓢} {C : NestedContext sgn s t} {φ : Pattern sgn s} {x : EVar} : ¬C[φ].FreeEVar x ↔ ¬φ.FreeEVar x ∧ ¬C.FreeEVar x := by
  constructor <;> intros h
  . induction C with
    | empty => aesop
    | nest Cσ C' ih =>
      constructor
      . simp at *
        have := AppContext.insert_not_free_evar_mpr h
        aesop
      .
        have := AppContext.insert_not_free_evar_mpr h
        aesop
  . induction C with
    | empty => aesop
    | @nest r r' Cσ C' ih =>
      simp at h
      push_neg at h
      simp
      have : ¬C'[φ].FreeEVar x := sorry --because it is neither free in C' nor φ
      have := AppContext.insert_not_free_evar this h.2.1
      aesop
