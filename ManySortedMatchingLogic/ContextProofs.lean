import ManySortedMatchingLogic.FirstOrderProofs

set_option autoImplicit false

variable {Symbol S : Type} [DecidableEq S] {sgn : Signature Symbol S}

open Pattern

namespace Proof

section ContextReasoning
  namespace Proof

  variable {Γ : Set <| Pattern sgn}
  variable {s t : S}
    {C : NestedContext sgn}
    {φ ψ : Pattern sgn}
    (wsφ : WellSorted φ s := by simp_all)
    (wsψ : WellSorted ψ s := by simp_all)
    {wsC : C.WellSorted t}

  def NestedContext.framing
    {s t : S}
    {C : NestedContext sgn} {φ ψ : Pattern sgn}
    (wsφ : WellSorted φ s := by simp_all)
    (wsψ : WellSorted ψ s := by simp_all)
    (wsC : C.WellSorted t := by simp_all)
    (compat : C.holeSort = s)
    :
    Γ ⊢ φ ⇒ ψ → Γ ⊢ C[φ] ⇒ C[ψ] :=
    fun l₁ : Γ ⊢ φ ⇒ ψ =>
    match C with
    | .empty _ => l₁
    | .nest Cσ C' =>
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[ψ] := (framing (C := C') (s := s) (t := Cσ.holeSort) (wsC := by
        cases wsC
        aesop
      )) (by cases compat; simp) l₁
      let l₃ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[ψ]) :=
      (Proof.framing (s := Cσ.holeSort)
        (wsφ := by
          cases compat
          cases wsC
          apply NestedContext.well_sorted_insert C' φ (by aesop) wsφ (by simp)
        )
        (wsψ := by
          cases compat
          cases wsC
          apply NestedContext.well_sorted_insert C' ψ (by aesop) wsψ (by simp)
        ))
        rfl
        l₂
      l₃

  attribute [simp] negation NestedContext.well_sorted_insert

  def NestedContext.propagationBottom {C : NestedContext sgn}
    (wsC : C.WellSorted t)
    :
    Γ ⊢ C[⊥] ⇒ ⊥ :=
    let x : EVar S := ⟨0, C.holeSort⟩
    let l₁ : Γ ⊢ ⊥ ⇒ .evar x ⋀ ⊥ := exFalso (s := C.holeSort)
    let l₂ : Γ ⊢ ⊥ ⇒ .evar x ⋀ ∼⊥ := exFalso (s := C.holeSort)
    let l₃ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] := (NestedContext.framing (s := C.holeSort) (t := t) (wsφ := by simp_all) (wsψ := by simp_all)) rfl l₁
    let l₄ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ∼⊥] := (NestedContext.framing (s := C.holeSort) (t := t)) rfl l₂
    have := NestedContext.well_sorted_insert (s := C.holeSort)
    have : WellSorted (C[⊥]) t := by apply NestedContext.well_sorted_insert (s := C.holeSort) <;> simp_all
    have : WellSorted (C[x ⋀ ⊥]) t := by apply NestedContext.well_sorted_insert (s := C.holeSort) <;> simp_all
    have : WellSorted (C[x ⋀ ∼⊥]) t := by apply NestedContext.well_sorted_insert (s := C.holeSort) <;> simp_all
    let l₅ : Γ ⊢ C[⊥] ⇒ C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥] := (conjIntroRule (s := t)) l₃ l₄
    have : WellSorted (C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥]) t := by aesop
    let l₆ : Γ ⊢ ∼(C[x ⋀ ⊥] ⋀ C[x ⋀ ∼⊥]) := singleton
    (syllogism (s := t)) l₅ l₆


  def NestedContext.propagationDisj
    {s t : S}
    {C : NestedContext sgn} {φ ψ : Pattern sgn}
    (wsφ : WellSorted φ s := by simp_all)
    (wsψ : WellSorted ψ s := by simp_all)
    (wsC : C.WellSorted t := by simp_all)
    (compat : C.holeSort = s)
  :
    Γ ⊢ C.insert (φ ⋁ ψ) ⇒ C.insert φ ⋁ C.insert ψ :=
    match C with
    | .empty _ => implSelf (s := s)
    | .nest Cσ C' =>
      let l₁ : Γ ⊢ C'[φ ⋁ ψ] ⇒ C'[φ] ⋁ C'[ψ] :=
        (propagationDisj (C := C') (s := s) (t := Cσ.holeSort)
          (wsC := by cases wsC; aesop)
        )
        (by cases compat; simp)
      have : WellSorted (C'[φ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (φ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (C'[ψ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (ψ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (C'[φ ⋁ ψ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (φ ⋁ ψ) (by aesop) (by aesop) (by cases compat; simp)
      let l₂ : Γ ⊢ Cσ.insert (C'[φ ⋁ ψ]) ⇒ Cσ.insert (C'[φ] ⋁ C'[ψ]) :=
        (Proof.framing
          (s := Cσ.holeSort)
          (wsφ := by aesop)
          (wsψ := by aesop
          )
        )
          rfl
          l₁
      -- let l₂ : Γ ⊢ (C'.nest Cσ)[φ ⋁ ψ] ⇒ Cσ.insert (C'[φ] ⋁ C'[ψ]) := by exact l₂ -- this is actually definitionally (as witnessed in `Context.nest_insert`) but doesn't work without `by exact`???
      --   -- rw [Context.nest_insert] -- this is actually
      --   -- exact l₂
      let l₃ : Γ ⊢ Cσ.insert (C'[φ] ⋁ C'[ψ]) ⇒ (Cσ.insert (C'[φ])) ⋁ (Cσ.insert (C'[ψ])) :=
        (Proof.propagationDisj (s := Cσ.holeSort)
          (wsφ := by assumption)
          (wsψ := by assumption)
        )
          rfl
      have : WellSorted (Cσ.insert (C'[φ ⋁ ψ])) t := by
        cases wsC
        apply AppContext.well_sorted_insert (s := Cσ.holeSort) rfl (by assumption)
      have : WellSorted ((Cσ.insert (C'[φ])) ⋁ (Cσ.insert (C'[ψ]))) t := by
        simp_all
        constructor <;> apply AppContext.well_sorted_insert (s := Cσ.holeSort) rfl (by assumption)
      have : WellSorted (Cσ.insert (C'[φ] ⋁ C'[ψ])) t := by
        cases wsC
        apply AppContext.well_sorted_insert (s := Cσ.holeSort) rfl (by aesop)
      id (syllogism (s := t)) l₂ l₃

  def NestedContext.propagationDisjR
    {s t : S}
    {C : NestedContext sgn} {φ ψ : Pattern sgn}
    (wsφ : WellSorted φ s := by simp_all)
    (wsψ : WellSorted ψ s := by simp_all)
    (wsC : C.WellSorted t := by simp_all)
    (compat : C.holeSort = s)
  :
    Γ ⊢ C[φ] ⋁ C[ψ] ⇒ C[φ ⋁ ψ] :=
    match C with
    | .empty _ => implSelf (s := s)
    | .nest Cσ C' =>
      let l₁ : Γ ⊢ C'[φ] ⋁ C'[ψ] ⇒ C'[φ ⋁ ψ] := (propagationDisjR (s := s) (t := Cσ.holeSort)
        (wsC := by cases wsC; aesop)
      ) (by cases compat; aesop)
      have : WellSorted (C'[φ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (φ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (C'[ψ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (ψ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (C'[φ ⋁ ψ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (φ ⋁ ψ) (by aesop) (by aesop) (by cases compat; simp)
      let l₁' : Γ ⊢ C'[φ] ⇒ C'[φ] ⋁ C'[ψ] := disjIntroLeft (s := Cσ.holeSort)
      let l₂ : Γ ⊢ C'[φ] ⇒ C'[φ ⋁ ψ] := (syllogism (s := Cσ.holeSort)) l₁' l₁
      let l₃ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[φ ⋁ ψ]) := (Proof.framing (s := Cσ.holeSort) (wsψ := by aesop)) rfl l₂
      let l₄ : Γ ⊢ (C'.nest Cσ)[φ] ⇒ (C'.nest Cσ)[φ ⋁ ψ] :=
      by
        rw [NestedContext.nest_insert]
        rw [NestedContext.nest_insert]
        exact l₃
      let l₂' : Γ ⊢ C'[ψ] ⇒ C'[φ ⋁ ψ] := (syllogism (s := Cσ.holeSort) (wsχ := by aesop)) (disjIntroRight (s := Cσ.holeSort)) l₁
      let l₃' : Γ ⊢ Cσ.insert (C'[ψ]) ⇒ Cσ.insert (C'[φ ⋁ ψ]) := (Proof.framing (s := Cσ.holeSort) (wsψ := by aesop)) rfl l₂'
      let l₄' : Γ ⊢ (C'.nest Cσ)[ψ] ⇒ (C'.nest Cσ)[φ ⋁ ψ] := l₃'
      have : WellSorted ((C'.nest Cσ)[φ]) t := sorry
      have : WellSorted ((C'.nest Cσ)[ψ]) t := sorry
      have : WellSorted ((C'.nest Cσ)[φ ⋁ ψ]) t := sorry
      (disjIntroAtHyp (s := t)) l₄ l₄'

  def NestedContext.propagationExist {s t : S} {C : NestedContext sgn} {φ : Pattern sgn} {x : EVar S} (hnfv : ¬C.FreeEVar x)
    (wsφ : WellSorted φ s := by aesop)
    (wsC : C.WellSorted t := by aesop)
    (compat : C.holeSort = s)
  :
    Γ ⊢ (C[∃∃ x φ]) ⇒ (∃∃ x (C [φ])) :=
    match h:C with
    | .empty _ => implSelf (s := s)
    | .nest Cσ C' =>
      have not_fvχ : ¬Cσ.FreeEVar x := by aesop?
      let l₁ : Γ ⊢ (C'[∃∃ x φ]) ⇒ (∃∃ x (C'[φ])) := (propagationExist (s := s) (t := Cσ.holeSort) (wsC := by cases wsC; aesop)) (by aesop?) (by cases compat; aesop)
      have : WellSorted (C'[∃∃ x φ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (∃∃ x φ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (C'[φ]) Cσ.holeSort := by cases wsC; apply NestedContext.well_sorted_insert (s := s) C' (φ) (by aesop) (by aesop) (by cases compat; simp)
      have : WellSorted (∃∃ x (C'[φ])) Cσ.holeSort := by cases wsC; rw [well_sorted_existential]; assumption
      let l₂ : Γ ⊢ Cσ.insert (C'[∃∃ x φ]) ⇒ Cσ.insert (∃∃ x (C'[φ])) := (Proof.framing (s := Cσ.holeSort)) rfl l₁
      let l₃ : Γ ⊢ Cσ.insert (∃∃ x (C'[φ])) ⇒ (∃∃ x (Cσ.insert <| C'[φ])) := (Proof.propagationExist (s := Cσ.holeSort)) _ (by
        have : ¬Cσ.FreeEVar x := by aesop?
        apply AppContext.insert_not_free_evar
        . aesop -- exists_binds
        . assumption
      )
      have : WellSorted (Cσ.insert (C'[∃∃ x φ])) t := sorry
      have : WellSorted (Cσ.insert (∃∃ x (C'[φ]))) t := sorry
      have : WellSorted (∃∃ x (Cσ.insert <| C'[φ])) t := sorry
      let l₄ : Γ ⊢ Cσ.insert (C'[∃∃ x φ]) ⇒ (∃∃ x (Cσ.insert <| C'[φ])) := (syllogism (s := t)) l₂ l₃
      l₄


  def NestedContext.propagationExistR {C : NestedContext sgn} {φ : Pattern sgn} {x : EVar S} (hnfv : ¬C.FreeEVar x) :
    Γ ⊢ (∃∃ x (C [φ])) ⇒ (C[∃∃ x φ]) :=
    match h:C with
    | .empty => implSelf
    | .nest Cσ C' =>
      have not_fvEφ : ¬(∃∃ x φ).FreeEVar x := by aesop?
      have not_fvCEφ : ¬((C'.nest Cσ)[∃∃ x φ]).FreeEVar x := by
        -- rw [AppContext.no_free_occ_evar_insert]
        -- exact And.intro not_fvEφ not_fv
        rw [NestedContext.nest_insert]
        apply AppContext.insert_not_free_evar
        . simp at hnfv
          push_neg at hnfv
          sorry
        . aesop
      let l₁ : Γ ⊢ (∃∃ x (C'[φ])) ⇒ (C'[∃∃ x φ]) := propagationExistR (C := C') (by aesop?)
      let l₂ : Γ ⊢ C'[φ][x ⇐ᵉ x] ⇒ ∃∃ x (C'[φ]) := existQuan <| Pattern.substitutable_evar_same _ _
      let l₃ : Γ ⊢ C'[φ][x ⇐ᵉ x] ⇒ C'[∃∃ x φ] := syllogism l₂ l₁
      -- let l₄ : Γ ⊢ (C'.substEvar x x)[φ[x ⇐ᵉ x]] ⇒ C'[∃∃ r x φ] := by
      --   rw [AppContext.subst_evar_insert] at l₃ ; exact l₃
      -- let l₄ : Γ ⊢ C'[φ[x ⇐ᵉ .evar x]] ⇒ C'[∃∃ x φ] := by rw [AppContext.subst_var_var_eq_self_evar] at l₄ ; exact l₄
      let l₅ : Γ ⊢ C'[φ] ⇒ C'[∃∃ x φ] := by rw [Pattern.subst_var_var_eq_self_evar] at l₃ ; exact l₃ -- why did I do it so convoluted in the other formalization?
      let l₆ : Γ ⊢ Cσ.insert (C'[φ]) ⇒ Cσ.insert (C'[∃∃ x φ]) := Proof.framing l₅
      let l₇ : Γ ⊢ (C'.nest Cσ)[φ] ⇒ (C'.nest Cσ)[∃∃ x φ] := by simpa [*]
      let l₉ : Γ ⊢ ∃∃ x ((C'.nest Cσ)[φ]) ⇒ (C'.nest Cσ)[∃∃ x φ] := existGen not_fvCEφ l₇
      l₉

  end Proof
end ContextReasoning
