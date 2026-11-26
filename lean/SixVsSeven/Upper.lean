import SixVsSeven.Coef

/-!
# Upper bounds: `MC(Q) ≤ 6` and `qMC(Q) ≤ 7`

The circuits are those of the note (0-based variables).  They are checked on all 64 inputs by
`decide`, after replacing the well-founded gate evaluation by an equivalent iteration.
-/

namespace SixVsSeven

variable {I O : Type} [Fintype I]

/-- Gate values after evaluating the first `n` gates (later gates are `0`). -/
def evalSeq (C : Circuit I O) (x : I → F) : ℕ → Fin C.size → F
  | 0 => fun _ => 0
  | n + 1 => fun r =>
      if r.val = n then
        (C.left r).evalBelow x n (fun j _ => evalSeq C x n j) *
          (C.right r).evalBelow x n (fun j _ => evalSeq C x n j)
      else evalSeq C x n r

theorem evalBelow_congr {g : ℕ} (A : Affine I g) (x : I → F) (b : ℕ)
    (v v' : (j : Fin g) → j.val < b → F) (h : ∀ j hj, v j hj = v' j hj) :
    A.evalBelow x b v = A.evalBelow x b v' := by
  simp only [Affine.evalBelow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rw [h j hj]
  · rfl

theorem evalSeq_eq (C : Circuit I O) (x : I → F) :
    ∀ n (r : Fin C.size), r.val < n → evalSeq C x n r = C.gateVal x r := by
  intro n
  induction n with
  | zero => intro r h; omega
  | succ n ih =>
    intro r hr
    simp only [evalSeq]
    split_ifs with h
    · rw [gateVal_unfold, h]
      congr 1
      · exact evalBelow_congr _ _ _ _ _ fun j hj => ih j hj
      · exact evalBelow_congr _ _ _ _ _ fun j hj => ih j hj
    · exact ih r (by omega)

theorem outVal_eq_seq (C : Circuit I O) (x : I → F) (o : O) :
    C.outVal x o = (C.out o).evalBelow x C.size (fun j _ => evalSeq C x C.size j) := by
  rw [Circuit.outVal]
  exact evalBelow_congr _ _ _ _ _ fun j hj => (evalSeq_eq C x C.size j hj).symm

/-- Affine combination from coefficient vectors. -/
def aff {g : ℕ} (l : Fin 6 → F) (gt : Fin g → F) : Affine (Fin 6) g := ⟨0, l, gt⟩

/-- The six-gate circuit (`g₄ g₅ g₆` read `a = g₁+g₂+x₂+x₃+x₅` and `b = g₃+x₁+x₂+x₆`). -/
def C6 : Circuit (Fin 6) (Fin 5) where
  size := 6
  left := ![aff ![0,1,1,1,0,0] 0, aff ![1,0,0,1,0,0] 0, aff ![1,1,0,1,0,0] 0,
    aff ![0,1,1,0,1,0] ![1,1,0,0,0,0], aff ![0,0,1,1,1,0] ![1,1,0,0,0,0],
    aff ![0,1,1,1,1,0] ![1,1,0,0,0,0]]
  right := ![aff ![1,1,1,1,0,0] 0, aff ![0,0,1,1,0,0] 0, aff ![1,0,1,1,0,0] 0,
    aff ![1,1,0,0,0,1] ![0,0,1,0,0,0], aff ![0,1,1,1,0,1] ![0,0,1,0,0,0],
    aff ![0,0,0,1,0,1] ![0,0,1,0,0,0]]
  out := ![aff ![0,1,1,1,0,0] ![1,0,0,0,0,0], aff ![0,0,0,1,0,0] ![0,1,0,0,0,0],
    aff ![1,0,0,1,0,0] ![0,0,1,0,0,0], aff ![1,1,0,1,0,0] ![0,0,1,1,1,0],
    aff ![1,1,1,1,0,0] ![1,1,1,1,0,1]]

/-- The seven-gate quadratic circuit. -/
def C7 : Circuit (Fin 6) (Fin 5) where
  size := 7
  left := ![aff ![0,1,1,1,0,0] 0, aff ![1,0,0,1,0,0] 0, aff ![1,1,0,1,0,0] 0,
    aff ![1,1,1,0,0,0] 0, aff ![0,1,0,1,0,0] 0, aff ![1,1,0,0,0,0] 0, aff ![0,0,0,1,0,0] 0]
  right := ![aff ![1,1,1,1,0,0] 0, aff ![0,0,1,1,0,0] 0, aff ![1,0,1,1,0,0] 0,
    aff ![0,0,0,0,1,0] 0, aff ![1,1,0,0,1,1] 0, aff ![0,0,1,0,1,0] 0, aff ![1,0,0,0,1,1] 0]
  out := ![aff ![0,1,1,1,0,0] ![1,0,0,0,0,0,0], aff ![0,0,0,1,0,0] ![0,1,0,0,0,0,0],
    aff ![1,0,0,1,0,0] ![0,0,1,0,0,0,0], aff ![1,1,0,1,0,0] ![0,0,1,1,1,0,0],
    aff ![0,0,0,0,0,0] ![0,0,0,0,0,1,1]]

theorem C6_computes : ComputesQ C6 := by
  intro x a
  rw [outVal_eq_seq]
  revert x a
  decide +kernel

theorem C7_quadratic : C7.IsQuadratic := by
  intro r j; revert r j; decide +kernel

theorem C7_computes : ComputesQ C7 := by
  intro x a
  rw [outVal_eq_seq]
  revert x a
  decide +kernel

theorem mc_le_six : ∃ C : Circuit (Fin 6) (Fin 5), C.size = 6 ∧ ComputesQ C :=
  ⟨C6, rfl, C6_computes⟩

theorem qmc_le_seven : ∃ C : Circuit (Fin 6) (Fin 5), C.IsQuadratic ∧ C.size = 7 ∧ ComputesQ C :=
  ⟨C7, C7_quadratic, rfl, C7_computes⟩

end SixVsSeven
