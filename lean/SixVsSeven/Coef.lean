import SixVsSeven.Defs

/-!
# Quadratic coefficients of Boolean functions

`coef f p` is the coefficient of `x_i x_j` (`(i, j) = pr p`, `i < j`) in the algebraic normal form
of `f`, computed as `f(e_i + e_j) + f(e_i) + f(e_j) + f(0)`.  It is additive, kills affine
functions, and sends a product of two affine functions to the wedge of their linear parts.
-/

namespace SixVsSeven

open Finset

/-- The 15 pairs `i < j` of `Fin 6`. -/
def pr : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

def e (i : Fin 6) : Fin 6 → F := Pi.single i 1

def coef (f : (Fin 6 → F) → F) (p : Fin 15) : F :=
  f (e (pr p).1 + e (pr p).2) + f (e (pr p).1) + f (e (pr p).2) + f 0

/-- Wedge of two linear forms, in the coordinates `pr`. -/
def wedgeF (u v : Fin 6 → F) : Fin 15 → F :=
  fun p => u (pr p).1 * v (pr p).2 + u (pr p).2 * v (pr p).1

/-- Linear form. -/
def lin6 (a x : Fin 6 → F) : F := ∑ k, a k * x k

theorem lin6_e (a : Fin 6 → F) (i : Fin 6) : lin6 a (e i) = a i := by
  simp [lin6, e, Pi.single_apply]

theorem lin6_add (a x y : Fin 6 → F) : lin6 a (x + y) = lin6 a x + lin6 a y := by
  simp [lin6, mul_add, Finset.sum_add_distrib]

theorem lin6_zero (a : Fin 6 → F) : lin6 a 0 = 0 := by simp [lin6]

theorem coef_add (f g : (Fin 6 → F) → F) (p : Fin 15) :
    coef (fun x => f x + g x) p = coef f p + coef g p := by
  simp only [coef]; ring

theorem coef_smul (c : F) (f : (Fin 6 → F) → F) (p : Fin 15) :
    coef (fun x => c * f x) p = c * coef f p := by
  simp only [coef]; ring

theorem coef_sum {ι : Type} (s : Finset ι) (f : ι → (Fin 6 → F) → F) (p : Fin 15) :
    coef (fun x => ∑ k ∈ s, f k x) p = ∑ k ∈ s, coef (f k) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef]
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [coef_add (fun x => f k x) (fun x => ∑ k ∈ s, f k x), ih]

/-- Affine functions have no quadratic part. -/
theorem coef_affine (c : F) (a : Fin 6 → F) (p : Fin 15) :
    coef (fun x => c + lin6 a x) p = 0 := by
  simp only [coef, lin6_add, lin6_e, lin6_zero]
  generalize a (pr p).1 = u; generalize a (pr p).2 = v
  revert c u v; decide

/-- The product of two affine functions has quadratic part the wedge of the linear parts. -/
theorem coef_mul (c d : F) (a b : Fin 6 → F) (p : Fin 15) :
    coef (fun x => (c + lin6 a x) * (d + lin6 b x)) p = wedgeF a b p := by
  simp only [coef, wedgeF, lin6_add, lin6_e, lin6_zero]
  generalize a (pr p).1 = a1; generalize a (pr p).2 = a2
  generalize b (pr p).1 = b1; generalize b (pr p).2 = b2
  revert c d a1 a2 b1 b2; decide

/-- Coefficient vectors of `q₁ … q₅`. -/
def Qm (a : Fin 5) : Fin 15 → F := coef (fun x => Qmap x a)

/-- The explicit table, for reference: `Qm a p` is the coefficient of pair `pr p` in `q_{a+1}`. -/
theorem Qm_table : Qm = ![
    ![1,1,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,1,0,0,0,0,0,0,1,0,0,0,0,0],
    ![1,1,0,0,0,1,1,0,0,1,0,0,0,0,0],
    ![0,1,1,1,0,1,0,0,1,1,1,0,1,1,0],
    ![0,1,1,1,0,1,0,1,0,0,0,0,1,1,0]] := by
  funext a p; revert a p; decide

/-- Value of an affine combination with no gate terms. -/
theorem evalBelow_noGate {I : Type} [Fintype I] {g : ℕ} (A : Affine I g) (hA : ∀ j, A.gat j = 0)
    (x : I → F) (b : ℕ) (v : (j : Fin g) → j.val < b → F) :
    A.evalBelow x b v = A.const + ∑ i, A.lin i * x i := by
  simp [Affine.evalBelow, hA]

theorem gateVal_unfold {I O : Type} [Fintype I] (C : Circuit I O) (x : I → F) (r : Fin C.size) :
    C.gateVal x r = (C.left r).evalBelow x r.val (fun j _ => C.gateVal x j) *
      (C.right r).evalBelow x r.val (fun j _ => C.gateVal x j) := by
  rw [Circuit.gateVal]

end SixVsSeven
