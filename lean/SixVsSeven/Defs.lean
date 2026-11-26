import Mathlib

/-!
# Definitions: XOR–AND circuits over `𝔽₂` and the map `Q : 𝔽₂⁶ → 𝔽₂⁵`

* A circuit on inputs `I` with outputs `O` has `size` fan-in-two AND gates.  Each AND input and
  each output is an affine combination (over `𝔽₂`) of the inputs and of the *earlier* AND gates.
  XOR gates and constants are free: they live inside the affine combinations.  So `size` is the
  number of AND gates.
* A circuit is *quadratic* if no AND input uses an AND gate (AND-depth one; the level-one
  circuits `L₁` of Mirwald–Schnorr, the quadratic circuits of Boyar–Find).
* Inputs are `x₁ … x₆`, written `x 0 … x 5` (0-based); outputs `q₁ … q₅` are `Qmap x 0 … Qmap x 4`.
-/

namespace SixVsSeven

/-- The field with two elements. -/
abbrev F := ZMod 2

/-- An affine combination of the inputs `I` and of `g` gate values. -/
structure Affine (I : Type) (g : ℕ) where
  const : F
  lin : I → F
  gat : Fin g → F

/-- A circuit with `size` fan-in-two AND gates; gate `r` may only read gates `j < r`
(entries of `gat` at indices `≥ r` are ignored). -/
structure Circuit (I O : Type) where
  size : ℕ
  left : Fin size → Affine I size
  right : Fin size → Affine I size
  out : O → Affine I size

variable {I O : Type} [Fintype I]

/-- Value of an affine combination, reading only gates `j` with `j < bound`. -/
def Affine.evalBelow {g : ℕ} (A : Affine I g) (x : I → F) (bound : ℕ)
    (v : (j : Fin g) → j.val < bound → F) : F :=
  A.const + ∑ i, A.lin i * x i + ∑ j : Fin g, (if h : j.val < bound then A.gat j * v j h else 0)

/-- The value of AND gate `r` on input `x`. -/
def Circuit.gateVal (C : Circuit I O) (x : I → F) (r : Fin C.size) : F :=
  (C.left r).evalBelow x r.val (fun j _ => C.gateVal x j) *
  (C.right r).evalBelow x r.val (fun j _ => C.gateVal x j)
termination_by r.val
decreasing_by all_goals assumption

/-- The value of output `o` on input `x`. -/
def Circuit.outVal (C : Circuit I O) (x : I → F) (o : O) : F :=
  (C.out o).evalBelow x C.size (fun j _ => C.gateVal x j)

/-- A circuit is quadratic if no AND gate reads another AND gate. -/
def Circuit.IsQuadratic (C : Circuit I O) : Prop :=
  ∀ r j, (C.left r).gat j = 0 ∧ (C.right r).gat j = 0

/-- The five quadratic forms (0-based variable indices; `x_{ij}` in the note is `x (i-1) * x (j-1)`). -/
def Qmap (x : Fin 6 → F) : Fin 5 → F :=
  ![x 0 * x 1 + x 0 * x 2 + x 0 * x 3,
    x 0 * x 2 + x 0 * x 3 + x 2 * x 3,
    x 0 * x 1 + x 0 * x 2 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3,
    x 0 * x 2 + x 1 * x 2 + x 0 * x 3 + x 2 * x 3 + x 0 * x 4 + x 2 * x 4 + x 3 * x 4 + x 1 * x 5 +
      x 3 * x 5,
    x 0 * x 2 + x 1 * x 2 + x 0 * x 3 + x 0 * x 4 + x 1 * x 4 + x 3 * x 4 + x 3 * x 5]

/-- `C` computes `Q` (as Boolean functions). -/
def ComputesQ (C : Circuit (Fin 6) (Fin 5)) : Prop := ∀ x a, C.outVal x a = Qmap x a

end SixVsSeven
