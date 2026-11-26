import SixVsSeven.Coef

/-!
# Multiplicative complexity of `Q` is at least 6

`mc_ge_six`: no XOR–AND circuit with at most 5 AND gates computes `Qmap`.
-/

namespace SixVsSeven

open Finset

/-! ### Constant shift differences -/

/-- `f (x + e i) + f x` does not depend on `x`. -/
def Sh (f : (Fin 6 → F) → F) (i : Fin 6) : Prop := ∀ x, f (x + e i) + f x = f (e i) + f 0

theorem Sh.add {f g : (Fin 6 → F) → F} {i : Fin 6} (hf : Sh f i) (hg : Sh g i) :
    Sh (fun x => f x + g x) i := by
  intro x; linear_combination hf x + hg x

theorem Sh.smul {f : (Fin 6 → F) → F} {i : Fin 6} (c : F) (hf : Sh f i) :
    Sh (fun x => c * f x) i := by
  intro x; linear_combination c * hf x

theorem Sh.const (c : F) (i : Fin 6) : Sh (fun _ => c) i := fun _ => rfl

theorem Sh.lin (a : Fin 6 → F) (i : Fin 6) : Sh (fun x => lin6 a x) i := by
  intro x
  simp only [lin6_add, lin6_zero]
  generalize lin6 a x = u; generalize lin6 a (e i) = v
  revert u v; decide

theorem Sh.sum {ι : Type} (s : Finset ι) (f : ι → (Fin 6 → F) → F) (i : Fin 6)
    (h : ∀ k ∈ s, Sh (f k) i) : Sh (fun x => ∑ k ∈ s, f k x) i := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x; simp
  | insert k s hk ih =>
    have H := (h k (mem_insert_self k s)).add (ih (fun j hj => h j (mem_insert_of_mem hj)))
    intro x
    simp only [sum_insert hk]
    exact H x

theorem evalBelow_eq {s : ℕ} (A : Affine (Fin 6) s) (b : ℕ) (G : Fin s → (Fin 6 → F) → F)
    (x : Fin 6 → F) :
    A.evalBelow x b (fun j _ => G j x) =
      (A.const + lin6 A.lin x) + ∑ j, (if j.val < b then A.gat j * G j x else 0) := by
  simp only [Affine.evalBelow, lin6, dite_eq_ite]

theorem Sh_eval {s : ℕ} (A : Affine (Fin 6) s) (b : ℕ) (G : Fin s → (Fin 6 → F) → F)
    (i : Fin 6) (hG : ∀ j : Fin s, j.val < b → Sh (G j) i) :
    Sh (fun x => A.evalBelow x b (fun j _ => G j x)) i := by
  have h : (fun x => A.evalBelow x b (fun j _ => G j x)) =
      fun x => (A.const + lin6 A.lin x) +
        ∑ j, (fun j x => if j.val < b then A.gat j * G j x else 0) j x := by
    funext x; exact evalBelow_eq A b G x
  rw [h]
  refine Sh.add (Sh.add (Sh.const _ _) (Sh.lin _ _)) (Sh.sum _ _ _ fun j _ => ?_)
  by_cases hj : j.val < b
  · simp only [hj, if_true]; exact (hG j hj).smul _
  · simp only [hj, if_false]; exact Sh.const _ _

/-! ### Finite facts about `Q` -/

theorem Qmap_shift (x : Fin 6 → F) (a : Fin 5) (ha : a.val < 3) (i : Fin 6) (hi : 4 ≤ i.val) :
    Qmap (x + e i) a = Qmap x a := by
  have h0 : (e i) 0 = 0 := by simp [e, Pi.single_apply]; omega
  have h1 : (e i) 1 = 0 := by simp [e, Pi.single_apply]; omega
  have h2 : (e i) 2 = 0 := by simp [e, Pi.single_apply]; omega
  have h3 : (e i) 3 = 0 := by simp [e, Pi.single_apply]; omega
  fin_cases a <;> simp at ha <;> simp [Qmap, h0, h1, h2, h3]

theorem Qm_inj (y y' : Fin 5 → F) (h : ∀ p, ∑ a, y a * Qm a p = ∑ a, y' a * Qm a p) : y = y' := by
  rw [Qm_table] at h
  revert y y'
  decide +kernel

theorem Qm_45 (d : Fin 5 → F) : ∑ a, d a * Qm a 14 = 0 := by
  rw [Qm_table]; revert d; decide +kernel

/-- Pair indices `(i, 4)` and `(i, 5)` for `i < 4`. -/
def p4 : Fin 4 → Fin 15 := ![3, 7, 10, 12]
def p5 : Fin 4 → Fin 15 := ![4, 8, 11, 13]

theorem pr_p4 (i : Fin 4) : pr (p4 i) = (Fin.castLE (by norm_num) i, 4) := by
  revert i; decide
theorem pr_p5 (i : Fin 4) : pr (p5 i) = (Fin.castLE (by norm_num) i, 5) := by
  revert i; decide
theorem pr_14 : pr 14 = (4, 5) := by decide

/-- The final finite contradiction. -/
theorem fin_contra (d : Fin 5 → F) (hd : d 3 ≠ 0 ∨ d 4 ≠ 0) (a5 a6 b5 b6 : F)
    (hab : a5 * b6 + a6 * b5 = 0) :
    ∃ i : Fin 4, ∀ T P : F, ¬ ((∑ a, d a * Qm a (p4 i)) = a5 * T + b5 * P ∧
      (∑ a, d a * Qm a (p5 i)) = a6 * T + b6 * P) := by
  rw [Qm_table]
  revert d a5 a6 b5 b6
  decide +kernel

/-! ### Algebra for `coef` of a product -/

theorem alg_i (L0 L1 L4 L14 R0 R1 R4 R14 : F) (hL : L14 + L1 = L4 + L0) (hR : R14 + R1 = R4 + R0) :
    L14 * R14 + L1 * R1 + L4 * R4 + L0 * R0 = (L4 + L0) * (R1 + R0) + (R4 + R0) * (L1 + L0) := by
  revert L0 L1 L4 L14 R0 R1 R4 R14; decide

theorem alg_45 (L0 L4 L5 L45 R0 R4 R5 R45 : F) (hL : L45 + L4 = L5 + L0) (hR : R45 + R4 = R5 + R0) :
    L45 * R45 + L4 * R4 + L5 * R5 + L0 * R0 = (L4 + L0) * (R5 + R0) + (L5 + L0) * (R4 + R0) := by
  revert L0 L4 L5 L45 R0 R4 R5 R45; decide

theorem coef_prod_i (Lf Rf : (Fin 6 → F) → F) (hL : Sh Lf 4) (hR : Sh Rf 4) (hL5 : Sh Lf 5)
    (hR5 : Sh Rf 5) (i : Fin 4) :
    coef (fun x => Lf x * Rf x) (p4 i) =
      (Lf (e 4) + Lf 0) * (Rf (e (Fin.castLE (by norm_num) i)) + Rf 0) +
      (Rf (e 4) + Rf 0) * (Lf (e (Fin.castLE (by norm_num) i)) + Lf 0) ∧
    coef (fun x => Lf x * Rf x) (p5 i) =
      (Lf (e 5) + Lf 0) * (Rf (e (Fin.castLE (by norm_num) i)) + Rf 0) +
      (Rf (e 5) + Rf 0) * (Lf (e (Fin.castLE (by norm_num) i)) + Lf 0) := by
  simp only [coef, pr_p4, pr_p5]
  exact ⟨alg_i _ _ _ _ _ _ _ _ (hL _) (hR _), alg_i _ _ _ _ _ _ _ _ (hL5 _) (hR5 _)⟩

theorem coef_prod_45 (Lf Rf : (Fin 6 → F) → F) (hL5 : Sh Lf 5) (hR5 : Sh Rf 5) :
    coef (fun x => Lf x * Rf x) 14 =
      (Lf (e 4) + Lf 0) * (Rf (e 5) + Rf 0) + (Lf (e 5) + Lf 0) * (Rf (e 4) + Rf 0) := by
  simp only [coef, pr_14]
  exact alg_45 _ _ _ _ _ _ _ _ (hL5 _) (hR5 _)

end SixVsSeven

namespace SixVsSeven

open Finset

theorem F_add_self (u : F) : u + u = 0 := by revert u; decide

theorem two_cancel (a b c : F) (h : a = b + c) : c = a + b := by
  subst h; revert b c; decide

theorem outVal_eq (C : Circuit (Fin 6) (Fin 5)) (x : Fin 6 → F) (a : Fin 5) :
    C.outVal x a = ((C.out a).const + lin6 (C.out a).lin x) +
      ∑ k, (C.out a).gat k * C.gateVal x k := by
  simp [Circuit.outVal, Affine.evalBelow, lin6, add_assoc]

theorem mc_ge_six (C : Circuit (Fin 6) (Fin 5)) (hC : ComputesQ C) : 6 ≤ C.size := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ : ∃ A : Fin 5 → (Fin 6 → F) → F,
      ∀ a x, A a x = (C.out a).const + lin6 (C.out a).lin x := ⟨_, fun _ _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 5 → F) → (Fin C.size → F),
      ∀ y k, φ y k = ∑ a, y a * (C.out a).gat k := ⟨_, fun _ _ => rfl⟩
  have hQ : ∀ x a, Qmap x a = A a x + ∑ k, (C.out a).gat k * C.gateVal x k := by
    intro x a; rw [← hC x a, outVal_eq, hA]
  have hcomb : ∀ (y : Fin 5 → F) x,
      ∑ a, y a * Qmap x a = ∑ a, y a * A a x + ∑ k, φ y k * C.gateVal x k := by
    intro y x
    simp only [hQ, mul_add, sum_add_distrib, hφ, sum_mul, mul_sum]
    congr 1
    rw [sum_comm]; simp only [mul_assoc]
  have hAfun : ∀ a, (fun x => A a x) = fun x => (C.out a).const + lin6 (C.out a).lin x :=
    fun a => funext (hA a)
  have hA0 : ∀ a p, coef (fun x => A a x) p = 0 := by
    intro a p; rw [hAfun a]; exact coef_affine _ _ _
  have hcoef : ∀ (y : Fin 5 → F) p,
      ∑ a, y a * Qm a p = ∑ k, φ y k * coef (fun x => C.gateVal x k) p := by
    intro y p
    have h1 : (fun x => ∑ a, y a * Qmap x a) =
        fun x => ∑ a, y a * A a x + ∑ k, φ y k * C.gateVal x k := funext (hcomb y)
    have h2 := congrArg (fun f => coef f p) h1
    simp only [coef_add, coef_sum, coef_smul, hA0, mul_zero, sum_const_zero, zero_add] at h2
    exact h2
  have hinj : Function.Injective φ := by
    intro y y' h
    apply Qm_inj
    intro p; rw [hcoef, hcoef, h]
  have hs : C.size = 5 := by
    have h := Fintype.card_le_of_injective φ hinj
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    omega
  have hsurj : Function.Surjective φ :=
    ((Fintype.bijective_iff_injective_and_card φ).mpr
      ⟨hinj, by simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, hs]⟩).2
  choose d hd using fun k : Fin C.size => hsurj (Pi.single k 1)
  have hgate : ∀ k x, C.gateVal x k = ∑ a, d k a * Qmap x a + ∑ a, d k a * A a x := by
    intro k x
    have h := hcomb (d k) x
    rw [hd k] at h
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
      if_true] at h
    exact two_cancel _ _ _ h
  have hgfun : ∀ k, (fun x => C.gateVal x k) =
      fun x => ∑ a, d k a * Qmap x a + ∑ a, d k a * A a x := fun k => funext (hgate k)
  have hgcoef : ∀ k p, coef (fun x => C.gateVal x k) p = ∑ a, d k a * Qm a p := by
    intro k p
    rw [hgfun k]
    simp only [coef_add, coef_sum, coef_smul, hA0, mul_zero, sum_const_zero, add_zero]
    rfl
  have hex : ∃ k, d k 3 ≠ 0 := by
    by_contra hno
    push Not at hno
    have key : φ (fun a => ∑ k, φ (Pi.single 3 1) k * d k a) = φ (Pi.single 3 1) := by
      funext j
      rw [hφ]
      simp only [sum_mul, mul_assoc]
      rw [sum_comm]
      simp only [← mul_sum, ← hφ, hd, Pi.single_apply, mul_ite, mul_one, mul_zero,
        sum_ite_eq, mem_univ, if_true]
    have := congrFun (hinj key) 3
    simp [hno] at this
  have hShgood : ∀ j, d j 3 = 0 → d j 4 = 0 → ∀ i : Fin 6, 4 ≤ i.val →
      Sh (fun x => C.gateVal x j) i := by
    intro j h3 h4 i hi
    rw [hgfun j]
    refine Sh.add (Sh.sum _ _ _ fun a _ => ?_) (Sh.sum _ _ _ fun a _ => ?_)
    · by_cases ha : a.val < 3
      · intro x
        have h0 := Qmap_shift 0 a ha i hi
        rw [zero_add] at h0
        simp only [Qmap_shift x a ha i hi, h0, F_add_self]
      · have hda : d j a = 0 := by
          have : a = 3 ∨ a = 4 := by omega
          rcases this with rfl | rfl <;> assumption
        simp only [hda, zero_mul]; exact Sh.const 0 i
    · show Sh (fun x => d j a * A a x) i
      refine Sh.smul _ ?_
      have H := Sh.add (Sh.const ((C.out a).const) i) (Sh.lin (C.out a).lin i)
      intro x; simp only [hA]; exact H x
  have main : ∀ n, ∀ k : Fin C.size, k.val = n → d k 3 = 0 ∧ d k 4 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro k hk
    by_contra hbad
    have hd' : d k 3 ≠ 0 ∨ d k 4 ≠ 0 := by tauto
    have hprev : ∀ j : Fin C.size, j.val < k.val → ∀ i : Fin 6, 4 ≤ i.val →
        Sh (fun x => C.gateVal x j) i := by
      intro j hj i hi
      have h := ih j.val (hk ▸ hj) j rfl
      exact hShgood j h.1 h.2 i hi
    obtain ⟨Lf, hLf⟩ : ∃ Lf : (Fin 6 → F) → F,
        Lf = fun x => (C.left k).evalBelow x k.val (fun j _ => C.gateVal x j) := ⟨_, rfl⟩
    obtain ⟨Rf, hRf⟩ : ∃ Rf : (Fin 6 → F) → F,
        Rf = fun x => (C.right k).evalBelow x k.val (fun j _ => C.gateVal x j) := ⟨_, rfl⟩
    have hL : ∀ i : Fin 6, 4 ≤ i.val → Sh Lf i := fun i hi => by
      rw [hLf]; exact Sh_eval _ _ (fun j x => C.gateVal x j) i (fun j hj => hprev j hj i hi)
    have hR : ∀ i : Fin 6, 4 ≤ i.val → Sh Rf i := fun i hi => by
      rw [hRf]; exact Sh_eval _ _ (fun j x => C.gateVal x j) i (fun j hj => hprev j hj i hi)
    have hgk : (fun x => C.gateVal x k) = fun x => Lf x * Rf x := by
      funext x; rw [gateVal_unfold, hLf, hRf]
    have hab := coef_prod_45 Lf Rf (hL 5 (by decide)) (hR 5 (by decide))
    rw [← hgk, hgcoef, Qm_45] at hab
    obtain ⟨i, hi⟩ := fin_contra (d k) hd' _ _ _ _ hab.symm
    have hpi := coef_prod_i Lf Rf (hL 4 (by decide)) (hR 4 (by decide)) (hL 5 (by decide))
      (hR 5 (by decide)) i
    rw [← hgk, hgcoef, hgcoef] at hpi
    exact hi _ _ hpi
  obtain ⟨k, hk⟩ := hex
  exact hk (main k.val k rfl).1

end SixVsSeven
