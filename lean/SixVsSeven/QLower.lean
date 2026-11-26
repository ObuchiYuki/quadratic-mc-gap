import SixVsSeven.Check0
import SixVsSeven.Check1
import SixVsSeven.Check2
import SixVsSeven.Check3

/-!
# `qMC(Q) ≥ 7`

From a quadratic circuit with `t ≤ 6` gates: the coefficient vectors satisfy
`q_a = Σ_k ρ_{a,k} (a_k ∧ b_k)`.  The rows `ρ_a` are independent and lie in the kernel of
`y ↦ Σ_k y_k π(a_k ∧ b_k)`, so its range has dimension `≤ t - 5 ≤ 1`: every `π(a_k ∧ b_k)` is `0`
or one fixed `σ`.  The certificate functional for `σ` vanishes on all such wedges (checked for
all `64 × 64` pairs in `Check*.lean`) but not on some `q_a`: contradiction.
-/

namespace SixVsSeven
open Finset

theorem allPairs (u v : Fin 64) : pairOK u v = true := by
  have hu := u.isLt
  by_cases h0 : u.val < 16
  · exact pairsOK_spec 0 16 check0 u v (by omega) (by omega)
  by_cases h1 : u.val < 32
  · exact pairsOK_spec 16 16 check1 u v (by omega) (by omega)
  by_cases h2 : u.val < 48
  · exact pairsOK_spec 32 16 check2 u v (by omega) (by omega)
  · exact pairsOK_spec 48 16 check3 u v (by omega) (by omega)

theorem idx_lt (s : Fin 10 → F) : idx s < 1024 := by
  have h : idx s ≤ ∑ i : Fin 10, 2 ^ (i : Nat) := by
    unfold idx
    refine Finset.sum_le_sum fun i _ => ?_
    have := ZMod.val_lt (s i)
    calc (s i).val * 2 ^ (i : Nat) ≤ 1 * 2 ^ (i : Nat) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (i : Nat) := one_mul _
  have h2 : ∑ i : Fin 10, 2 ^ (i : Nat) = 1023 := by decide
  omega

theorem cert_wedge (σ : Fin 10 → F) (u v : Fin 6 → F)
    (h : piF (wedgeF u v) = 0 ∨ piF (wedgeF u v) = σ) : dot (certI (idx σ)) (wedgeF u v) = 0 := by
  obtain ⟨n, rfl⟩ := dec_surj u
  obtain ⟨m, rfl⟩ := dec_surj v
  have hp := pairOK_spec n m (allPairs n m)
  rcases h with h | h
  · rcases hp.2 h with h0 | h0 | h0 | h0
    · rw [h0]; simp [dot]
    · rw [h0]; exact cert_S ⟨idx σ, idx_lt σ⟩ 0
    · rw [h0]; exact cert_S ⟨idx σ, idx_lt σ⟩ 1
    · rw [h0]; exact cert_S ⟨idx σ, idx_lt σ⟩ 2
  · have := hp.1; rw [h] at this; exact this

theorem qmc_ge_seven (C : Circuit (Fin 6) (Fin 5)) (hq : C.IsQuadratic) (hC : ComputesQ C) :
    7 ≤ C.size := by
  by_contra hlt
  push Not at hlt
  let a : Fin C.size → Fin 6 → F := fun k => (C.left k).lin
  let b : Fin C.size → Fin 6 → F := fun k => (C.right k).lin
  let w : Fin C.size → Fin 15 → F := fun k => wedgeF (a k) (b k)
  let ρ : Fin 5 → Fin C.size → F := fun j k => (C.out j).gat k
  have hgate : ∀ x k, C.gateVal x k =
      ((C.left k).const + lin6 (a k) x) * ((C.right k).const + lin6 (b k) x) := by
    intro x k
    rw [gateVal_unfold, evalBelow_noGate _ (fun j => (hq k j).1),
      evalBelow_noGate _ (fun j => (hq k j).2)]
    rfl
  have hout : ∀ x j, Qmap x j =
      ((C.out j).const + lin6 (C.out j).lin x) + ∑ k, ρ j k * C.gateVal x k := by
    intro x j
    rw [← hC x j]
    simp [Circuit.outVal, Affine.evalBelow, lin6, ρ]
  have hcoef : ∀ j p, Qlit j p = ∑ k, ρ j k * w k p := by
    intro j p
    rw [← Qm_eq_Qlit]
    show coef (fun x => Qmap x j) p = _
    rw [show (fun x => Qmap x j) = fun x => ((C.out j).const + lin6 (C.out j).lin x) +
        ∑ k, ρ j k * C.gateVal x k from funext fun x => hout x j]
    rw [coef_add, coef_affine, zero_add, coef_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coef_smul]
    congr 1
    simp_rw [hgate]
    exact coef_mul _ _ _ _ p
  -- the map y ↦ Σ_k y_k π(w_k)
  let P : (Fin C.size → F) →ₗ[F] (Fin 10 → F) :=
    { toFun := fun y i => ∑ k, piF (w k) i * y k
      map_add' := by
        intro y z; funext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y; funext i; simp [Finset.mul_sum, mul_left_comm] }
  have hker : ∀ j, ρ j ∈ LinearMap.ker P := by
    intro j
    rw [LinearMap.mem_ker]
    funext i
    show ∑ k, (∑ p, Gm i p * w k p) * ρ j k = 0
    have : ∑ k, (∑ p, Gm i p * w k p) * ρ j k = ∑ p, Gm i p * Qlit j p := by
      simp_rw [hcoef, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact Gm_ann i j
  have hind : LinearIndependent F ρ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply Qlit_indep g
    intro p
    have hk : ∀ k, ∑ j, g j * ρ j k = 0 := fun k => by
      have := congrFun hg k
      simpa [Finset.sum_apply, smul_eq_mul] using this
    calc ∑ j, g j * Qlit j p = ∑ k, (∑ j, g j * ρ j k) * w k p := by
          simp_rw [hcoef, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hk]
  have hfr : Module.finrank F (LinearMap.range P) ≤ 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P
    have h2 : 5 ≤ Module.finrank F (LinearMap.ker P) := by
      have hle : Submodule.span F (Set.range ρ) ≤ LinearMap.ker P :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hker j)
      have := Submodule.finrank_mono hle
      rw [finrank_span_eq_card hind, Fintype.card_fin] at this
      exact this
    rw [Module.finrank_fin_fun] at h1
    omega
  obtain ⟨σ', hσ'⟩ := finrank_le_one_iff.mp hfr
  let σ : Fin 10 → F := σ'
  have hcol : ∀ k, piF (w k) = 0 ∨ piF (w k) = σ := by
    intro k
    obtain ⟨c, hc⟩ := hσ' ⟨P (Pi.single k 1), LinearMap.mem_range_self _ _⟩
    have hPk : P (Pi.single k 1) = piF (w k) := by
      funext i
      show ∑ k', piF (w k') i * (Pi.single k (1 : F) : Fin C.size → F) k' = piF (w k) i
      simp [Pi.single_apply]
    have h' := congrArg Subtype.val hc
    simp only [Submodule.coe_smul] at h'
    rw [hPk] at h'
    fin_cases c
    · left; rw [← h']; show (0 : F) • (σ' : Fin 10 → F) = 0; exact zero_smul _ _
    · right; rw [← h']; show (1 : F) • (σ' : Fin 10 → F) = σ; exact one_smul _ _
  let f := certI (idx σ)
  have hfw : ∀ k, dot f (w k) = 0 := fun k => cert_wedge σ _ _ (hcol k)
  obtain ⟨j, hj⟩ := cert_W ⟨idx σ, idx_lt σ⟩
  have hzero : dot f (Qlit j) = 0 := by
    have : dot f (Qlit j) = ∑ k, ρ j k * dot f (w k) := by
      simp only [dot]
      simp_rw [hcoef, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by ring
    rw [this]
    simp [hfw]
  have : (1 : F) = 0 := by rw [← hj]; exact hzero
  exact absurd this (by decide)

end SixVsSeven
