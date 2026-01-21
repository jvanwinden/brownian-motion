import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Gaussian.GaussianProcess
import BrownianMotion.Gaussian.Moment
import BrownianMotion.Gaussian.ProjectiveLimit
import BrownianMotion.Gaussian.BrownianMotion
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Notation
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.PSeries

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable (X : ℝ≥0 → Ω → ℝ) [ProbabilityTheory.IsBrownian X P]

lemma IsBrownian.upper_tail {X} (hX : IsBrownian X P) : ∃ C : ℝ≥0, ∀ (t : ℝ≥0) (c : ℝ) (hc : 0 ≤ c),
    P.real {ω | (⨆ s ≤ t, (X s ω : EReal)) ≥ c}
      ≤ C * Real.sqrt (c^2 / (t : ℝ))⁻¹ * Real.exp (-1/2 * (c^2 / (t : ℝ))) := by
  sorry

lemma IsBrownian.LIL_upper [IsProbabilityMeasure P] [hX : IsBrownian X P] : ∀ᵐ ω ∂P,
    limsup (fun t ↦ (((X t ω) / √(2 * t * Real.log (Real.log t))) : EReal)) atTop ≤ 1 := by
  -- define a slightly nicer function f'
  let loglog := fun (t : ℝ≥0) ↦ (t : ℝ).log.log
  let f := fun (t : ℝ≥0) ↦ (2*t*(loglog t)).sqrt
  let M := fun t ω ↦ (⨆ s ≤ t, (X s ω : EReal))

  -- rewrite limsup inequality in terms of quantifiers
  conv => enter [1, ω]; rw [limsup_le_iff']

  -- pull quantifiers outside and rewrite the fraction
  obtain ⟨Q,cQ,dQ⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  suffices h : ∀ (c : Q), (1 : ℝ≥0) < c → ∀ᵐ (ω : Ω) ∂P, ∀ᶠ (t : ℝ≥0) in atTop,
      X t ω ≤ c * f t by
    haveI : (Countable Q) := cQ
    simp_rw [← Filter.eventually_imp_distrib_left, ← ae_all_iff] at h
    filter_upwards [h] with ω hω
    rw [EReal.forall]
    refine ⟨(by simp), (by simp),?_⟩
    intro y hy1; norm_cast at hy1
    have hy0 : (0 ≤ y) := by bound
    lift y to ℝ≥0 using hy0
    rcases Dense.exists_between dQ (by exact_mod_cast hy1) with ⟨r,hrQ,⟨hr1,hry⟩⟩
    filter_upwards [hω ⟨r,hrQ⟩] with t ht
    rw [EReal.div_le_iff_le_mul (by sorry) (by apply EReal.coe_ne_top), mul_comm]
    norm_cast
    apply le_trans (ht (by exact_mod_cast hr1)) (mul_le_mul _ _ (by positivity) _)
    all_goals bound
  rw [Subtype.forall]; push_cast
  intro c _ hc; norm_cast at hc

  -- prepare for application of Borel-Cantelli
  suffices h : ∀ᵐ ω ∂P, {n : ℕ | c * f (c ^ n) < M (c^(n+1)) ω}.Finite by
    filter_upwards [h] with ω hω
    rcases (bddAbove_def.1 hω.bddAbove) with ⟨N,hN⟩
    replace hN := fun x ↦ (hN x).mt
    simp at hN
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c^(N+1))] with t ht1 ht
    rcases exists_nat_pow_near (x := t) ht1 hc with ⟨n,hn1,hn2⟩
    have h := calc
      X t ω ≤ M (c^(n+1)) ω := by
        apply le_iSup_of_le t; apply le_iSup_of_le
        · rfl
        · exact le_of_lt hn2
      _ ≤ c * f (c^n)   := by
        specialize hN n
        apply hN
        suffices (N : ℝ) < (n : ℝ) by exact_mod_cast this
        apply lt_of_add_lt_add_right (a := 1)
        rw [←Real.rpow_lt_rpow_left_iff hr]; push_cast
        exact lt_of_le_of_lt (by exact_mod_cast ht) (by exact_mod_cast hn2)
      _ ≤ c * (f t)       := by
        apply mul_le_mul_right
        unfold f; norm_cast
        apply mul_le_mul _ _ (by bound) (by bound)
        · rw [NNReal.sqrt_le_sqrt]; bound
        · apply Real.toNNReal_monotone
          apply loglog_mono
          bound
    sorry

  -- apply Borel-Cantelli
  let A := fun n : ℕ ↦ {ω | c * f (c ^ n) < M (c^(n+1)) ω}
  apply ae_finite_setOf_mem (s := A)

  -- prove summability
  rcases (IsBrownian.upper_tail hX) with ⟨C,h'⟩
  conv => enter [1, 1, i]; rw [← MeasureTheory.ofReal_measureReal]
  apply Summable.tsum_ofReal_ne_top
  apply summable_of_isBigO (Real.summable_nat_rpow_inv.2 hc)
  rw [Nat.cofinite_eq_atTop]

  -- do the bound
  apply Asymptotics.IsBigO.of_bound (C * ((Real.log c) ^ (c : ℝ))⁻¹)
  filter_upwards [eventually_ge_atTop 1] with n hn

  -- collect n-based facts
  specialize h' (c ^ (n + 1)) (c * f (c ^ n)) (by positivity)
  have c2t_eq : (c * f (c^n))^2 / ((c ^ (n+1)) : ℝ≥0) = 2 * c * (loglog (c^n)) := by
    push_cast
    apply div_eq_of_eq_mul (by aesop)
    push_cast
    simp_rw [mul_pow, pow_add]
    rw [Real.sq_sqrt (by sorry)]
    push_cast; field_simp

  -- rewrite and estimate the probability
  simp_rw [c2t_eq] at h'
  repeat rw [Real.norm_of_nonneg (by positivity)]
  trans P.real {ω | c * f (c ^ n) ≤ M (c^(n+1)) ω}
  · unfold A;
    apply measureReal_mono _ (by finiteness)
    exact fun _ hω ↦ le_of_lt hω.out
  apply le_trans h'

  -- numerical calculation
  conv => enter [2]; rw [mul_assoc]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply mul_le_of_le_one_right (by positivity)
    rw [Real.sqrt_le_one, inv_le_one₀ ?_]
    · sorry
    · sorry
  · field_simp
    rw [Real.exp_neg]
    conv in Real.exp _ => rw [mul_comm]
    rw [Real.exp_mul, Real.exp_log]
    · push_cast
      simp_rw [Real.log_pow]
      rw [Real.mul_rpow (by positivity) (by exact le_of_lt (Real.log_pos hc)), mul_inv]
      field_simp; rfl
    · push_cast
      rw [Real.log_pow]
      positivity [Real.log_pos hc]
