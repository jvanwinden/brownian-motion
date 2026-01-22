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

lemma IsBrownian.upper_tail {X} (hX : IsBrownian X P) : ∃ C : ℝ≥0, ∀ (t : ℝ≥0) (c : ℝ) (hc : 0 ≤ c),
    P.real {ω | (⨆ s ≤ t, (X s ω : EReal)) ≥ c}
      ≤ C * Real.sqrt (c^2 / (t : ℝ))⁻¹ * Real.exp (-1/2 * (c^2 / (t : ℝ))) := by
  sorry

variable (X : ℝ≥0 → Ω → ℝ) [hX : ProbabilityTheory.IsBrownian X P]

lemma IsBrownian.LIL_upper : ∀ᵐ ω ∂P, limsup (fun t ↦ (X t ω) / √(2 * t * Real.log (Real.log t)) :
    ℝ≥0 → EReal) atTop ≤ 1 := by
  -- introduce notation
  let M := fun t ω ↦ (⨆ s ≤ t, (X s ω : EReal))
  let f := fun (t : ℝ≥0) ↦ (2*t*(t : ℝ).log.log).sqrt
  have loglog_atTop : Filter.Tendsto (fun t : ℝ≥0 ↦ (t : ℝ).log.log) atTop atTop := by
    rw [← Function.comp_def]
    repeat apply Filter.Tendsto.comp Real.tendsto_log_atTop
    simp [Filter.Tendsto]
  -- rewrite limsup inequality in terms of quantifiers
  conv in (_ ≤ _) => rw [limsup_le_iff']
  -- pull quantifiers outside and rewrite the fraction
  obtain ⟨Q,cQ,dQ⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  suffices h : ∀ (c : Q), (1 : ℝ) < c → ∀ᵐ (ω : Ω) ∂P, ∀ᶠ (t : ℝ≥0) in atTop,
      X t ω ≤ c * f t by
    haveI : (Countable Q) := cQ
    simp_rw [← Filter.eventually_imp_distrib_left, ← ae_all_iff] at h
    filter_upwards [h] with ω hω
    refine EReal.forall.2 ⟨(by simp), (by simp),?_⟩
    intro c hc1; norm_cast at hc1
    lift c to ℝ≥0 using by positivity
    rcases Dense.exists_between dQ (by exact_mod_cast hc1) with ⟨r,hrQ,⟨hr1,hry⟩⟩
    filter_upwards [hω ⟨r,hrQ⟩, eventually_gt_atTop 0, loglog_atTop.eventually_ge_atTop 1]
      with _ ht ht0 hll1
    rw [EReal.div_le_iff_le_mul (by positivity) (by apply EReal.coe_ne_top), mul_comm] -- positivity
    norm_cast
    apply le_trans (ht (by exact_mod_cast hr1)) (mul_le_mul _ _ (by positivity) (by positivity))
    all_goals bound
  rw [Subtype.forall]; push_cast
  intro c _ hc
  -- prepare for application of Borel-Cantelli
  suffices h : ∀ᵐ ω ∂P, {n : ℕ | c * f (c ^ n) < M (c^(n+1)) ω}.Finite by
    filter_upwards [h] with ω hω
    rcases (bddAbove_def.1 hω.bddAbove) with ⟨N,hN⟩
    replace hN := fun x ↦ (hN x).mt
    simp only [not_le, Set.mem_setOf_eq, not_lt] at hN
    have h'' := tendsto_pow_atTop_atTop_of_one_lt hc
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c^(N+1)),
      eventually_ge_atTop (c * ⟨(Real.exp 1),_⟩ : ℝ≥0)] with t ht1 ht htce
    rcases exists_nat_pow_near ht1 hc with ⟨n,hn1,hn2⟩
    have hcn : Real.exp 1 ≤ (c ^ n) := by
      trans t / c
      · rw [le_div_iff₀ (by positivity), mul_comm]
        exact_mod_cast htce
      · rw [div_le_iff₀ (by positivity)]
        bound
    have h := calc
      X t ω ≤ M (c^(n+1)) ω := by
        exact le_iSup_of_le t <| le_iSup_of_le (by bound) (by rfl)
      _ ≤ c * f (c^n)   := by
        apply hN n
        suffices (N : ℝ) < (n : ℝ) by exact_mod_cast this
        apply lt_of_add_lt_add_right (a := 1)
        rw [←Real.rpow_lt_rpow_left_iff hc]
        exact lt_of_le_of_lt (by exact_mod_cast ht) (by exact_mod_cast hn2)
      _ ≤ c * (f t)       := by
        -- monotonicity
        apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
        apply EReal.coe_le_coe (Real.sqrt_le_sqrt _)
        push_cast
        apply mul_le_mul _ _ _ (by positivity)
        · apply mul_le_mul (by bound) (by bound) (by positivity) (by positivity)
        · apply Real.log_le_log
          · apply Real.log_pos (lt_of_lt_of_le (by bound) hcn)
          · apply Real.log_le_log (by positivity) (by bound)
        · apply Real.log_nonneg
          rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
          exact hcn
    rw [EReal.coe_nnreal_eq_coe_real] at h
    exact_mod_cast h
  -- apply Borel-Cantelli, rewrite to eventual bound
  let A := fun n : ℕ ↦ {ω | c * f (c ^ n) < M (c^(n+1)) ω}
  apply ae_finite_setOf_mem (s := A)
  conv in (P _) => rw [← MeasureTheory.ofReal_measureReal]
  apply Summable.tsum_ofReal_ne_top
  apply summable_of_isBigO (Real.summable_nat_rpow_inv.2 hc)
  rw [Nat.cofinite_eq_atTop]
  rcases (IsBrownian.upper_tail hX) with ⟨C,h'⟩
  apply Asymptotics.IsBigO.of_bound (C * ((Real.log c) ^ (c : ℝ))⁻¹)
  -- show the eventual bound
  filter_upwards [(loglog_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hc)).eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hll1 instHashableInt16
  -- rewrite and estimate the probability using tail bound
  repeat rw [Real.norm_of_nonneg (by positivity)]
  refine le_trans ?_ (le_trans (h' (c ^ (n + 1)) (c * f (c ^ n)) (by positivity)) ?_)
  · unfold A;
    apply measureReal_mono _ (by finiteness)
    exact fun _ hω ↦ le_of_lt hω.out
  -- simplify fraction
  have hfrac : (c * f (c^n))^2 / ((c ^ (n+1)) : ℝ≥0) = 2 * c * (c ^ n : ℝ).log.log := by
    push_cast
    apply div_eq_of_eq_mul (by positivity)
    simp_rw [mul_pow, pow_add]
    rw [Real.sq_sqrt (by positivity)]
    push_cast; field_simp
  simp_rw [hfrac]
  -- numerical calculation
  conv=> rhs; rw [mul_assoc]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply mul_le_of_le_one_right (by positivity)
    rw [Real.sqrt_le_one, inv_le_one₀ (by positivity)]
    bound
  · field_simp
    conv in Real.exp _ => rw [mul_comm]
    rw [Real.exp_neg, Real.exp_mul, Real.exp_log, Real.log_pow]
    · rw [Real.mul_rpow (by positivity) (by exact le_of_lt (Real.log_pos hc)), mul_inv]
      field_simp; rfl
    · rw [Real.log_pow]
      positivity [Real.log_pos hc]
