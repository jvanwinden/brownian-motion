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
import Mathlib.Order.Filter.Basic

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsBrownian.upper_tail {X} (hX : IsBrownian X P) : ∃ C : ℝ≥0, ∀ (t : ℝ≥0) (c : ℝ) (hc : 0 ≤ c),
    P.real {ω | ⨆ s ≤ t, (X s ω).toEReal ≥ c}
      ≤ C * Real.sqrt (c^2 / (t : ℝ))⁻¹ * Real.exp (-1/2 * (c^2 / (t : ℝ))) := by
  sorry

variable (X : ℝ≥0 → Ω → ℝ) [hX : ProbabilityTheory.IsBrownian X P]

lemma IsBrownian.LIL_upper : ∀ᵐ ω ∂P, limsup (fun t ↦
    ((X t ω) / (2 * t * (t : ℝ).log.log).sqrt).toEReal) atTop ≤ 1 := by
  -- Introduce notation
  let M := fun t ω ↦ (⨆ s ≤ t, (X s ω : EReal))
  let f := fun (t : ℝ≥0) ↦ (2 * t * (t : ℝ).log.log).sqrt
  have loglog_atTop : Filter.Tendsto (fun t : ℝ≥0 ↦ (t : ℝ).log.log) atTop atTop := by
    rw [← Function.comp_def]
    repeat apply Filter.Tendsto.comp Real.tendsto_log_atTop
    simp [Filter.Tendsto]
  -- Rewrite limsup inequality in terms of quantifiers which do not depend on `ω`
  simp_rw [ae_le_const_iff_forall_gt_measure_zero, ← not_lt, ← ae_iff]
  suffices h : ∀ (c : ℝ≥0), 1 < (c : ℝ) → ∀ᵐ (ω : Ω) ∂P, ∀ᶠ (t : ℝ≥0) in atTop,
      X t ω ≤ c * f t by
    intro _ hc
    rcases EReal.lt_iff_exists_real_btwn.mp hc with ⟨b,hb⟩
    lift b to ℝ≥0 using by positivity [by exact_mod_cast hb.1]
    filter_upwards [h b <| by exact_mod_cast hb.1] with _ hω
    apply lt_of_le_of_lt _ hb.2
    apply limsup_le_of_le (hf := by isBoundedDefault)
    filter_upwards [hω] with t ht
    exact EReal.coe_le_coe <| div_le_of_le_mul₀ (by positivity) (by positivity) ht
  intro c hc
  -- Prepare for application of Borel-Cantellli
  suffices h : ∀ᵐ ω ∂P, {n : ℕ | c * f (c ^ n) < M (c^(n+1)) ω}.Finite by
    filter_upwards [h] with ω hω
    rcases (bddAbove_def.1 hω.bddAbove) with ⟨N,hN⟩
    replace hN := fun x ↦ (hN x).mt
    simp only [not_le, Set.mem_setOf_eq, not_lt] at hN
    have h'' := tendsto_pow_atTop_atTop_of_one_lt hc
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c^(N+1)),
      eventually_ge_atTop (c * ⟨Real.exp 1,_⟩ : ℝ≥0)] with t ht1 ht htce
    rcases exists_nat_pow_near ht1 hc with ⟨n,hn1,hn2⟩
    have hcn : Real.exp 1 ≤ (c ^ n) := by
      trans t / c
      · rw [le_div_iff₀ (by positivity), mul_comm]
        exact_mod_cast htce
      · rw [div_le_iff₀ (by positivity)]
        bound
    exact_mod_cast calc
      X t ω ≤ M (c^(n+1)) ω := le_iSup_of_le t <| le_iSup_of_le (by bound) (by rfl)
      _ ≤ c * f (c^n) := by
        apply hN n
        rify
        apply lt_of_add_lt_add_right (a := 1)
        rw [←Real.rpow_lt_rpow_left_iff hc]
        exact_mod_cast lt_of_le_of_lt ht hn2
      _ ≤ (c : ℝ) * (f t) := by
        -- f is (eventually) monotone
        apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
        apply EReal.coe_le_coe (Real.sqrt_le_sqrt _)
        push_cast
        apply mul_le_mul (mul_le_mul (by bound) (by bound) (by positivity) (by positivity))
          _ _ (by positivity)
        · apply Real.log_le_log (Real.log_pos _) (Real.log_le_log (by positivity) (by bound))
          exact lt_of_lt_of_le (by bound) hcn
        · apply Real.log_nonneg
          rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
          exact hcn
  -- Apply Borel-Cantelli and rewrite to an asymptotic bound
  apply ae_finite_setOf_mem (s := fun n : ℕ ↦ {ω | c * f (c ^ n) < M (c^(n+1)) ω})
  conv in (P _) => rw [← MeasureTheory.ofReal_measureReal]
  apply Summable.tsum_ofReal_ne_top
  apply summable_of_isBigO (Real.summable_nat_rpow_inv.2 hc)
  rw [Nat.cofinite_eq_atTop]
  rcases (IsBrownian.upper_tail hX) with ⟨C,h'⟩
  apply Asymptotics.IsBigO.of_bound <| C * ((Real.log c) ^ (c : ℝ))⁻¹
  filter_upwards [(loglog_atTop.comp <| tendsto_pow_atTop_atTop_of_one_lt hc).eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hll1 instHashableInt16
  -- Apply Gaussian tail bound and simplify
  repeat rw [Real.norm_of_nonneg (by positivity)]
  refine le_trans ?_ <| le_trans (h' (c ^ (n + 1)) (c * f (c ^ n)) (by positivity)) ?_
  · exact measureReal_mono (fun _ hω ↦ le_of_lt hω.out) (by finiteness)
  have hfrac : (c * f (c^n))^2 / ((c ^ (n+1)) : ℝ≥0) = 2 * c * (c ^ n : ℝ).log.log := by
    push_cast
    apply div_eq_of_eq_mul (by positivity)
    simp_rw [mul_pow, pow_add]
    rw [Real.sq_sqrt (by positivity)]
    field_simp; rfl
  simp_rw [hfrac]
  -- Show elementary inequality
  conv => rhs; rw [mul_assoc]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply mul_le_of_le_one_right (by positivity)
    rw [Real.sqrt_le_one, inv_le_one₀ (by positivity)]
    bound
  · field_simp
    conv in Real.exp _ => rw [mul_comm]
    rw [Real.exp_neg, Real.exp_mul, Real.exp_log, Real.log_pow]
    · rw [Real.mul_rpow (by positivity) <| le_of_lt <| Real.log_pos hc, mul_inv]
      field_simp; rfl
    · rw [Real.log_pow]
      positivity [Real.log_pos hc]

lemma IsBrownian.LIL_lower : ∀ᵐ ω ∂P, 1 ≤ limsup (fun t ↦ (X t ω) / (2 * t * (t : ℝ).log.log).sqrt :
    ℝ≥0 → EReal) atTop := by
  let f := fun (t : ℝ≥0) ↦ (2 * t * (t : ℝ).log.log).sqrt
  -- Rewrite the inequality into a nice form with the quantifier outside
  suffices h : ∀ (c : ℝ), 0 < c → ∀ᵐ ω ∂P, (1 - 1 / c).sqrt - (1 / c.sqrt : ℝ) ≤
      limsup (fun t ↦ (X t ω) / (f t) : ℝ≥0 → EReal) atTop by
    simp_rw [ae_const_le_iff_forall_lt_measure_zero, ← not_lt, ← ae_iff]
    have h' : Filter.Tendsto (fun (r : ℝ) ↦ (1 - 1 / r).sqrt - (1 / r.sqrt)) atTop (nhds 1) := by
      sorry -- the exact expression is subject to change, so hold off on the proof
    intro c hc1
    wlog! hc0 : (0 < c) generalizing c with h
    · replace h := fun (c : ℝ) ↦ h c
      specialize h (1/2) (by sorry) (by norm_num)
      exact h.mono fun _ hω ↦ lt_trans (lt_of_le_of_lt hc0 (by bound)) hω
    · lift c to ℝ using by aesop;; norm_cast at hc0 hc1
      apply (Filter.eventually_const (f := atTop (α := ℝ))).1
      filter_upwards [eventually_gt_atTop 0, Eventually.of_forall h,
        h'.eventually <| lt_mem_nhds <| hc1] with r hr0 hr1 hr2
      filter_upwards [hr1 hr0] with ω hω
      apply lt_of_lt_of_le _ hω
      exact_mod_cast hr2
  intro c hc0
  lift c to ℝ≥0 using by positivity
  suffices h : ∀ᵐ ω ∂P, (1 - 1 / (c : ℝ)).sqrt ≤
      limsup (fun t ↦ (X (c * t) ω - X t ω) / f (c * t) : ℝ≥0 → EReal) atTop by
    have h' : ∀ᵐ ω ∂P, limsup (fun t ↦ (X t ω) / f (c * t) : ℝ≥0 → EReal) atTop
        ≤ (1 / (c : ℝ).sqrt : ℝ) := by
      sorry -- Consequence of LIL_upper
    filter_upwards [h, h'] with ω hω hω'
    sorry -- Combine inequalities in standard way
  -- use a ≤ f (c ^ n) i.o. → a ≤ limsup f t
  -- apply second Borel-Cantelli lemma (using independence)
  -- use Gaussianity to get lower bound
  -- show lower bound is non-summable
  sorry
