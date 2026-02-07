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
import Mathlib.Probability.BorelCantelli

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsBrownian.upper_tail {X} (hX : IsBrownian X P) : ∃ C : ℝ≥0, ∀ (t : ℝ≥0) (c : ℝ) (hc : 0 ≤ c),
    P.real {ω | ⨆ s ≤ t, (X s ω).toEReal ≥ c}
      ≤ C * Real.sqrt (c^2 / (t : ℝ))⁻¹ * Real.exp (-1/2 * (c^2 / (t : ℝ))) := by
  sorry

lemma IsStandardGaussian.tail {X} (hX : HasLaw X (gaussianReal 0 1) P) :
    Asymptotics.IsEquivalent atTop (fun x ↦ P.real {ω | x ≤ X ω})
    (fun x ↦ 1 / x * (-1/2 * x ^ 2).exp) := by
  sorry

lemma filter_atTop_atTop (c : ℝ≥0) (hc0 : 0 < c) :
    Filter.map (fun x ↦ c * x : ℝ≥0 → ℝ≥0) atTop = atTop := by
  apply Filter.map_atTop_eq_of_gc_preorder (mul_right_mono) 0 _
  exact fun d _ ↦ ⟨c⁻¹ * d, ⟨mul_inv_cancel_left₀ (by aesop) d,
    fun _ ↦ (le_inv_mul_iff₀ hc0).symm⟩⟩

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
  -- is there a better way to stick 'a ≤ b' in the middle?
  refine le_trans ?_ <| ((h' (c ^ (n + 1)) (c * f (c ^ n)) (by positivity)).trans ?_)
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
  suffices h : ∀ (c : ℝ), 1 < c → ∀ᵐ ω ∂P, (1 - 1 / c).sqrt - (1 / c.sqrt : ℝ) ≤
      limsup (fun t ↦ (X t ω) / (f t) : ℝ≥0 → EReal) atTop by
    simp_rw [ae_const_le_iff_forall_lt_measure_zero, ← not_lt, ← ae_iff]
    have h' : Filter.Tendsto (fun (r : ℝ) ↦ (1 - 1 / r).sqrt - (1 / r.sqrt)) atTop (nhds 1) := by
      sorry -- the exact expression is subject to change, so hold off on the proof
    intro c hc1
    wlog! hc0 : (0 < c) generalizing c with h
    · replace h := fun (c : ℝ) ↦ h c
      specialize h (1/2) (?_) (by norm_num)
      · apply EReal.coe_lt_coe; bound
      exact h.mono fun _ hω ↦ lt_trans (lt_of_le_of_lt hc0 (by norm_num)) hω
    · lift c to ℝ using by aesop;; norm_cast at hc0 hc1
      apply (Filter.eventually_const (f := atTop (α := ℝ))).1
      filter_upwards [eventually_gt_atTop 1, Eventually.of_forall h,
        h'.eventually <| lt_mem_nhds <| hc1] with r hr0 hr1 hr2
      filter_upwards [hr1 hr0] with ω hω
      exact lt_of_lt_of_le (by exact_mod_cast hr2) hω
  intro c hc1
  lift c to ℝ≥0 using by positivity
  have hc0 : (0 < c) := by positivity [by exact_mod_cast hc1]

  suffices h : ∀ᵐ ω ∂P, (1 - 1 / (c : ℝ)).sqrt ≤
      limsup (fun t ↦ ((X (c * t) ω - X t ω) / f (c * t)).toEReal) atTop by
    have h' : ∀ᵐ ω ∂P,
        limsup (fun t ↦ (-X t ω / f (c * t)).toEReal) atTop
          ≤ (1 / (c : ℝ).sqrt).toEReal := by
      sorry -- consequence of LIL_upper + scaling + symmetry
    filter_upwards [h, h'] with ω hω hω'
    simp_rw [neg_div, EReal.coe_neg, ← Pi.neg_def, EReal.limsup_neg, EReal.neg_le] at hω'
    grw [sub_eq_add_neg, (add_le_add hω hω'), EReal.le_limsup_add]
    apply le_of_eq
    nth_rw 2 [← filter_atTop_atTop c hc0]
    simp_rw [← Filter.limsup_comp, Function.comp_def, ← EReal.coe_div, ← div_sub_div_same,
      EReal.coe_sub, Pi.add_def]
    norm_cast; aesop
  let A := fun n ↦ {ω | (1 - 1 / (c : ℝ)).sqrt ≤
    (X (c ^ (n + 1)) ω - X (c ^ n) ω) / f (c ^ (n + 1))}

  have hM : (t : ℝ≥0) → Measurable (X t) := sorry -- add as hypothesis?

  suffices h : P (Filter.limsup A atTop) = 1 by
    rw [← MeasureTheory.mem_ae_iff_prob_eq_one <| by measurability] at h
    filter_upwards [h] with ω hω
    rw [Filter.mem_limsup_iff_frequently_mem] at hω
    have htend : Tendsto (fun n : ℕ => c ^ n) atTop (atTop : Filter NNReal) :=
      tendsto_pow_atTop_atTop_of_one_lt hc1
    apply le_limsup_of_frequently_le'
    apply Filter.Tendsto.frequently_map _ htend _ hω
    intro n hn
    simpa [EReal.coe_le_coe_iff, mul_comm, pow_add, pow_one] using hn.out
  apply ProbabilityTheory.measure_limsup_eq_one (by measurability)
  all_goals unfold A
  · rw [iIndepSet_iff_iIndep]
    have h' := hX.hasIndepIncrements
    rw [HasIndepIncrements.iff_increments_nat] at h'
    specialize h' (fun n ↦ c ^ n) _
    · apply pow_right_monotone <| le_of_lt <| by exact_mod_cast hc1
    rw [iIndepFun_iff_iIndep] at h'
    have h_le : (n : ℕ) → generateFrom {(A n)} ≤
        MeasurableSpace.comap (fun ω ↦ X (c ^ (n + 1)) ω - X (c ^ n) ω) Real.measurableSpace := by
      -- this proof should be trivial...
      intro n; unfold A
      by_cases! hf : 0 < f (c ^ (n + 1))
      · simp_rw [le_div_iff₀ hf]
        apply generateFrom_singleton_le <| measurableSet_le (by measurability) _
        apply Measurable.of_comap_le (by rfl)
      · simp [le_antisymm hf (by positivity)]
    -- the line below can be replaced by `iIndep_of_iIndep_of_le`
    exact fun s t ht ↦ h' s fun i hi ↦ h_le i (t i) <| ht i hi
  -- convert tsum_eq_top to ¬Summable
  conv in P _ =>
    rw [← MeasureTheory.ofReal_measureReal]
  simp_rw [← ENNReal.ofNNReal_toNNReal, ENNReal.tsum_coe_eq_top_iff_not_summable_coe,
    Real.coe_toNNReal (r := P.real _) (by positivity)]

  have hlogc : 1 < Real.log c := sorry -- get it from before wlog

  let g := fun n : ℕ ↦ (2 * (c ^ n : ℝ).log.log).sqrt
  have h'' : Tendsto (fun n : ℕ ↦ Real.log (c ^ n)) atTop atTop := by
    simp_rw [Real.log_pow]
    apply Filter.Tendsto.atTop_mul_const (by bound)
    apply tendsto_natCast_atTop_atTop
  have hg : Tendsto g atTop atTop := sorry -- elementary limit

  -- rewrite in terms of a standard normal
  suffices h : ¬(Summable (fun n ↦ P.real {ω | g (n) ≤ X 1 ω})) by
    -- shift index
    rw [← summable_nat_add_iff 1 (G := ℝ)] at h
    convert h using 2
    funext n
    have h' : ∀ x, √(1 - 1 / c : ℝ) ≤ x / f (c ^ (n + 1)) ↔
        g (n + 1) ≤ x / (c ^ (n + 1) - c ^ n : ℝ).sqrt := by
      intro x
      unfold f
      conv in 2 * _ => rw [mul_comm]
      rw [mul_assoc, Real.sqrt_mul (by positivity)]
      push_cast
      rw [le_div_iff₀ (by sorry)] -- positivity
      rw [le_div_iff₀ (by sorry)] -- positivity
      rw [← mul_assoc, mul_comm]
      rw [← Real.sqrt_mul' _ (by bound)]
      rw [sub_mul]
      apply iff_of_eq
      congr 4
      · simp
      · rw [pow_add]
        field_simp
    simp_rw [h']
    rw [Measure.real_def, Measure.real_def]
    rw [ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    apply ProbabilityTheory.IdentDistrib.measure_mem_eq _
      (by measurability : MeasurableSet (Set.Ici (g (n + 1))))
    -- we would like to use `hasLaw.identDistrib` but we are behind mathlib
    sorry -- identical distribution
  rw [← IsEquivalent.summable_iff_nat
      (f := fun n ↦ (1 / Real.sqrt 2) * (1 / (Real.log n).sqrt) * (1 / n) * (1 / Real.log c))]
  · -- prove non-summability of elementary function
    rw [summable_mul_right_iff <| one_div_ne_zero <| ne_of_gt <| Real.log_pos hc1]
    simp_rw [mul_assoc]
    rw [summable_mul_left_iff (by positivity)]
    rw [summable_congr_atTop (g₁ := fun n : ℕ ↦ 1 / √(Real.log (max n 2)) * (1 / ↑n))]
    · rw [← summable_condensed_iff_of_nonneg (fun _ ↦ by positivity)]
      · push_cast; field_simp
        rw [summable_congr_atTop (g₁ := fun n : ℕ ↦ 1 / √(Real.log (2 ^ n)))]
        · simp_rw [Real.log_pow]
          conv in √_ => rw [Real.sqrt_mul (by positivity)]
          simp_rw [← one_div_mul_one_div]
          rw [summable_mul_right_iff]
          · simp_rw [Real.sqrt_eq_rpow]
            rw [Real.summable_one_div_nat_rpow]
            norm_num
          · apply ne_of_gt
            positivity
        · filter_upwards [eventually_ge_atTop 1] with n hn
          rw [max_eq_left]; bound
      · intro m n hm0 hmn
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · rw [one_div_le_one_div]
          · apply Real.sqrt_le_sqrt
            apply Real.log_le_log (by positivity)
            · apply max_le_max_right; aesop
          all_goals rw [Real.sqrt_pos]; apply Real.log_pos; simp
        · rw [one_div_le_one_div (by bound) (by positivity)]
          aesop
    · filter_upwards [eventually_ge_atTop 2] with n hn
      rw [max_eq_left]
      aesop
  · -- asymptotic equivalence of elementary functions
    have h' := (IsStandardGaussian.tail <| hX.hasLaw_eval 1).comp_tendsto hg
    simp_rw [Function.comp_def] at h'
    grw [h']
    conv in _ * _ * _ => rw [mul_assoc]
    apply Asymptotics.IsEquivalent.mul
    · unfold g
      simp_rw [one_div_mul_one_div]
      apply Asymptotics.IsEquivalent.div (by rfl)
      conv in √_ * √_ => rw [← Real.sqrt_mul (by positivity)]
      simp_rw [Real.sqrt_eq_rpow]
      -- we want to use `IsEquivalent.rpow` and `IsEquivalent.log`
      -- but we are behind Mathlib
      sorry -- asymptotic equivalence
    · -- here we actually have an identity
      apply Filter.EventuallyEq.isEquivalent
      filter_upwards [h''.eventually_ge_atTop 1] with n hn
      rw [Real.sq_sqrt (by bound)] -- positivity
      field_simp
      rw [Real.exp_neg]
      rw [Real.exp_log <| lt_of_lt_of_le (by norm_num) hn] -- positivity
      rw [Real.log_pow]
      field_simp
