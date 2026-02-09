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

theorem EReal.limsup_const_mul {α : Type u_1} {f : Filter α}
    {u : α → EReal} {a : EReal} (h₁ : 0 < a) (h₂ : a ≠ ⊤) :
    Filter.limsup (fun x => a * u x) f = a * Filter.limsup u f := by
  simp_rw [mul_comm (a := a)]
  apply eq_of_le_of_ge
  · rw [Filter.limsup_le_iff]
    intro r hr
    rw [gt_iff_lt] at hr
    simp_rw [← EReal.lt_div_iff (by aesop) (by aesop)] at hr ⊢
    apply Filter.eventually_lt_of_limsup_lt (hu := by isBoundedDefault) hr
  · rw [Filter.le_limsup_iff]
    intro r hr
    simp_rw [← EReal.div_lt_iff (by aesop) (by aesop)] at hr ⊢
    apply Filter.frequently_lt_of_lt_limsup (hu := by isBoundedDefault) hr

-- already upstreamed to mathlib
theorem iIndep_of_iIndep_of_le {ι} {m₁ m₂ : ι → MeasurableSpace Ω}
    (h_indep : iIndep m₂ P) (h_le : ∀ i, m₁ i ≤ m₂ i) : iIndep m₁ P :=
  fun s t ht ↦ h_indep s fun i hi ↦ h_le i (t i) <| ht i hi

-- already upstreamed to mathlib
theorem hasLaw.identDistrib {α β γ} {f : α → γ} {g : β → γ}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {κ : Measure γ} (h₀ : HasLaw f κ μ)
    (h₁ : HasLaw g κ ν) : IdentDistrib f g μ ν :=
  ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩

lemma IsBrownian.neg {X} (hX : IsBrownian X P) :
    IsBrownian (fun t ω ↦ -(X t ω)) P := by
  sorry

lemma IsBrownian.upper_tail {X} (hX : IsBrownian X P) : ∃ C : ℝ≥0, ∀ (t : ℝ≥0) (c : ℝ) (hc : 0 ≤ c),
    P.real {ω | ⨆ s ≤ t, (X s ω).toEReal ≥ c}
      ≤ C * Real.sqrt (c^2 / (t : ℝ))⁻¹ * Real.exp (-1/2 * (c^2 / (t : ℝ))) := by
  sorry

lemma IsBrownian.reflection {X} (hX : IsBrownian X P) (t : ℝ≥0) (c : ℝ) (hc : 0 < c)
    : P {ω | c ≤ ⨆ s ≤ t, (X s ω).toEReal} = 2 * P {ω | c ≤ X t ω} := sorry

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

lemma IsBrownian.LIL_lower (h_meas : ∀ t, Measurable (X t)) :
    ∀ᵐ ω ∂P, 1 ≤ limsup (fun t ↦ (X t ω) / (2 * t * (t : ℝ).log.log).sqrt : ℝ≥0 → EReal) atTop := by
  let f := fun (t : ℝ≥0) ↦ (2 * t * (t : ℝ).log.log).sqrt
  -- Rewrite the inequality into a nice form with the quantifier outside
  suffices h : ∀ (c : ℝ), 1 < c → 1 < Real.log c → ∀ᵐ ω ∂P, (1 - 1 / c).sqrt - (1 / c.sqrt : ℝ) ≤
      limsup (fun t ↦ (X t ω) / (f t) : ℝ≥0 → EReal) atTop by
    simp_rw [ae_const_le_iff_forall_lt_measure_zero, ← not_lt, ← ae_iff]
    have h' : Filter.Tendsto (fun (r : ℝ) ↦ (1 - 1 / r).sqrt - (1 / r.sqrt)) atTop (nhds 1) := by
      rw [(by simp : nhds (1 : ℝ) = nhds (Real.sqrt (1 - 0) - 0))]
      apply Filter.Tendsto.sub
      · apply Filter.Tendsto.sqrt
        apply Filter.Tendsto.sub (by aesop)
        apply Filter.Tendsto.const_div_atTop <| tendsto_id
      · apply Filter.Tendsto.const_div_atTop <| Real.tendsto_sqrt_atTop
    intro c hc1
    wlog! hc0 : (0 < c) generalizing c with h
    · replace h := fun (c : ℝ) ↦ h c
      specialize h (1/2) (?_) (by norm_num)
      · apply EReal.coe_lt_coe; bound
      exact h.mono fun _ hω ↦ lt_trans (lt_of_le_of_lt hc0 (by norm_num)) hω
    · lift c to ℝ using by aesop;; norm_cast at hc0 hc1
      apply (Filter.eventually_const (f := atTop (α := ℝ))).1
      filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 1,
      Eventually.of_forall h, h'.eventually <| lt_mem_nhds <| hc1] with r hr1 hlogr hrimp hrc
      filter_upwards [hrimp hr1 hlogr] with ω hω
      exact lt_of_lt_of_le (by exact_mod_cast hrc) hω
  intro c hc1 hlogc
  lift c to ℝ≥0 using by positivity
  have hc0 : (0 < c) := by positivity [by exact_mod_cast hc1]

  -- Rewrite in terms of limsup of difference
  suffices h : ∀ᵐ ω ∂P, (1 - 1 / (c : ℝ)).sqrt ≤
      limsup (fun t ↦ ((X t ω - X (t / c) ω) / f t).toEReal) atTop by
    have h' : ∀ᵐ ω ∂P,
        limsup (fun t ↦ (-X (t / c) ω / f (t)).toEReal) atTop
          ≤ (1 / (c : ℝ).sqrt).toEReal := by
      convert IsBrownian.LIL_upper (X := fun t ω ↦ (c : ℝ).sqrt * (-X (t / c) ω)) using 1
      · funext ω
        simp_rw [← mul_div, EReal.coe_mul]
        rw [EReal.limsup_const_mul (by positivity) (by aesop)]
        rw [mul_comm, ← EReal.le_div_iff_mul_le (by positivity) (by aesop)]
        congr
      · infer_instance
      · have hnegX : IsBrownian (fun t ω ↦ - X t ω) P := IsBrownian.neg hX
        have hsX := hnegX.smul (c := (1 / c)) (by positivity)
        convert hsX using 2
        funext ω
        field_simp
        congr 1
        rw [mul_assoc, mul_comm, mul_assoc, ← Real.sqrt_mul (by positivity)]
        push_cast; field_simp; norm_num
    filter_upwards [h, h'] with ω hω hω'
    simp_rw [neg_div, EReal.coe_neg, ← Pi.neg_def, EReal.limsup_neg, EReal.neg_le] at hω'
    grw [sub_eq_add_neg, (add_le_add hω hω'), EReal.le_limsup_add]
    apply le_of_eq
    simp_rw [← EReal.coe_div, ← div_sub_div_same,
      EReal.coe_sub, Pi.add_def]
    norm_cast; aesop
  -- auxiliary definitions
  let g := fun x ↦ (2 * (x : ℝ).log.log).sqrt
  let A := fun n ↦ {ω | g (c ^ (n + 1)) ≤
    (X (c ^ (n + 1)) ω - X (c ^ n) ω) / Real.sqrt (c ^ (n + 1) - c ^ n)}
  -- prepare for application of Borel-Cantelli
  suffices h : P (Filter.limsup A atTop) = 1 by
    rw [← MeasureTheory.mem_ae_iff_prob_eq_one <| by measurability] at h
    filter_upwards [h] with ω hω
    rw [Filter.mem_limsup_iff_frequently_mem] at hω
    apply le_limsup_of_frequently_le'
    apply Filter.Tendsto.frequently_map _ (_ : Tendsto (fun n ↦ c ^ (n + 1)) atTop atTop) _ hω
    · simp_rw [pow_add]
      apply Filter.Tendsto.atTop_mul_const (by positivity)
      exact tendsto_pow_atTop_atTop_of_one_lt hc1
    intro n hn
    replace hn := hn.out
    unfold f A g at *; push_cast at *
    -- simple rewrite
    simp_rw [Real.log_pow, pow_add] at *; push_cast at *
    rw [EReal.coe_le_coe_iff, le_div_iff₀ <| Real.sqrt_pos_of_pos <| by bound]
    rw [le_div_iff₀ (Real.sqrt_pos_of_pos <| by aesop)] at hn
    convert hn using 1
    · rw [← Real.sqrt_mul (by bound), ← Real.sqrt_mul' _ (by bound)]
      field_simp
    · field_simp
  apply ProbabilityTheory.measure_limsup_eq_one (by measurability)
  all_goals unfold A
  · -- show independence
    conv in g _ ≤ _ => rw [le_div_iff₀ (Real.sqrt_pos_of_pos <| by rw [pow_add]; aesop)]
    rw [iIndepSet_iff_iIndep]
    have h' := hX.hasIndepIncrements
    rw [HasIndepIncrements.iff_increments_nat] at h'
    specialize h' (fun n ↦ c ^ n) _
    · apply pow_right_monotone <| le_of_lt <| by exact_mod_cast hc1
    rw [iIndepFun_iff_iIndep] at h'
    apply iIndep_of_iIndep_of_le h' _
    intro n
    apply generateFrom_singleton_le <| measurableSet_le (by measurability) _
    apply Measurable.of_comap_le (by rfl)
  -- convert to sum of reals
  conv in P _ =>
    rw [← MeasureTheory.ofReal_measureReal]
  simp_rw [← ENNReal.ofNNReal_toNNReal, ENNReal.tsum_coe_eq_top_iff_not_summable_coe,
    Real.coe_toNNReal (r := P.real _) (by positivity)]
  -- rewrite in terms of a standard normal
  suffices h : ¬(Summable (fun n ↦ P.real {ω | g (c ^ (max 1 n)) ≤ X 1 ω})) by
    -- shift index
    rw [← summable_nat_add_iff 1 (G := ℝ)] at h
    convert h using 2
    funext n
    rw [max_eq_right (by bound)]
    rw [Measure.real_def, Measure.real_def]
    rw [ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    apply ProbabilityTheory.IdentDistrib.measure_mem_eq _
      (by measurability : MeasurableSet (Set.Ici (g (c ^ (n + 1)))))
    apply hasLaw.identDistrib _ (hX.hasLaw_eval 1)
    -- need scalar multiplication for hasLaw, then apply hasLaw_preBrownian_sub
    sorry -- determine law of `X (c ^ (n + 1)) - X (c ^ n)`
  -- apply limit comparison test
  rw [← IsEquivalent.summable_iff_nat
      (f := fun n ↦ (1 / (g (c ^ (max 1 n)))) * (-1/2 * (g (c ^ (max 1 n))) ^ 2).exp)]; swap
  · -- show asymptotic equivalence
    apply ((IsStandardGaussian.tail <| hX.hasLaw_eval 1).comp_tendsto _).symm
    apply Real.tendsto_sqrt_atTop.comp
    apply Filter.Tendsto.const_mul_atTop (by norm_num)
    apply Real.tendsto_log_atTop.comp
    apply Real.tendsto_log_atTop.comp
    apply tendsto_pow_atTop_atTop_of_one_lt hc1 |>.congr'
    exact eventually_ge_atTop 1|>.mono <| fun _ hn ↦ by simp [max_eq_right hn]
  · -- show non-summability of elementary function
    unfold g
    simp_rw [Real.log_pow]
    conv in √_ ^ 2 => rw [Real.sq_sqrt (by bound)]
    field_simp
    simp_rw [Real.exp_neg]
    conv in Real.exp _ => rw [Real.exp_log (by bound)]
    conv in √_ => rw [Real.sqrt_mul (by positivity)]
    field_simp
    simp_rw [← one_div_mul_one_div]
    simp_rw [mul_comm (b := 1 / Real.log c), mul_assoc]
    rw [summable_mul_left_iff (by positivity)]
    simp_rw [← mul_assoc, mul_comm (b := 1 / Real.sqrt 2), mul_assoc]
    rw [summable_mul_left_iff (by positivity)]
    conv in Real.log _ => rw [Real.log_mul (by positivity) (by positivity)]
    -- apply Cauchy condensation test
    rw [← summable_condensed_iff_of_nonneg (fun _ ↦ by positivity)]; swap
    all_goals push_cast
    · -- antitone side condition of condensation test
      intro m n hm0 hmn
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · rw [one_div_le_one_div (by aesop) (by aesop)]
        apply max_le_max_left; aesop
      rw [one_div_le_one_div _ _]
      · apply Real.sqrt_le_sqrt
        apply add_le_add (Real.log_le_log (by positivity) <| max_le_max_left _ (by aesop)) _
        apply Real.log_le_log (by positivity) (by rfl)
      all_goals
      rw [Real.sqrt_pos]
      apply (lt_add_of_nonneg_of_lt (by bound) (Real.log_pos (by assumption)))
    repeat conv in max _ _ => rw [max_eq_right (by bound)]
    field_simp
    simp_rw [Real.log_pow]
    -- apply limit comparison test again
    rw [← IsEquivalent.summable_iff_nat (f := fun k : ℕ ↦ 1 / Real.sqrt (k * Real.log 2))]
    · conv in √_ => rw [Real.sqrt_mul (by positivity)]
      simp_rw [← one_div_mul_one_div, Real.sqrt_eq_rpow]
      rw [summable_mul_right_iff (by positivity), Real.summable_one_div_nat_rpow]
      norm_num
    · apply Asymptotics.isEquivalent_of_tendsto_one
      rw [Pi.div_def]; field_simp
      conv in _ / _ => rw [← Real.sqrt_div' _ (by positivity)]
      rw [(by simp : nhds 1 = nhds (Real.sqrt (1 + 0)))]
      simp_rw [add_div]
      apply Filter.Tendsto.sqrt
      apply Filter.Tendsto.add
      · apply Filter.Tendsto.congr' (f₁ := fun x ↦ 1) _ (by aesop)
        filter_upwards [eventually_gt_atTop 0] with n hn using by field_simp
      · apply Filter.Tendsto.const_div_atTop
        rw [Filter.tendsto_mul_const_atTop_iff_pos]
        · positivity
        exact tendsto_natCast_atTop_atTop
