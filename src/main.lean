import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral
import analysis.special_functions.exp_log
import analysis.special_functions.trigonometric
import topology.uniform_space.compact_separated
import geometry.euclidean.triangle
import integral_limits

noncomputable theory

open interval_integral set filter measure_theory
open_locale topological_space

def f : ℝ → ℝ := λ x, ∫ t in 0..x, real.exp (-t^2)

def g : ℝ → ℝ := λ x, ∫ t in 0..1, (real.exp (-(1+t^2)*x^2))/(1+t^2)

def h : ℝ → ℝ := λ x, g x + (f^2) x

lemma interval_integral_mono {μ : measure ℝ} {f g : ℝ → ℝ} {a b : ℝ}
  (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) 
  (hab : a ≤ b) (h : f ≤ g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
sorry --proven in PR #6292

lemma is_const_of_deriv_eq_zero {F : Type*} 
  [normed_group F] [normed_space ℝ F] {f : ℝ → F} (hf : differentiable ℝ f) 
  (hz : ∀ x, deriv f x = 0) : ∀ x y, f x = f y :=
begin
  apply is_const_of_fderiv_eq_zero hf (λ x, _),
  rw [← deriv_fderiv, hz x],
  ext u,
  simp
end

lemma exists_has_deriv_at_eq_slope_interval (f f' : ℝ → ℝ) {a b : ℝ}
  (hab : a ≠ b) (hf : continuous_on f (interval a b))
  (hff' : ∀ (x : ℝ), x ∈ Ioo (min a b) (max a b) → has_deriv_at f (f' x) x) :
  (∃ (c : ℝ) (H : c ∈ Ioo (min a b) (max a b)), f' c = (f b - f a) / (b - a)) :=
begin
  by_cases hlt : a < b;
  [skip, have hlt : b < a := lt_of_le_of_ne (le_of_not_lt hlt) hab.symm];
  rw interval at *;
  [rw min_eq_left_of_lt hlt at *, rw min_eq_right_of_lt hlt at *];
  [rw max_eq_right_of_lt hlt at *, rw max_eq_left_of_lt hlt at *];
  convert exists_has_deriv_at_eq_slope f f' hlt hf hff',
  conv in (_ / _) { rw [← neg_div_neg_eq, neg_sub, neg_sub] }
end

lemma has_deriv_at_parametric {a b : ℝ} (hab : a < b) (f f' : ℝ → ℝ → ℝ) 
  (hff' : ∀ x t, has_deriv_at (λ u, f u t) (f' x t) x)
  (hf : continuous ↿f) (hf' : continuous ↿f') (x₀ : ℝ) :
has_deriv_at (λ x, ∫ t in a..b, f x t) (∫ t in a..b, f' x₀ t) x₀ :=
begin
  refine has_deriv_within_at.has_deriv_at _ (Icc_mem_nhds (sub_one_lt x₀) (lt_add_one x₀)),
  have compact_ab : is_compact (interval a b) := compact_Icc,
  have compact_cd : is_compact (Icc (x₀-1) (x₀+1)) := compact_Icc,
  have := (compact_cd.prod compact_ab).uniform_continuous_on_of_continuous hf'.continuous_on,
  rw [has_deriv_within_at_iff_tendsto_slope, metric.tendsto_nhds_within_nhds],
  intros ε hε,
  rw metric.uniform_continuous_on_iff at this,
  specialize this ((ε/2)/(b-a)) (div_pos (by linarith) (by linarith)),
  rcases this with ⟨δ, hδ, this⟩,
  use [δ, hδ],
  rintros y₀ ⟨⟨hy₁, hy₂⟩, hy₃ : y₀ ≠ x₀⟩ hy₀x₀,
  have key₁ := λ (t : ℝ), exists_has_deriv_at_eq_slope_interval (λ x, f x t) (λ x, f' x t) hy₃.symm 
    (@continuous_uncurry_right _ _ _ _ _ _ f t hf).continuous_on (λ x hx, hff' x t),
  choose u hu using key₁,
  have key₂ : ∀ t, dist (u t) x₀ < δ,
  { intro t,
    rw [real.dist_eq, abs, max_lt_iff] at ⊢ hy₀x₀,
    rcases hu t with ⟨⟨ht₁, ht₂⟩, _⟩,
    by_cases hl : x₀ < y₀;
    [skip, push_neg at hl];
    [rw min_eq_left_of_lt hl at ht₁, rw min_eq_right hl at ht₁];
    [rw max_eq_right_of_lt hl at ht₂, rw max_eq_left hl at ht₂];
    split;
    linarith },
  have key₃ : Ioo (min x₀ y₀) (max x₀ y₀) ⊆ Icc (x₀-1) (x₀+1),
  { by_cases hl : x₀ < y₀;
    [skip, push_neg at hl];
    [rw min_eq_left_of_lt hl, rw min_eq_right hl];
    [rw max_eq_right_of_lt hl, rw max_eq_left hl];
    rintros a ⟨ha₁, ha₂⟩;
    split;
    linarith },
  have key₄ : ∀ x, continuous (f x) := λ x, @continuous_uncurry_left _ _ _ _ _ _ f x hf,
  have key₅ : continuous (λ (t : ℝ), (y₀ - x₀)⁻¹ * (f y₀ t - f x₀ t)) :=
    continuous_const.mul ((key₄ y₀).sub (key₄ x₀)),
  have key₅' : continuous (λ (t : ℝ), (y₀ - x₀)⁻¹ • (f y₀ t - f x₀ t)) := key₅,
  have key₆ : continuous (λ (t : ℝ), f' (u t) t),
  { convert key₅,
    ext t,
    rw [(hu t).2, div_eq_mul_inv, mul_comm] },
  rw [← integral_sub ((key₄ y₀).interval_integrable _ _) ((key₄ x₀).interval_integrable _ _), 
      ← interval_integral.integral_smul, real.dist_eq, 
      ← integral_sub (key₅'.interval_integrable _ _)
        ((@continuous_uncurry_left _ _ _ _ _ _ f' x₀ hf').interval_integrable _ _)],
  conv in (_ • _)
  { dsimp, rw ← div_eq_inv_mul, rw ← (hu _).2 },
  calc abs (∫ (t : ℝ) in a..b, f' (u t) t - f' x₀ t) 
      ≤ abs (∫ (t : ℝ) in a..b, abs (f' (u t) t - f' x₀ t)) : 
        by rw ← real.norm_eq_abs; exact norm_integral_le_abs_integral_norm
  ... = abs (∫ (t : ℝ) in Ioc a b, abs (f' (u t) t - f' x₀ t)) : 
        by repeat {conv in (interval_integral _ _ _ _) { rw integral_of_le hab.le }}
  ... = (∫ (t : ℝ) in Ioc a b, abs (f' (u t) t - f' x₀ t)) : 
        by rw abs_eq_self; exact integral_nonneg (λ x, abs_nonneg _)
  ... ≤ (∫ (t : ℝ) in Ioc a b, (ε/2)/(b-a)) : 
        begin
          have meas_ab : measurable_set (Ioc a b) := measurable_set_Ioc,
          rw ← integral_indicator meas_ab,
          rw ← integral_indicator meas_ab,
          refine integral_mono _ _ (λ t, _),
          { rw integrable_indicator_iff meas_ab,
            refine ((continuous_abs.comp _).integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
            refine key₆.sub (@continuous_uncurry_left _ _ _ _ _ _ f' x₀ hf') },
          { rw integrable_indicator_iff meas_ab,
            refine (continuous.integrable_on_compact compact_Icc _).mono_set Ioc_subset_Icc_self,
            simp only [continuous_const]},
          by_cases ht : t ∈ Ioc a b,
          { have := le_of_lt (this (u t, t) (x₀, t) _ _ _),
            { simpa only [ht, indicator_of_mem] using this},
            { refine ⟨key₃ (hu t).1, Icc_subset_interval $ Ioc_subset_Icc_self ht⟩, },
            { exact ⟨⟨(sub_one_lt x₀).le, (lt_add_one x₀).le⟩, 
                Icc_subset_interval $ Ioc_subset_Icc_self ht⟩ },
            { rw [prod.dist_eq, max_lt_iff],
              refine ⟨key₂ t, (dist_self t).symm ▸ hδ⟩ } },
          { simp only [ht, indicator_of_not_mem, not_false_iff]},
        end
  ... = (b-a) * (ε/2/(b-a)) :
        by rw [set_integral_const, real.volume_Ioc,
               ennreal.to_real_of_real (show 0 ≤ b - a, by linarith),
               smul_eq_mul]
  ... = ε/2 : mul_div_cancel' (ε/2) (show b - a ≠ 0, by linarith)
  ... < ε : by linarith [hε],
  all_goals {apply_instance}
end

lemma continuous_gauss : continuous (λ x, real.exp (-x^2)) := by continuity; exact complex.continuous_exp

lemma has_deriv_at_f (x : ℝ) : has_deriv_at f (real.exp (-x^2)) x := 
integral_has_deriv_at_right (continuous_gauss.interval_integrable _ _) 
  continuous_gauss.measurable.measurable_at_filter continuous_gauss.continuous_at

lemma has_deriv_at_f_square (x : ℝ) : has_deriv_at (f^2) (2 * real.exp (-x^2) * ∫ t in 0..x, real.exp (-t^2)) x := 
begin
  convert has_deriv_at.comp x (has_deriv_at_pow 2 _) (has_deriv_at_f x) using 1,
  norm_cast,
  ring
end

lemma has_deriv_at_g (x₀ : ℝ) : has_deriv_at g (∫ t in 0..1, -2 * x₀ * real.exp (-(1+t^2)*x₀^2)) x₀ := 
begin
  have key₁ : continuous (λ (t : ℝ), 1 + t^2) := by continuity,
  have key₂ : continuous ↿(λ x t, real.exp (-(1+t^2) * x^2)) :=
    real.continuous_exp.comp ((key₁.comp continuous_snd).neg.mul 
      ((continuous_pow 2).comp continuous_fst)),
  apply has_deriv_at_parametric (zero_lt_one),
  { intros x t,
    have step₁ : has_deriv_at (λ u, -(1 + t^2) * u^2) (-(1 + t^2) * 2 * x) x,
    { convert (has_deriv_at_pow 2 x).const_mul (-(1 + t ^ 2)) using 1,
      norm_cast,
      ring },
    have step₂ : has_deriv_at (λ u, real.exp (-(1 + t^2) * u^2)) 
      (-(1 + t^2) * 2 * x * real.exp (-(1 + t^2) * x^2)) x,
    { rw mul_comm, 
      exact has_deriv_at.comp x (real.has_deriv_at_exp _) step₁ },
    conv in (_ / _) { rw div_eq_mul_inv },
    convert step₂.mul_const _ using 1,
    conv_rhs {rw mul_comm, rw ← mul_assoc, rw ← mul_assoc, rw ← mul_assoc, 
              rw mul_neg_eq_neg_mul_symm, 
              rw inv_mul_cancel (show 1 + t^2 ≠ 0, by linarith [pow_two_nonneg t]) },
    ring },
  { exact key₂.div (key₁.comp continuous_snd) (λ ⟨x, t⟩, by linarith [pow_two_nonneg t]) },
  { exact (continuous_const.mul continuous_fst).mul key₂, },
end

lemma key1 : ∀ x : ℝ, ∀ t ∈ (set.interval 0 1 : set ℝ), 
  has_deriv_at ((λ (u : ℝ), ∫ (t : ℝ) in 0..u, real.exp (-t ^ 2)) ∘ λ (u : ℝ), u * x) (real.exp (-(t * x) ^ 2) * x) t :=
begin
  intros x t ht,
  apply has_deriv_at.comp _ (has_deriv_at_f _),
  convert (has_deriv_at_id t).mul_const x, 
  ring
end

lemma has_deriv_at_h : ∀ x, has_deriv_at h 0 x :=
begin
  intros x,
  rw h,
  convert ← (has_deriv_at_g x).add (has_deriv_at_f_square x),
  rw add_eq_zero_iff_eq_neg,
  calc  ∫ (t : ℝ) in 0..1, (-2) * x * real.exp (-(1 + t ^ 2) * x ^ 2)
      = ∫ (t : ℝ) in 0..1, (-2) * x * real.exp (-(t * x) ^ 2 + -x ^ 2) :
        by conv in (-(1+_^2)*x^2) { ring, rw [← mul_pow, mul_comm, sub_eq_add_neg] }
  ... = ∫ t in 0..1, (-2) * x * (real.exp (-x ^ 2) * real.exp (-(t * x) ^ 2)) : 
        by conv in (real.exp _) { rw real.exp_add, rw mul_comm }
  ... = ∫ t in 0..1, (-2 * real.exp (-x ^ 2)) * (real.exp (-(t * x) ^ 2) * x) : 
        by congr; ext t; ring
  ... = ∫ t in 0..1, (-2 * real.exp (-x ^ 2)) • (real.exp (-(t * x) ^ 2) * x) : 
        by congr; ext t; rw smul_eq_mul
  ... = (-2 * real.exp (-x ^ 2)) • ∫ t in 0..1, (real.exp (-(t * x) ^ 2) * x) : 
        integral_smul _
  ... = (-2 * real.exp (-x ^ 2)) * ∫ t in 0..1, (real.exp (-(t * x) ^ 2) * x) : 
        by rw smul_eq_mul
  ... = (-2 * real.exp (-x ^ 2)) *
          ( ((λ u, ∫ t in 0..u, real.exp (-t ^ 2)) ∘ (λ u, u * x)) 1
          - ((λ u, ∫ t in 0..u, real.exp (-t ^ 2)) ∘ (λ u, u * x)) 0 ) : 
        begin
          congr,
          refine integral_eq_sub_of_has_deriv_at (key1 x) (continuous.continuous_on _),
          continuity,
          exact complex.continuous_exp
        end
  ... = (-2 * real.exp (-x ^ 2)) * ∫ t in 0..x, real.exp (-t ^ 2) : by simp
  ... = -(2 * real.exp (-x ^ 2) * ∫ t in 0..x, real.exp (-t ^ 2)) : by ring
end

lemma h_zero : h 0 = real.pi / 4 :=
begin
  change (∫ t in 0..1, real.exp (-(1 + t^2) * 0^2) / (1 + t^2)) + 
    (∫ (t : ℝ) in 0..0, real.exp (-t^2))^2 = real.pi / 4,
  rw [integral_same, zero_pow zero_lt_two, add_zero],
  conv_lhs {congr, funext, rw mul_zero, rw real.exp_zero},
  convert integral_eq_sub_of_has_deriv_at (λ t _, t.has_deriv_at_arctan) 
    (continuous_const.div _ _).continuous_on,
  { rw [real.arctan_one, real.arctan_zero, sub_zero] },
  { continuity },
  { intro t,
    linarith [pow_two_nonneg t] } 
end

lemma h_eq : h = (λ x, real.pi / 4) := 
funext $ λ x, h_zero ▸ (is_const_of_deriv_eq_zero (λ t, (has_deriv_at_h t).differentiable_at) 
  (λ t, (has_deriv_at_h t).deriv) x 0)

lemma g_le_key (x : ℝ) (hx : 1 ≤ x) :
  (λ t, (real.exp (-(1+t^2)*x^2))/(1+t^2)) ≤ (λ t, real.exp (-x)) :=
assume t,
have key₁ : 1 ≤ 1 + t^2,
  from (le_add_iff_nonneg_right 1).mpr (pow_two_nonneg t),
calc (real.exp (-(1+t^2)*x^2))/(1+t^2) 
      ≤ (real.exp (-(1+t^2)*x^2))/1 : div_le_div_of_le_left 
          (real.exp_pos _).le zero_lt_one key₁
  ... = real.exp (-(1+t^2)*x^2) : div_one _
  ... = real.exp ((1+t^2)*(-x^2)) : congr_arg real.exp (by ring)
  ... ≤ real.exp (1*(-x^2)) : real.exp_monotone 
          (mul_mono_nonpos (neg_nonpos.mpr $ pow_two_nonneg x) key₁)
  ... = real.exp (-x^2) : by rw one_mul
  ... = real.exp (x*(-x)) : by ring
  ... ≤ real.exp (1*(-x)) : real.exp_monotone
          (mul_mono_nonpos (neg_nonpos.mpr $ zero_le_one.trans hx) hx)
  ... = real.exp (-x) : by rw one_mul

lemma g_le : g ≤ᶠ[at_top] (λ x, real.exp (-x)) :=
begin
  dsimp [g],
  refine ((eventually_ge_at_top 1).mono $ λ x hx, _),
  convert interval_integral_mono _ _ zero_le_one (g_le_key x hx),
  { rw interval_integral.integral_const,
    simp },
  { refine (continuous.div _ _ _).interval_integrable 0 1,
    { continuity, exact complex.continuous_exp },
    { continuity },
    { intro x, linarith [pow_two_nonneg x] } },
  { exact continuous.interval_integrable (by continuity) 0 1 },
end

lemma g_tendsto : tendsto g at_top (𝓝 0) := 
begin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds 
    (real.tendsto_exp_at_bot.comp tendsto_neg_at_top_at_bot) 
    (eventually_of_forall $ λ x, _) g_le,
  dsimp [g],
  rw integral_of_le,
  { refine integral_nonneg (λ t, _),
    exact div_nonneg (real.exp_pos _).le 
      (zero_le_one.trans $ (le_add_iff_nonneg_right 1).mpr (pow_two_nonneg t)) },
  { exact zero_le_one }
end

lemma f_square_tendsto : tendsto (f^2) at_top (𝓝 $ real.pi/4) :=
begin
  have : f^2 = h - g,
  { ext, simp [h] },
  rw [this, ← sub_zero (real.pi/4), h_eq],
  exact tendsto_const_nhds.sub g_tendsto
end

lemma f_tendsto : tendsto f at_top (𝓝 $ real.pi.sqrt / 2) :=
begin
  rw [← real.sqrt_sqr zero_le_two, ← real.sqrt_div real.pi_pos.le],
  norm_num,
  refine f_square_tendsto.sqrt.congr' _,
  refine (eventually_ge_at_top 0).mono (λ x hx, real.sqrt_sqr _),
  dsimp [f],
  rw integral_of_le hx,
  refine integral_nonneg (λ t, (real.exp_pos _).le),
end

lemma tendsto_gauss_integral_symm_interval : 
  tendsto (λ x, ∫ t in (-x)..x, real.exp (-t^2)) at_top (𝓝 real.pi.sqrt) :=
begin
  convert ← tendsto.const_mul 2 f_tendsto,
  { ext x,
    rw [two_mul, ← integral_add_adjacent_intervals 
      (continuous_gauss.interval_integrable (-x) 0) 
      (continuous_gauss.interval_integrable 0 x)],
    refine congr_arg2 (+) _ rfl,
    conv in (real.exp _) {rw ← neg_square, change (λ t, real.exp (-t^2)) (-t)},
    rw [integral_comp_neg 0 x (λ t, real.exp (-t^2)) 
          continuous_gauss.measurable.ae_measurable, neg_zero],
    all_goals {apply_instance} },
  { linarith }
end

lemma tendsto_gauss_integral_symm_Ioc : 
  tendsto (λ x, ∫ t in Ioc (-x) x, real.exp (-t^2)) at_top (𝓝 real.pi.sqrt) :=
tendsto_gauss_integral_symm_interval.congr' 
  ((eventually_ge_at_top 0).mono $ λ x hx, integral_of_le (neg_le_self hx))

--lemma gauss_integral_right : ∫ x in Ioi 0, real.exp (-x^2) = real.pi.sqrt / 2 :=
--begin
--  let F := λ (n : ℕ), indicator (Iic n : set ℝ) (λ x, real.exp (-x^2)),
--  have key : ∀ᵐ (x:ℝ), filter.tendsto (λ n, F n x) at_top (𝓝 (real.exp (-x^2))),
--  { refine ae_of_all volume (λ x, tendsto_const_nhds.congr' _),
--    refine eventually_at_top.mpr ⟨nat_ceil x, (λ n hn, _)⟩,
--    refine (indicator_of_mem _ _).symm,
--    change x ≤ n,
--    calc x  ≤ nat_ceil x : le_nat_ceil x
--        ... ≤ n : by exact_mod_cast hn },
--end

lemma gauss_integral : ∫ x : ℝ, real.exp (-x^2) = real.pi.sqrt :=
begin
  refine integral_eq_of_tendsto_integral_of_nonneg_ae _ _ _ _ 
    (ae_of_all _ $ λ x, (real.exp_pos _).le) _ _ 
    (tendsto_gauss_integral_symm_Ioc.comp tendsto_coe_nat_at_top_at_top),
  { intro x,
    refine (tendsto_coe_nat_at_top_at_top.eventually (eventually_gt_at_top $ abs x)).mono 
      (λ n hn, ⟨_, _⟩);
    rw abs_lt at hn;
    linarith },
  { intros i j hij,
    refine Ioc_subset_Ioc _ _;
    [rw neg_le_neg_iff, skip];
    norm_cast;
    linarith },
  { intro n, 
    exact measurable_set_Ioc },
  { exact continuous_gauss.measurable },
  { intro n, 
    exact (continuous_gauss.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self }
end