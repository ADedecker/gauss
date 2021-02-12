import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral
import analysis.special_functions.exp_log
import analysis.special_functions.trigonometric
import topology.uniform_space.compact_separated

noncomputable theory

open interval_integral
open set

def f : ℝ → ℝ := λ x, ∫ t in 0..x, real.exp (-t^2)

def g : ℝ → ℝ := λ x, ∫ t in 0..1, (real.exp (-(1+t^2)*x^2))/(1+t^2)

def h : ℝ → ℝ := λ x, g x + (f^2) x

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
  rw [← integral_sub, ← integral_smul],
  have key₁ := λ (t : ℝ), exists_has_deriv_at_eq_slope_interval (λ x, f x t) (λ x, f' x t) hy₃.symm 
    (@continuous_uncurry_right _ _ _ _ _ _ f t hf).continuous_on (λ x hx, hff' x t),
  choose u hu using key₁,
  conv in (_ • _)
  { rw smul_eq_mul, rw ← div_eq_inv_mul, rw ← (hu _).2 },
  rw real.dist_eq,
  calc abs ((∫ (t : ℝ) in a..b, f' (u t) t) - ∫ (t : ℝ) in a..b, f' x₀ t) 
      ≤ abs (∫ (t : ℝ) in a..b, abs (f' (u t) t - f' x₀ t)) : 
        begin
          rw ← real.norm_eq_abs,
          rw ← integral_sub,
          refine norm_integral_le_abs_integral_norm,
          sorry,
          sorry
        end
  ... = abs (∫ (t : ℝ) in Ioc a b, abs (f' (u t) t - f' x₀ t)) : 
        by repeat {conv in (interval_integral _ _ _ _) { rw integral_of_le hab.le }}
  ... = (∫ (t : ℝ) in Ioc a b, abs (f' (u t) t - f' x₀ t)) : 
        begin
          rw abs_eq_self,
          refine measure_theory.integral_nonneg (λ x, abs_nonneg _),
        end
  ... ≤ (∫ (t : ℝ) in Ioc a b, (ε/2)/(b-a)) : 
        begin
          have meas_ab : measurable_set (Ioc a b) := measurable_set_Ioc,
          rw ← measure_theory.integral_indicator meas_ab,
          rw ← measure_theory.integral_indicator meas_ab,
          refine measure_theory.integral_mono _ _ (λ t, _),
          { rw measure_theory.integrable_indicator_iff meas_ab,
            refine measure_theory.integrable_on.mono_set _ Ioc_subset_Icc_self,
            refine continuous.integrable_on_compact compact_Icc _,
            refine continuous_abs.comp _,
            sorry },
          { rw measure_theory.integrable_indicator_iff meas_ab,
            refine measure_theory.integrable_on.mono_set _ Ioc_subset_Icc_self,
            refine continuous.integrable_on_compact compact_Icc _,
            simp [continuous_const] },
          by_cases ht : t ∈ Ioc a b,
          { have := le_of_lt (this (u t, t) (x₀, t) sorry sorry sorry),
            simpa [ht] using this },
          { simp [ht] },
        end
  ... = (b-a) * (ε/2/(b-a)) :
        by rw [measure_theory.set_integral_const, real.volume_Ioc,
               ennreal.to_real_of_real (show 0 ≤ b - a, by linarith),
               smul_eq_mul]
  ... = ε/2 : mul_div_cancel' (ε/2) (show b - a ≠ 0, by linarith)
  ... < ε : by linarith,
  sorry,
  sorry,
end

lemma has_deriv_at_f (x : ℝ) : has_deriv_at f (real.exp (-x^2)) x := 
have key : continuous (λ x, real.exp (-x^2)), by continuity; exact complex.continuous_exp,
integral_has_deriv_at_right (key.interval_integrable _ _) 
  key.measurable.measurable_at_filter key.continuous_at

lemma has_deriv_at_f_sq (x : ℝ) : has_deriv_at (f^2) (2 * real.exp (-x^2) * ∫ t in 0..x, real.exp (-t^2)) x := 
begin
  convert has_deriv_at.comp x (has_deriv_at_pow 2 _) (has_deriv_at_f x) using 1,
  norm_cast,
  ring
end

lemma has_deriv_at_g (x : ℝ) : has_deriv_at g (∫ t in 0..1, -2 * x * real.exp (-(1+t^2)*x^2)) x := 
begin
  sorry
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
  convert ← (has_deriv_at_g x).add (has_deriv_at_f_sq x),
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

lemma gauss_integral : ∫ x : ℝ, real.exp (-x^2) = real.pi.sqrt :=
begin
  sorry
end
