import integral_limits

open measure_theory set filter interval_integral
open_locale topological_space

lemma real.integral_exp_Iic (x : ℝ) : ∫ t in Iic x, t.exp = x.exp :=
begin
  have key : tendsto (λ (n : ℕ), ∫ (t : ℝ) in -n..x, t.exp) at_top (𝓝 x.exp),
  { have : ∀ (n:ℕ), x.exp - real.exp (-n) = ∫ t:ℝ in -n..x, t.exp,
    { intro n,
      rw integral_eq_sub_of_has_deriv_at 
        (λ t ht, real.has_deriv_at_exp t) 
        real.continuous_exp.continuous_on },
    refine tendsto.congr this _,
    convert tendsto_const_nhds.sub 
      (real.tendsto_exp_neg_at_top_nhds_0.comp tendsto_coe_nat_at_top_at_top),
    rw sub_zero _ },
  have antimono_neg_coe : ∀ i j : ℕ, i ≤ j → (-j : ℝ) ≤ -i := λ i j hij, by simpa,
  have tendsto_neg_coe : tendsto (λ n : ℕ, -(n : ℝ)) at_top at_bot :=
    tendsto_neg_at_top_at_bot.comp tendsto_coe_nat_at_top_at_top,
  have hfi : integrable_on real.exp (Iic x) :=
    integrable_on_Iic_of_tendsto_interval_integral_norm antimono_neg_coe real.measurable_exp
      _ _ (λ n, (real.continuous_exp.interval_integrable _ _).1) tendsto_neg_coe 
      (key.congr $ λ n, integral_congr (λ t _, (real.norm_of_nonneg t.exp_pos.le).symm)),
  exact integral_Iic_eq_of_tendsto_interval_integral antimono_neg_coe
    real.measurable_exp _ _ hfi tendsto_neg_coe key,
end

example : ∫ (t : ℝ) in Iic 0, t.exp = 1 := real.exp_zero ▸ real.integral_exp_Iic 0