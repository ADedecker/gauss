import integral_limits

open measure_theory set filter
open_locale topological_space

lemma integral_exp_Ici {x : ℝ} : ∫ t in Ici x, t.exp = x.exp :=
begin
  let a : ℕ → ℝ := λ n, x + n,
  let b : ℕ → ℝ := λ n, x - n,
  have ha : tendsto a at_top at_top := tendsto_at_top_add_const_left _ _ 
    tendsto_coe_nat_at_top_at_top,
  have hb : tendsto b at_top at_bot := tendsto_at_bot_add_const_left _ _ 
    (tendsto_neg_at_top_at_bot.comp tendsto_coe_nat_at_top_at_top),
  refine integral_eq_of_tendsto_integral_of_nonneg_ae (growing_family_Icc _ hb _ ha) _ _ _ _ _,
  { simp },
  { simp [monotone] },
  { exact ae_of_all _ (λ t, t.exp_pos.le) },
  { exact real.continuous_exp.measurable },
  { exact λ n, (continuous.integrable_on_compact compact_Icc real.continuous_exp).mono_measure
      measure.restrict_le_self },
  {  }
end