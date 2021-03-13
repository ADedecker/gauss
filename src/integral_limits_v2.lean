import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral

open measure_theory filter set
open_locale ennreal nnreal topological_space

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma lintegral_eq_supr {φ : ℕ → set α} (hφ₁ : ∀ᵐ x ∂μ, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let F := λ n, indicator (φ n) f, 
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    hφ₁.mono (λ x hx, tendsto_const_nhds.congr' $
      hx.mono $ λ n hn, (indicator_of_mem hn _).symm),
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ₂ hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx 
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have lintegral_F_eq : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ,
  { intro n,
    dsimp [F],
    rw lintegral_indicator _ (hφ₃ n) },
  rw lintegral_congr_ae f_eq_supr_F,
  conv_rhs {congr, funext, rw ← lintegral_F_eq},
  exact lintegral_supr (λ n, hfm.indicator $ hφ₃ n) (λ i j hij x, F_mono x hij)
end

/-
lemma lintegral_eq_supr_fail {φ : ℕ → set α} (hφ₁ : ∀ᵐ x ∂μ, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : ∀ n, measurable_set $ φ n) {f : α → ℝ≥0∞} (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let ψ := λ n, ⋃₀ (φ '' (Icc 0 n)),
  let F := λ n, indicator (ψ n) f,
  have ψ_mono : monotone ψ := λ i j hij, sUnion_mono (image_subset φ $ Icc_subset_Icc_right hij),
  have ψ_meas : ∀ n, measurable_set (ψ n) := λ n, measurable_set.sUnion 
    ((countable_range φ).mono $ image_subset_range φ _)
    (λ t ⟨n, _, hn⟩, hn ▸ (hφ₂ n)),
  have eventually_mem_ψ : ∀ᵐ x ∂μ, ∀ᶠ n in at_top, x ∈ ψ n :=
    hφ₁.mono (λ x hx, hx.mono $ λ n hn, 
      mem_sUnion_of_mem hn ⟨n, right_mem_Icc.mpr (zero_le n), rfl⟩),
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    eventually_mem_ψ.mono (λ x hx, tendsto_const_nhds.congr' $
      hx.mono $ λ n hn, (indicator_of_mem hn _).symm),
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (ψ_mono hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx 
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have key₄ : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in ψ n, f x ∂μ,
  { intro n,
    dsimp [F],
    rw lintegral_indicator _ (ψ_meas n) },
  rw lintegral_congr_ae f_eq_supr_F,
  conv_rhs {congr, funext, rw ← key₄},
  exact lintegral_supr (λ n, hfm.indicator $ hφ₃ n) (λ i j hij x, key₂ x hij)
end
-/