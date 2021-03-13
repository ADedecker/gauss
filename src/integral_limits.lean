import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral

open measure_theory filter set
open_locale ennreal nnreal topological_space

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma lintegral_eq_supr {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let F := λ (n : ℕ), indicator (φ n) f, 
  have key₁ : ∀ x, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    λ x, tendsto_const_nhds.congr' ((hφ₁ x).mono $ 
      λ n hn, (indicator_of_mem hn _).symm),
  have key₂ : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ₂ hij) (λ _, zero_le _) x,
  have key₃ : monotone F := λ i j hij x, key₂ x hij,
  have key₄ : ∀ x, f x = ⨆ (n : ℕ), F n x :=
    λ x, tendsto_nhds_unique (key₁ x) (tendsto_at_top_csupr (key₂ x) ⟨⊤, λ _ _, le_top⟩),
  have key₅ : monotone (λ (n : ℕ), ∫⁻ (x : α), F n x ∂μ),
  { intros i j hij,
    dsimp [F], 
    exact lintegral_mono (λ x, key₂ x hij) },
  have key₆ : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ,
  { intro n,
    dsimp [F],
    rw lintegral_indicator _ (hφ₃ n) },
  conv_lhs {congr, skip, funext, rw key₄},
  conv_rhs {congr, funext, rw ← key₆},
  exact lintegral_supr (λ n, hfm.indicator $ hφ₃ n) key₃
end

lemma tendsto_set_lintegral_of_monotone_set {φ : ℕ → set α} (hφ : monotone φ) {f : α → ℝ≥0∞} :
  tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 $ ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ) :=
tendsto_at_top_csupr 
  (λ i j hij, lintegral_mono' (measure.restrict_mono (hφ hij) (le_refl _)) (le_refl _)) 
  ⟨⊤, λ _ _, le_top⟩

lemma lintegral_eq_of_tendsto_lintegral {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ≥0∞} (I : ℝ≥0∞) 
  (hfm : measurable f) (h : tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
begin
  convert lintegral_eq_supr hφ₁ hφ₂ hφ₃ hfm,
  refine tendsto_nhds_unique h (tendsto_set_lintegral_of_monotone_set hφ₂)
end

lemma eventually_ne_of_tendsto_nhds {β : Type*} [topological_space β] [t1_space β] {f : α → β} {b b' : β}
  (hbb' : b ≠ b') {l : filter α} (hf : tendsto f l (𝓝 b)) : ∀ᶠ x in l, f x ≠ b' :=
hf (compl_singleton_mem_nhds hbb')

lemma integrable_of_tendsto_lintegral_nnnorm {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ) (hfm : measurable f) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw lintegral_eq_of_tendsto_lintegral hφ₁ hφ₂ hφ₃ _ 
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) h,
  exact ennreal.of_real_lt_top
end

lemma integrable_of_tendsto_lintegral_nnnorm' {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ≥0) (hfm : measurable f) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  refine integrable_of_tendsto_lintegral_nnnorm hφ₁ hφ₂ hφ₃ (I : ℝ) hfm _,
  convert h,
  exact ennreal.of_real_coe_nnreal
end

lemma integrable_of_tendsto_integral_norm {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ) (hfm : measurable f) 
  (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, ∥f x∥ ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  conv at h in (integral _ _) 
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg ℝ _ (f x))) 
    hfm.norm.ae_measurable },
  conv at h in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  have h' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ)) at_top (𝓝 $ ennreal.of_real I),
  { convert ennreal.tendsto_of_real h,
    ext n : 1,
    rw ennreal.of_real_to_real _, 
    exact ne_top_of_lt (hfi n).2 },
  exact integrable_of_tendsto_lintegral_nnnorm hφ₁ hφ₂ hφ₃ I hfm h'
end

lemma integrable_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f)
  (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) : integrable f μ :=
integrable_of_tendsto_integral_norm hφ₁ hφ₂ hφ₃ I hfm hfi 
  (h.congr $ λ n, integral_congr_ae $ ae_restrict_of_ae $ hf.mono $ 
    λ x hx, (real.norm_of_nonneg hx).symm)

lemma integral_eq_supr_max_sub_supr_min {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ}
  (hfm : measurable f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = (⨆ (n : ℕ), ∫⁻ x in φ n, ennreal.of_real (max (f x) 0) ∂μ).to_real - 
    (⨆ (n : ℕ), ∫⁻ x in φ n, ennreal.of_real (- min (f x) 0) ∂μ).to_real :=
begin
  rw [integral_eq_lintegral_max_sub_lintegral_min hfi, 
      lintegral_eq_supr hφ₁ hφ₂ hφ₃ _, lintegral_eq_supr hφ₁ hφ₂ hφ₃ _],
  { exact ennreal.measurable_of_real.comp (measurable_neg.comp $ hfm.min measurable_zero) },
  { exact ennreal.measurable_of_real.comp (hfm.max measurable_zero) }
end

lemma integral_eq_of_tendsto_integral {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ)
  (hfm : measurable f) (hfi : integrable f μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
begin
  have hfm₁ : measurable (λ x, ennreal.of_real $ max (f x) 0) :=
    ennreal.measurable_of_real.comp (hfm.max measurable_zero), --factor out ? (cf before)
  have hfm₂ : measurable (λ x, ennreal.of_real $ -min (f x) 0) := 
    ennreal.measurable_of_real.comp (measurable_neg.comp $ hfm.min measurable_zero),
  convert integral_eq_supr_max_sub_supr_min hφ₁ hφ₂ hφ₃ hfm hfi,
  refine tendsto_nhds_unique h _,
  conv in (integral _ _) 
  { rw integral_eq_lintegral_max_sub_lintegral_min hfi.integrable_on },
  refine tendsto.sub _ _;
  refine (ennreal.tendsto_to_real _).comp (tendsto_set_lintegral_of_monotone_set hφ₂);
  rw ← lintegral_eq_supr hφ₁ hφ₂ hφ₃ _;
  [convert ne_top_of_lt hfi.max_zero.2, assumption,
   convert ne_top_of_lt hfi.min_zero.neg.2, assumption];
  ext x : 1;
  [rw real.nnnorm_of_nonneg (le_max_right _ _), 
   rw [pi.neg_apply, real.nnnorm_of_nonneg (neg_nonneg.mpr $ min_le_right _ _)]];
  rw ennreal.coe_nnreal_eq;
  norm_cast
end

lemma integral_eq_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α} (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) {f : α → ℝ} (I : ℝ)
  (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from integrable_of_tendsto_integral_of_nonneg_ae hφ₁ hφ₂ hφ₃ I hf hfm hfi h,
integral_eq_of_tendsto_integral hφ₁ hφ₂ hφ₃ I hfm hfi' h
