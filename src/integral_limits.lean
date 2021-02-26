import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral

open measure_theory filter set
open_locale ennreal nnreal topological_space

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma ae_restrict_of_ae {s : set α} {p : α → Prop} :
  (∀ᵐ x ∂μ, p x) → (∀ᵐ x ∂(μ.restrict s), p x) :=
eventually.filter_mono (ae_mono measure.restrict_le_self)

lemma lintegral_eq_of_tendsto (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ≥0∞) (I : ℝ≥0∞) 
  (hfm : measurable f) (h : tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 I)) :
∫⁻ x, f x ∂μ = I :=
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
  conv at h {congr, funext, rw ← key₆}, 
  have key₇ : I = ⨆ (n : ℕ), ∫⁻ (x : α), F n x ∂μ :=
    tendsto_nhds_unique h (tendsto_at_top_csupr key₅ ⟨⊤, λ _ _, le_top⟩),
  conv_lhs {congr, skip, funext, rw key₄},
  rw key₇,
  exact lintegral_supr (λ n, hfm.indicator $ hφ₃ n) key₃
end

lemma eventually_ne_of_tendsto_nhds {β : Type*} [topological_space β] [t1_space β] {f : α → β} {b b' : β}
  (hbb' : b ≠ b') {l : filter α} (hf : tendsto f l (𝓝 b)) : ∀ᶠ x in l, f x ≠ b' :=
hf (compl_singleton_mem_nhds hbb')

lemma integrable_of_tendsto_lintegral_nnnorm (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ) (I : ℝ) (hfm : measurable f) 
  (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw lintegral_eq_of_tendsto φ hφ₁ hφ₂ hφ₃ _ _ 
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) h,
  exact ennreal.of_real_lt_top
end

lemma integrable_of_tendsto_lintegral_nnnorm' (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ) (I : ℝ≥0) (hfm : measurable f) 
  (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 I)) :
integrable f μ :=
begin
  refine integrable_of_tendsto_lintegral_nnnorm φ hφ₁ hφ₂ hφ₃ f (I : ℝ) hfm hfi _,
  convert h,
  exact ennreal.of_real_coe_nnreal
end

lemma integrable_of_tendsto_integral_norm (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ) (I : ℝ) (hfm : measurable f) 
  (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, ∥f x∥ ∂μ) at_top (𝓝 I)) :
integrable f μ :=
begin
  conv at h in (integral _ _) 
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg ℝ _ (f x))) 
    hfm.norm.ae_measurable },
  conv at h in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  have h' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ)) at_top (𝓝 $ ennreal.of_real I),
  { convert (ennreal.continuous_of_real.tendsto I).comp h,
    dsimp [function.comp],
    ext n : 1,
    rw ennreal.of_real_to_real _, 
    exact ne_top_of_lt (hfi n).2 },
  exact integrable_of_tendsto_lintegral_nnnorm φ hφ₁ hφ₂ hφ₃ f I hfm hfi h'
end

lemma integrable_of_tendsto_integral_of_nonneg_ae (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ) (I : ℝ) (hf : 0 ≤ᵐ[μ] f)
  (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) : integrable f μ :=
integrable_of_tendsto_integral_norm φ hφ₁ hφ₂ hφ₃ f I hfm hfi 
  (h.congr $ λ n, integral_congr_ae $ ae_restrict_of_ae $ hf.mono $ 
    λ x hx, (real.norm_of_nonneg hx).symm)
--begin
  --conv at h in (integral _ _) 
  --{ rw integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf) (measurable.ae_measurable hfm) },
  --have h' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ).to_real) at_top (𝓝 I),
  --{ refine h.congr (λ n, _),
  --  congr' 1,
  --  refine lintegral_congr_ae ((ae_restrict_of_ae hf).mono $ λ x hx, _),
  --  rw [ennreal.coe_nnreal_eq, coe_nnnorm, real.norm_eq_abs],
  --  congr,
  --  exact (abs_eq_self.mpr hx).symm },
  --have h'' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ)) at_top (𝓝 $ ennreal.of_real I),
  --{ convert (ennreal.continuous_of_real.tendsto I).comp h',
  --  dsimp [function.comp],
  --  ext n : 1,
  --  rw ennreal.of_real_to_real _, 
  --  exact ne_top_of_lt (hfi n).2 },
  --exact integrable_of_tendsto_lintegral_nnnorm φ hφ₁ hφ₂ hφ₃ f I hfm hfi h''
--end

lemma integral_eq_of_tendsto_integral

/-
lemma integral_eq_of_tendsto_of_nonneg_ae (φ : ℕ → set α) (hφ₁ : ∀ x, ∀ᶠ n in at_top, x ∈ φ n) 
  (hφ₂ : monotone φ) (hφ₃ : ∀ n, measurable_set $ φ n) (f : α → ℝ) (I : ℝ) (hf : 0 ≤ᵐ[μ] f)
  (hfm : measurable f) (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
∫ x, f x ∂μ = I :=
begin
  rw integral_eq_lintegral_of_nonneg_ae hf (measurable.ae_measurable hfm),
  conv at h in (integral _ _) 
  { rw integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hf) (measurable.ae_measurable hfm) },
  have h' := ennreal.tendsto_of_real h,
  have h' : tendsto (λ n, ∫⁻ x in φ n, ennreal.of_real (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I) := 
    h'.congr' ((eventually_ne_of_tendsto_nhds ennreal.of_real_ne_top h').mono $ λ n hn, 
      ennreal.of_real_to_real hn),
end
-/
