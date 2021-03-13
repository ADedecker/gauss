import measure_theory.integration
import measure_theory.bochner_integration
import measure_theory.lebesgue_measure
import measure_theory.interval_integral

open measure_theory filter set
open_locale ennreal nnreal topological_space

section growing_family

variables {α : Type*} [measurable_space α] (μ : measure α)

structure growing_family (φ : ℕ → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ n in at_top, x ∈ φ n)
(mono : monotone φ)
(measurable : ∀ n, measurable_set $ φ n)

variables {μ}

section Icc

variables [preorder α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {a b : ℕ → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (ha₂ : tendsto a at_top at_bot) 
  (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma growing_family_Icc : growing_family μ (λ n, Icc (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x, 
    (ha₂.eventually $ eventually_le_at_bot x).mp $ 
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Icc_subset_Icc (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Icc }

end Icc

section Ixx

variables [linear_order α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {a b : ℕ → α} (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (ha₂ : tendsto a at_top at_bot) 
  (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

lemma growing_family_Ioo [no_bot_order α] [no_top_order α] : 
  growing_family μ (λ n, Ioo (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x, 
    (ha₂.eventually $ eventually_lt_at_bot x).mp $ 
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ioo_subset_Ioo (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ioo }

lemma growing_family_Ioc [no_bot_order α] : growing_family μ (λ n, Ioc (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x, 
    (ha₂.eventually $ eventually_lt_at_bot x).mp $ 
    (hb₂.eventually $ eventually_ge_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ioc_subset_Ioc (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ioc }

lemma growing_family_Ico [no_top_order α] : growing_family μ (λ n, Ico (a n) (b n)) :=
{ ae_eventually_mem := ae_of_all μ (λ x, 
    (ha₂.eventually $ eventually_le_at_bot x).mp $ 
    (hb₂.eventually $ eventually_gt_at_top x).mono $
    λ n hbn han, ⟨han, hbn⟩ ),
  mono := λ i j hij, Ico_subset_Ico (ha₁ hij) (hb₁ hij),
  measurable := λ n, measurable_set_Ico }

end Ixx

end growing_family

section integral_limits

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma lintegral_eq_supr {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let F := λ n, indicator (φ n) f, 
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
      hx.mono $ λ n hn, (indicator_of_mem hn _).symm),
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ.mono hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx 
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have lintegral_F_eq : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ,
  { intro n,
    dsimp [F],
    rw lintegral_indicator _ (hφ.measurable n) },
  rw lintegral_congr_ae f_eq_supr_F,
  conv_rhs {congr, funext, rw ← lintegral_F_eq},
  exact lintegral_supr (λ n, hfm.indicator $ hφ.measurable n) (λ i j hij x, F_mono x hij)
end

lemma tendsto_set_lintegral_of_monotone_set {φ : ℕ → set α} (hφ : monotone φ) {f : α → ℝ≥0∞} :
  tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 $ ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ) :=
tendsto_at_top_csupr 
  (λ i j hij, lintegral_mono' (measure.restrict_mono (hφ hij) (le_refl _)) (le_refl _)) 
  ⟨⊤, λ _ _, le_top⟩

lemma lintegral_eq_of_tendsto_lintegral {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ≥0∞} (I : ℝ≥0∞) 
  (hfm : measurable f) (h : tendsto (λ n, ∫⁻ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
begin
  convert lintegral_eq_supr hφ hfm,
  refine tendsto_nhds_unique h (tendsto_set_lintegral_of_monotone_set hφ.mono)
end

lemma eventually_ne_of_tendsto_nhds {β : Type*} [topological_space β] [t1_space β] {f : α → β} {b b' : β}
  (hbb' : b ≠ b') {l : filter α} (hf : tendsto f l (𝓝 b)) : ∀ᶠ x in l, f x ≠ b' :=
hf (compl_singleton_mem_nhds hbb')

variables {E : Type*} [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E] 
  [complete_space E] [measurable_space E] [borel_space E]

lemma integrable_of_tendsto_lintegral_nnnorm {φ : ℕ → set α} 
  (hφ : growing_family μ φ) {f : α → E} (I : ℝ) (hfm : measurable f) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine ⟨hfm.ae_measurable, _⟩,
  unfold has_finite_integral,
  rw lintegral_eq_of_tendsto_lintegral hφ _ 
    (measurable_ennreal_coe_iff.mpr (measurable_nnnorm.comp hfm)) h,
  exact ennreal.of_real_lt_top
end

lemma integrable_of_tendsto_lintegral_nnnorm' {φ : ℕ → set α} 
  (hφ : growing_family μ φ) {f : α → E} (I : ℝ≥0) (hfm : measurable f) 
  (h : tendsto (λ n, ∫⁻ x in φ n, nnnorm (f x) ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  refine integrable_of_tendsto_lintegral_nnnorm hφ (I : ℝ) hfm _,
  convert h,
  exact ennreal.of_real_coe_nnreal
end

lemma integrable_of_tendsto_integral_norm {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → E} (I : ℝ) (hfm : measurable f) 
  (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, ∥f x∥ ∂μ) at_top (𝓝 I)) :
  integrable f μ :=
begin
  conv at h in (integral _ _) 
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x))) 
    hfm.norm.ae_measurable },
  conv at h in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  have h' : tendsto (λ (n : ℕ), (∫⁻ (a : α) in φ n, nnnorm (f a) ∂μ)) at_top (𝓝 $ ennreal.of_real I),
  { convert ennreal.tendsto_of_real h,
    ext n : 1,
    rw ennreal.of_real_to_real _, 
    exact ne_top_of_lt (hfi n).2 },
  exact integrable_of_tendsto_lintegral_nnnorm hφ I hfm h'
end

lemma integrable_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α} 
  (hφ : growing_family μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) : integrable f μ :=
integrable_of_tendsto_integral_norm hφ I hfm hfi 
  (h.congr $ λ n, integral_congr_ae $ ae_restrict_of_ae $ hf.mono $ 
    λ x hx, (real.norm_of_nonneg hx).symm)

lemma integral_eq_supr_max_sub_supr_min {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ}
  (hfm : measurable f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = (⨆ (n : ℕ), ∫⁻ x in φ n, ennreal.of_real (max (f x) 0) ∂μ).to_real - 
    (⨆ (n : ℕ), ∫⁻ x in φ n, ennreal.of_real (- min (f x) 0) ∂μ).to_real :=
begin
  rw [integral_eq_lintegral_max_sub_lintegral_min hfi, 
      lintegral_eq_supr hφ _, lintegral_eq_supr hφ _],
  { exact ennreal.measurable_of_real.comp (measurable_neg.comp $ hfm.min measurable_zero) },
  { exact ennreal.measurable_of_real.comp (hfm.max measurable_zero) }
end

lemma integral_eq_of_tendsto_integral {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ} (I : ℝ)
  (hfm : measurable f) (hfi : integrable f μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
begin
  have hfm₁ : measurable (λ x, ennreal.of_real $ max (f x) 0) :=
    ennreal.measurable_of_real.comp (hfm.max measurable_zero), --factor out ? (cf before)
  have hfm₂ : measurable (λ x, ennreal.of_real $ -min (f x) 0) := 
    ennreal.measurable_of_real.comp (measurable_neg.comp $ hfm.min measurable_zero),
  convert integral_eq_supr_max_sub_supr_min hφ hfm hfi,
  refine tendsto_nhds_unique h _,
  conv in (integral _ _) 
  { rw integral_eq_lintegral_max_sub_lintegral_min hfi.integrable_on },
  refine tendsto.sub _ _;
  refine (ennreal.tendsto_to_real _).comp (tendsto_set_lintegral_of_monotone_set hφ.mono);
  rw ← lintegral_eq_supr hφ _;
  [convert ne_top_of_lt hfi.max_zero.2, assumption,
   convert ne_top_of_lt hfi.min_zero.neg.2, assumption];
  ext x : 1;
  [rw real.nnnorm_of_nonneg (le_max_right _ _), 
   rw [pi.neg_apply, real.nnnorm_of_nonneg (neg_nonneg.mpr $ min_le_right _ _)]];
  rw ennreal.coe_nnreal_eq;
  norm_cast
end

lemma integral_eq_of_tendsto_integral_of_nonneg_ae {φ : ℕ → set α} 
  (hφ : growing_family μ φ) {f : α → ℝ} (I : ℝ) (hf : 0 ≤ᵐ[μ] f) (hfm : measurable f) (hfi : ∀ n, integrable_on f (φ n) μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from integrable_of_tendsto_integral_of_nonneg_ae hφ I hf hfm hfi h,
integral_eq_of_tendsto_integral hφ I hfm hfi' h

end integral_limits

section interval_integral

variables {μ : measure ℝ} (a b : ℕ → ℝ) (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (ha₂ : tendsto a at_top at_bot) 
  (hb₁ : monotone b) (hb₂ : tendsto b at_top at_top)

end interval_integral