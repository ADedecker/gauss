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

lemma growing_family.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β] 
  {f : α → β} {φ : ℕ → set α} (hφ : growing_family μ φ) : 
  ∀ᵐ x ∂μ, tendsto (λ n, (φ n).indicator f x) at_top (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

lemma growing_family_restrict_of_ae_imp {s : set α} {φ : ℕ → set α} 
  (hs : measurable_set s) (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in at_top, x ∈ φ n)
  (mono : monotone φ) (measurable : ∀ n, measurable_set $ φ n) :
  growing_family (μ.restrict s) φ :=
{ ae_eventually_mem := by rwa ae_restrict_iff' hs,
  mono := mono,
  measurable := measurable }

lemma growing_family.inter_restrict {φ : ℕ → set α} (hφ : growing_family μ φ) 
  {s : set α} (hs : measurable_set s) :
  growing_family (μ.restrict s) (λ n, φ n ∩ s) :=
growing_family_restrict_of_ae_imp hs 
  (hφ.ae_eventually_mem.mono (λ x hx hxs, hx.mono $ λ n hn, ⟨hn, hxs⟩))
  (λ i j hij, inter_subset_inter_left s (hφ.mono hij))
  (λ n, (hφ.measurable n).inter hs)

end growing_family

section integral_limits

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma lintegral_eq_supr {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → ℝ≥0∞}
  (hfm : measurable f) :
  ∫⁻ x, f x ∂μ = ⨆ (n : ℕ), ∫⁻ x in φ n, f x ∂μ :=
begin
  let F := λ n, indicator (φ n) f, 
  have F_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, F n x) at_top (𝓝 $ f x) :=
    hφ.ae_tendsto_indicator,
  have F_mono : ∀ x, monotone (λ n, F n x) :=
    λ x i j hij, indicator_le_indicator_of_subset (hφ.mono hij) (λ _, zero_le _) x,
  have f_eq_supr_F : ∀ᵐ x ∂μ, f x = ⨆ (n : ℕ), F n x :=
    F_tendsto.mono (λ x hx, tendsto_nhds_unique hx 
      (tendsto_at_top_csupr (F_mono x) ⟨⊤, λ _ _, le_top⟩)),
  have lintegral_F_eq : ∀ n, ∫⁻ (x : α), F n x ∂μ = ∫⁻ x in φ n, f x ∂μ :=
    λ n, lintegral_indicator _ (hφ.measurable n),
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

lemma eventually_le_of_tendsto_of_tendsto_of_lt {β : Type*} [linear_order β] [topological_space β] 
  [order_topology β] {f g : α → β} {b b' : β} (hbb' : b < b') {l : filter α} 
  (hf : tendsto f l (𝓝 b)) (hg : tendsto g l (𝓝 b')) : 
  f ≤ᶠ[l] g :=
begin
  rcases order_separated hbb' with ⟨u, v, hu, hv, hub, hvb', huv⟩,
  have hfu : f ⁻¹' u ∈ l := hf (mem_nhds_sets hu hub),
  have hgv : g ⁻¹' v ∈ l := hg (mem_nhds_sets hv hvb'),
  exact eventually_of_mem (inter_mem_sets hfu hgv) (λ x ⟨hxu, hxv⟩, (huv _ hxu _ hxv).le),
end

lemma le_of_tendsto_of_monotone {β : Type*} [preorder α] [linear_order β] [topological_space β] 
  [order_closed_topology β] {f : ℕ → β} {b : β} (hmono : monotone f) 
  (hf : tendsto f at_top (𝓝 b)) : 
  ∀ x, f x ≤ b :=
λ x, ge_of_tendsto hf ((eventually_ge_at_top x).mono $ λ _ h, hmono h)

lemma ge_of_tendsto_of_antimono {β : Type*} [preorder α] [linear_order β] [topological_space β] 
  [order_closed_topology β] {f : ℕ → β} {b : β} (hanti : ∀ ⦃x y⦄, x ≤ y → f y ≤ f x) 
  (hf : tendsto f at_top (𝓝 b)) : 
  ∀ x, b ≤ f x :=
λ x, le_of_tendsto hf ((eventually_ge_at_top x).mono $ λ _ h, hanti h)

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

lemma integral_eq_of_tendsto_integral {φ : ℕ → set α} (hφ : growing_family μ φ) {f : α → E} (I : E)
  (hfm : measurable f) (hfi : integrable f μ) 
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) at_top (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
begin
  refine tendsto_nhds_unique _ h,
  suffices : tendsto (λ (n : ℕ), ∫ (x : α), (φ n).indicator f x ∂μ) at_top (𝓝 (∫ (x : α), f x ∂μ)),
  { convert this,
    ext n,
    rw integral_indicator (hφ.measurable n) },
  exact tendsto_integral_of_dominated_convergence (λ x, ∥f x∥) 
    (λ n, (hfm.indicator $ hφ.measurable n).ae_measurable) hfm.ae_measurable hfi.norm 
    (λ n, ae_of_all _ $ norm_indicator_le_norm_self f) hφ.ae_tendsto_indicator
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

variables {α : Type*} {E : Type*} [topological_space α] [linear_order α] [order_closed_topology α]
  [measurable_space α] [no_bot_order α] [opens_measurable_space α] [measurable_space E] 
  [normed_group E] [topological_space.second_countable_topology E] [complete_space E] 
  [normed_space ℝ E] [borel_space E] {μ : measure α} {a b : ℕ → α} 
  (ha₁ : ∀ ⦃x y⦄, x ≤ y → a y ≤ a x) (hb₁ : monotone b) {f : α → E} (I : E) (hfm : measurable f)

include ha₁ hb₁

lemma monotone_ite_le_interval :
  monotone (λ n, if a n ≤ b n then Ioc (a n) (b n) else ∅) :=
begin
  intros i j hij,
  by_cases hi : a i ≤ b i,
  { have hj : a j ≤ b j := (ha₁ hij).trans (hi.trans (hb₁ hij)),
    simp [hi, hj, Ioc_subset_Ioc (ha₁ hij) (hb₁ hij)] },
  { by_cases hj : a j ≤ b j;
    simp[hi, hj] }
end

include hfm

lemma integral_eq_of_tendsto_interval_integral
  (hfi : integrable f μ) (ha₂ : tendsto a at_top at_bot) (hb₂ : tendsto b at_top at_top) 
  (h : tendsto (λ n, ∫ x in a n .. b n, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x, f x ∂μ = I :=
begin
  let φ := λ n, if a n ≤ b n then Ioc (a n) (b n) else ∅,
  have hφ : growing_family μ φ :=
  { ae_eventually_mem := ae_of_all _ $ λ x,
      begin
        filter_upwards [ha₂.eventually (eventually_lt_at_bot x), 
                        hb₂.eventually (eventually_ge_at_top x)],
        intros n han hbn,
        dsimp only [φ],
        simp [han.le.trans hbn, han, hbn]
      end,
    mono := monotone_ite_le_interval ha₁ hb₁,
    measurable := 
      begin
        intro n,
        dsimp only [φ],
        split_ifs with h,
        { exact measurable_set_Ioc },
        { exact measurable_set.empty }
      end },
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi (h.congr' _),
  filter_upwards [ha₂.eventually (eventually_le_at_bot $ b 0)],
  intros n han, 
  have : a n ≤ b n := han.trans (hb₁ $ zero_le n),
  convert interval_integral.integral_of_le this,
  simp [φ, this]
end

lemma interval_integral_eq_of_tendsto_interval_integral [order_topology α] 
  [has_no_atoms μ] {la lb : α} (hl : la < lb)
  (hfi : interval_integrable f μ la lb) (ha₂ : tendsto a at_top (𝓝 la)) 
  (hb₂ : tendsto b at_top (𝓝 lb)) 
  (h : tendsto (λ n, ∫ x in a n .. b n, f x ∂μ) at_top (𝓝 $ I)) :
  ∫ x in la..lb, f x ∂μ = I :=
begin
  let φ := λ n, if a n ≤ b n then Ioc (a n) (b n) else ∅,
  have hφ : growing_family (μ.restrict $ Ioc la lb) φ :=
    growing_family_restrict_of_ae_imp measurable_set_Ioc
      (
        begin
          refine Ioo_ae_eq_Ioc.mono (λ x (heq : (x ∈ Ioo la lb) = (x ∈ Ioc la lb)) hx, _),
          have hx : x ∈ Ioo la lb := heq.symm ▸ hx,
          refine (eventually_le_of_tendsto_lt hx.1 ha₂).mp _,
          refine (eventually_ge_of_tendsto_gt hx.2 hb₂).mono _,
          intros n hbx hax,
          dsimp only [φ],
          split_ifs,
        end
      )
      (monotone_ite_le_interval ha₁ hb₁)
      _,
  rw interval_integral.integral_of_le hl.le,
  refine integral_eq_of_tendsto_integral hφ _ hfm hfi.1 (h.congr' _),
  filter_upwards [eventually_le_of_tendsto_of_tendsto_of_lt hl ha₂ hb₂],
  intros n han, 
  have hφ₂ : φ n = Ioc (a n) (b n),
  { dsimp only [φ],
    split_ifs,
    refl }, 
  have ha₃ := ge_of_tendsto_of_antimono ha₁ ha₂ n,
  have hb₃ := le_of_tendsto_of_monotone hb₁ hb₂ n,
  have : φ n ⊆ Ioc la lb := hφ₂.symm ▸ Ioc_subset_Ioc ha₃ hb₃,
  rw [measure.restrict_restrict, inter_eq_self_of_subset_left this, hφ₂],
  exact interval_integral.integral_of_le han,
end

end interval_integral