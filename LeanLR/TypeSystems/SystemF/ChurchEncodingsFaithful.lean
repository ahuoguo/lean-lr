import LeanLR.TypeSystems.SystemF.BinaryLogRel
import LeanLR.TypeSystems.SystemF.ChurchEncodings

/-!
# System F: the Church encoding of booleans is faithful

`systemf/church_encodings_faithful.v`. Every term of type `∀ α. α → α → α` is contextually
equivalent to its eta-expansion, so the encoding has only the two intended inhabitants.
-/

open Iris.Std

namespace SystemF.Binary

/-! ## Big-step evaluation and evaluation contexts -/

/-- Reverse (snoc) induction on evaluation contexts; `SystemF/Pure.lean` keeps its copy private. -/
private theorem ectx_rev_induction {motive : Ectx → Prop} (hnil : motive [])
    (hsnoc : ∀ (K : Ectx) (Ki : EctxItem), motive K → motive (K ++ [Ki])) : ∀ K, motive K := by
  intro K
  have h : ∀ L : Ectx, motive L.reverse := by
    intro L
    induction L with
    | nil => exact hnil
    | cons Ki L ih => simpa using hsnoc L.reverse Ki ih
  simpa using h K.reverse

/-- One frame of `big_step_bind`. -/
theorem big_step_bind_item (Ki : EctxItem) {e : Expr} {v w : Val}
    (h₁ : BigStep e v) (h₂ : BigStep (fillItem Ki v.toExpr) w) : BigStep (fillItem Ki e) w := by
  cases Ki <;> simp only [fillItem] at h₂ ⊢
  case appLCtx u =>
    cases h₂ with
    | bs_app _ _ _ _ _ _ hf ha hr =>
      obtain rfl := big_step_val hf
      exact .bs_app _ _ _ _ _ _ h₁ ha hr
  case appRCtx e₁ =>
    cases h₂ with
    | bs_app _ _ _ _ _ _ hf ha hr =>
      obtain rfl := big_step_val ha
      exact .bs_app _ _ _ _ _ _ hf h₁ hr
  case unOpCtx op =>
    cases h₂ with
    | bs_unop _ _ _ _ hb hev =>
      obtain rfl := big_step_val hb
      exact .bs_unop _ _ _ _ h₁ hev
  case binOpLCtx op u =>
    cases h₂ with
    | bs_binop _ _ _ _ _ _ hb₁ hb₂ hev =>
      obtain rfl := big_step_val hb₁
      exact .bs_binop _ _ _ _ _ _ h₁ hb₂ hev
  case binOpRCtx op e₁ =>
    cases h₂ with
    | bs_binop _ _ _ _ _ _ hb₁ hb₂ hev =>
      obtain rfl := big_step_val hb₂
      exact .bs_binop _ _ _ _ _ _ hb₁ h₁ hev
  case ifCtx e₁ e₂ =>
    cases h₂ with
    | bs_if_true _ _ _ _ hb₀ hb₁ =>
      obtain rfl := big_step_val hb₀
      exact .bs_if_true _ _ _ _ h₁ hb₁
    | bs_if_false _ _ _ _ hb₀ hb₂ =>
      obtain rfl := big_step_val hb₀
      exact .bs_if_false _ _ _ _ h₁ hb₂
  case tAppCtx =>
    cases h₂ with
    | bs_tapp _ _ _ hb₁ hb₂ =>
      obtain rfl := big_step_val hb₁
      exact .bs_tapp _ _ _ h₁ hb₂
  case packCtx =>
    cases h₂ with
    | bs_pack _ _ hb =>
      obtain rfl := big_step_val hb
      exact .bs_pack _ _ h₁
  case unpackCtx x e₂ =>
    cases h₂ with
    | bs_unpack _ _ _ _ _ hb₁ hb₂ =>
      obtain rfl := big_step_val hb₁
      exact .bs_unpack _ _ _ _ _ h₁ hb₂
  case pairLCtx u =>
    cases h₂ with
    | bs_pair _ _ _ _ hb₁ hb₂ =>
      obtain rfl := big_step_val hb₁
      exact .bs_pair _ _ _ _ h₁ hb₂
  case pairRCtx e₁ =>
    cases h₂ with
    | bs_pair _ _ _ _ hb₁ hb₂ =>
      obtain rfl := big_step_val hb₂
      exact .bs_pair _ _ _ _ hb₁ h₁
  case fstCtx =>
    cases h₂ with
    | bs_fst _ _ _ hb =>
      obtain rfl := big_step_val hb
      exact .bs_fst _ _ _ h₁
  case sndCtx =>
    cases h₂ with
    | bs_snd _ _ _ hb =>
      obtain rfl := big_step_val hb
      exact .bs_snd _ _ _ h₁
  case injLCtx =>
    cases h₂ with
    | bs_injl _ _ hb =>
      obtain rfl := big_step_val hb
      exact .bs_injl _ _ h₁
  case injRCtx =>
    cases h₂ with
    | bs_injr _ _ hb =>
      obtain rfl := big_step_val hb
      exact .bs_injr _ _ h₁
  case caseCtx e₁ e₂ =>
    cases h₂ with
    | bs_casel _ _ _ _ _ hb hr =>
      obtain rfl := big_step_val hb
      exact .bs_casel _ _ _ _ _ h₁ hr
    | bs_caser _ _ _ _ _ hb hr =>
      obtain rfl := big_step_val hb
      exact .bs_caser _ _ _ _ _ h₁ hr

/-- One frame of `big_step_bind_inv`. -/
theorem big_step_bind_inv_item (Ki : EctxItem) {e : Expr} {w : Val}
    (h : BigStep (fillItem Ki e) w) :
    ∃ v : Val, BigStep e v ∧ BigStep (fillItem Ki v.toExpr) w := by
  cases Ki <;> simp only [fillItem] at h ⊢
  case appLCtx u =>
    cases h with
    | bs_app _ _ _ _ _ _ hf ha hr =>
      exact ⟨_, hf, .bs_app _ _ _ _ _ _ (big_step_of_val rfl) ha hr⟩
  case appRCtx e₁ =>
    cases h with
    | bs_app _ _ _ _ _ _ hf ha hr =>
      exact ⟨_, ha, .bs_app _ _ _ _ _ _ hf (big_step_of_val rfl) hr⟩
  case unOpCtx op =>
    cases h with
    | bs_unop _ _ _ _ hb hev =>
      exact ⟨_, hb, .bs_unop _ _ _ _ (big_step_of_val rfl) hev⟩
  case binOpLCtx op u =>
    cases h with
    | bs_binop _ _ _ _ _ _ hb₁ hb₂ hev =>
      exact ⟨_, hb₁, .bs_binop _ _ _ _ _ _ (big_step_of_val rfl) hb₂ hev⟩
  case binOpRCtx op e₁ =>
    cases h with
    | bs_binop _ _ _ _ _ _ hb₁ hb₂ hev =>
      exact ⟨_, hb₂, .bs_binop _ _ _ _ _ _ hb₁ (big_step_of_val rfl) hev⟩
  case ifCtx e₁ e₂ =>
    cases h with
    | bs_if_true _ _ _ _ hb₀ hb₁ =>
      exact ⟨_, hb₀, .bs_if_true _ _ _ _ (big_step_of_val rfl) hb₁⟩
    | bs_if_false _ _ _ _ hb₀ hb₂ =>
      exact ⟨_, hb₀, .bs_if_false _ _ _ _ (big_step_of_val rfl) hb₂⟩
  case tAppCtx =>
    cases h with
    | bs_tapp _ _ _ hb₁ hb₂ =>
      exact ⟨_, hb₁, .bs_tapp _ _ _ (big_step_of_val rfl) hb₂⟩
  case packCtx =>
    cases h with
    | bs_pack _ _ hb =>
      exact ⟨_, hb, .bs_pack _ _ (big_step_of_val rfl)⟩
  case unpackCtx x e₂ =>
    cases h with
    | bs_unpack _ _ _ _ _ hb₁ hb₂ =>
      exact ⟨_, hb₁, .bs_unpack _ _ _ _ _ (big_step_of_val rfl) hb₂⟩
  case pairLCtx u =>
    cases h with
    | bs_pair _ _ _ _ hb₁ hb₂ =>
      exact ⟨_, hb₁, .bs_pair _ _ _ _ (big_step_of_val rfl) hb₂⟩
  case pairRCtx e₁ =>
    cases h with
    | bs_pair _ _ _ _ hb₁ hb₂ =>
      exact ⟨_, hb₂, .bs_pair _ _ _ _ hb₁ (big_step_of_val rfl)⟩
  case fstCtx =>
    cases h with
    | bs_fst _ _ _ hb =>
      exact ⟨_, hb, .bs_fst _ _ _ (big_step_of_val rfl)⟩
  case sndCtx =>
    cases h with
    | bs_snd _ _ _ hb =>
      exact ⟨_, hb, .bs_snd _ _ _ (big_step_of_val rfl)⟩
  case injLCtx =>
    cases h with
    | bs_injl _ _ hb =>
      exact ⟨_, hb, .bs_injl _ _ (big_step_of_val rfl)⟩
  case injRCtx =>
    cases h with
    | bs_injr _ _ hb =>
      exact ⟨_, hb, .bs_injr _ _ (big_step_of_val rfl)⟩
  case caseCtx e₁ e₂ =>
    cases h with
    | bs_casel _ _ _ _ _ hb hr =>
      exact ⟨_, hb, .bs_casel _ _ _ _ _ (big_step_of_val rfl) hr⟩
    | bs_caser _ _ _ _ _ hb hr =>
      exact ⟨_, hb, .bs_caser _ _ _ _ _ (big_step_of_val rfl) hr⟩

theorem big_step_bind_inv (K : Ectx) {e : Expr} {w : Val} (h : BigStep (fill K e) w) :
    ∃ v : Val, BigStep e v ∧ BigStep (fill K v.toExpr) w := by
  induction K using ectx_rev_induction generalizing w with
  | hnil => exact ⟨w, h, big_step_of_val rfl⟩
  | hsnoc K Ki ih =>
    simp only [fill_last] at h ⊢
    obtain ⟨u, hu, hw⟩ := big_step_bind_inv_item Ki h
    obtain ⟨v, hv, hvu⟩ := ih hu
    exact ⟨v, hv, big_step_bind_item Ki hvu hw⟩

theorem big_step_bind (K : Ectx) {e : Expr} {v w : Val} (h₁ : BigStep e v)
    (h₂ : BigStep (fill K v.toExpr) w) : BigStep (fill K e) w := by
  induction K using ectx_rev_induction generalizing w with
  | hnil =>
    obtain rfl := big_step_val h₂
    exact h₁
  | hsnoc K Ki ih =>
    simp only [fill_last] at h₂ ⊢
    obtain ⟨u, hu, hw⟩ := big_step_bind_inv_item Ki h₂
    exact big_step_bind_item Ki (ih hu) hw

theorem big_step_det {e : Expr} {v : Val} (h : BigStep e v) :
    ∀ {w : Val}, BigStep e w → v = w := by
  induction h with
  | bs_lit l => intro w hw; cases hw; rfl
  | bs_lam x e => intro w hw; cases hw; rfl
  | bs_tlam e => intro w hw; cases hw; rfl
  | bs_binop e₁ e₂ v₁ v₂ v' op _ _ hev ih₁ ih₂ =>
    intro w hw
    cases hw with
    | bs_binop _ _ _ _ _ _ hc₁ hc₂ hev' =>
      obtain rfl := ih₁ hc₁
      obtain rfl := ih₂ hc₂
      rw [hev] at hev'
      injection hev'
  | bs_unop e v v' op _ hev ih =>
    intro w hw
    cases hw with
    | bs_unop _ _ _ _ hc hev' =>
      obtain rfl := ih hc
      rw [hev] at hev'
      injection hev'
  | bs_app e₁ e₂ x e v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    intro w hw
    cases hw with
    | bs_app _ _ _ _ _ _ hc₁ hc₂ hc₃ =>
      have hl := ih₁ hc₁
      injection hl with hx hb
      subst hx
      subst hb
      obtain rfl := ih₂ hc₂
      exact ih₃ hc₃
  | bs_tapp e₁ e₂ v _ _ ih₁ ih₂ =>
    intro w hw
    cases hw with
    | bs_tapp _ _ _ hc₁ hc₂ =>
      have hl := ih₁ hc₁
      injection hl with hb
      subst hb
      exact ih₂ hc₂
  | bs_pack e v _ ih =>
    intro w hw
    cases hw with
    | bs_pack _ _ hc =>  rw [ih hc]
  | bs_unpack e₁ e₂ v₁ v₂ x _ _ ih₁ ih₂ =>
    intro w hw
    cases hw with
    | bs_unpack _ _ _ _ _ hc₁ hc₂ =>
      have hl := ih₁ hc₁
      injection hl with hb
      subst hb
      exact ih₂ hc₂
  | bs_if_true e₀ e₁ e₂ v _ _ ih₀ ih₁ =>
    intro w hw
    cases hw with
    | bs_if_true _ _ _ _ hc₀ hc₁ =>  exact ih₁ hc₁
    | bs_if_false _ _ _ _ hc₀ hc₂ =>  exact absurd (ih₀ hc₀) (by simp)
  | bs_if_false e₀ e₁ e₂ v _ _ ih₀ ih₂ =>
    intro w hw
    cases hw with
    | bs_if_true _ _ _ _ hc₀ hc₁ =>  exact absurd (ih₀ hc₀) (by simp)
    | bs_if_false _ _ _ _ hc₀ hc₂ =>  exact ih₂ hc₂
  | bs_pair e₁ e₂ v₁ v₂ _ _ ih₁ ih₂ =>
    intro w hw
    cases hw with
    | bs_pair _ _ _ _ hc₁ hc₂ =>  rw [ih₁ hc₁, ih₂ hc₂]
  | bs_fst e v₁ v₂ _ ih =>
    intro w hw
    cases hw with
    | bs_fst _ _ _ hc =>
      have hl := ih hc
      injection hl
  | bs_snd e v₁ v₂ _ ih =>
    intro w hw
    cases hw with
    | bs_snd _ _ _ hc =>
      have hl := ih hc
      injection hl
  | bs_injl e v _ ih =>
    intro w hw
    cases hw with
    | bs_injl _ _ hc =>  rw [ih hc]
  | bs_injr e v _ ih =>
    intro w hw
    cases hw with
    | bs_injr _ _ hc =>  rw [ih hc]
  | bs_casel e e₁ e₂ v v' _ _ ih ih' =>
    intro w hw
    cases hw with
    | bs_casel _ _ _ _ _ hc hr =>
      have hl := ih hc
      injection hl with hu
      subst hu
      exact ih' hr
    | bs_caser _ _ _ _ _ hc hr =>  exact absurd (ih hc) (by simp)
  | bs_caser e e₁ e₂ v v' _ _ ih ih' =>
    intro w hw
    cases hw with
    | bs_casel _ _ _ _ _ hc hr =>  exact absurd (ih hc) (by simp)
    | bs_caser _ _ _ _ _ hc hr =>
      have hl := ih hc
      injection hl with hu
      subst hu
      exact ih' hr

/-! ## Closure of the relation under reduction and expansion -/

theorem closure_under_reduction {e₁ e₂ : Expr} {v₁ v₂ : Val} {δ : TyVarInterp} {A : Ty}
    (hb₁ : BigStep e₁ v₁) (hb₂ : BigStep e₂ v₂) (hv : valRel δ A v₁ v₂) :
    exprRel δ A e₁ e₂ := ⟨v₁, v₂, hb₁, hb₂, hv⟩

theorem closure_under_partial_reduction (K₁ K₂ : Ectx) {e₁ e₂ : Expr} {v₁ v₂ : Val}
    {δ : TyVarInterp} {A : Ty} (hb₁ : BigStep e₁ v₁) (hb₂ : BigStep e₂ v₂)
    (h : exprRel δ A (fill K₁ v₁.toExpr) (fill K₂ v₂.toExpr)) :
    exprRel δ A (fill K₁ e₁) (fill K₂ e₂) := by
  obtain ⟨u₁, u₂, h₁, h₂, hu⟩ := h
  exact ⟨u₁, u₂, big_step_bind K₁ hb₁ h₁, big_step_bind K₂ hb₂ h₂, hu⟩

theorem closure_under_expansion (K₁ K₂ : Ectx) {e₁ e₂ : Expr} {v₁ v₂ : Val}
    {δ : TyVarInterp} {A : Ty} (hb₁ : BigStep e₁ v₁) (hb₂ : BigStep e₂ v₂)
    (h : exprRel δ A (fill K₁ e₁) (fill K₂ e₂)) :
    exprRel δ A (fill K₁ v₁.toExpr) (fill K₂ v₂.toExpr) := by
  obtain ⟨u₁, u₂, h₁, h₂, hu⟩ := h
  obtain ⟨r₁, hr₁, hs₁⟩ := big_step_bind_inv K₁ h₁
  obtain ⟨r₂, hr₂, hs₂⟩ := big_step_bind_inv K₂ h₂
  obtain rfl := big_step_det hr₁ hb₁
  obtain rfl := big_step_det hr₂ hb₂
  exact ⟨u₁, u₂, hs₁, hs₂, hu⟩

theorem tforall_expand (v₁ v₂ v₃ v₄ : Val) (δ : TyVarInterp) (A : Ty)
    (hty : ∀ τ : SemType, exprRel (τ .:₂ δ) A (.tApp v₁.toExpr) (.tApp v₂.toExpr))
    (h₁ : valRel δ (.all A) v₁ v₃) (h₂ : valRel δ (.all A) v₂ v₄) :
    valRel δ (.all A) v₁ v₂ := by
  simp only [valRel] at h₁ h₂ ⊢
  obtain ⟨e₁, e₂, rfl, _, hc₁, _, _⟩ := h₁
  obtain ⟨e₃, e₄, rfl, _, hc₃, _, _⟩ := h₂
  refine ⟨e₁, e₃, rfl, rfl, hc₁, hc₃, fun τ => ?_⟩
  obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hty τ
  cases hb₁ with
  | bs_tapp _ _ _ hx hy =>
    have hl := big_step_val hx
    injection hl with hl
    subst hl
    cases hb₂ with
    | bs_tapp _ _ _ hx' hy' =>
      have hl' := big_step_val hx'
      injection hl' with hl'
      subst hl'
      exact ⟨u₁, u₂, hy, hy', hu⟩

theorem tforall_reduce (v₁ v₂ : Val) (δ : TyVarInterp) (A : Ty) (τ : SemType)
    (h : valRel δ (.all A) v₁ v₂) :
    exprRel (τ .:₂ δ) A (.tApp v₁.toExpr) (.tApp v₂.toExpr) := by
  simp only [valRel] at h
  obtain ⟨e₁, e₂, rfl, rfl, _, _, hty⟩ := h
  obtain ⟨u₁, u₂, hb₁, hb₂, hu⟩ := hty τ
  exact ⟨u₁, u₂, .bs_tapp _ _ _ (big_step_of_val rfl) hb₁,
    .bs_tapp _ _ _ (big_step_of_val rfl) hb₂, hu⟩

theorem fun_reduce {e₁ e₂ : Expr} {δ : TyVarInterp} {A B : Ty}
    (h : exprRel δ (.fn A B) e₁ e₂) (v w : Val) (hvw : valRel δ A v w) :
    exprRel δ B (.app e₁ v.toExpr) (.app e₂ w.toExpr) := by
  obtain ⟨f₁, f₂, hb₁, hb₂, hf⟩ := h
  simp only [valRel] at hf
  obtain ⟨x, y, g₁, g₂, rfl, rfl, _, _, hbody⟩ := hf
  obtain ⟨u₁, u₂, hu₁, hu₂, hu⟩ := hbody v w hvw
  exact ⟨u₁, u₂, .bs_app _ _ x g₁ v u₁ hb₁ (big_step_of_val rfl) hu₁,
    .bs_app _ _ y g₂ w u₂ hb₂ (big_step_of_val rfl) hu₂, hu⟩

theorem fun_expand {e₁ e₂ e₃ e₄ : Expr} {δ : TyVarInterp} {A B : Ty}
    (hty : ∀ v w : Val, valRel δ A v w → exprRel δ B (.app e₁ v.toExpr) (.app e₂ w.toExpr))
    (h₁ : exprRel δ (.fn A B) e₁ e₃) (h₂ : exprRel δ (.fn A B) e₄ e₂) :
    exprRel δ (.fn A B) e₁ e₂ := by
  obtain ⟨v₁, v₃, hb₁, hb₃, h₁₃⟩ := h₁
  obtain ⟨v₄, v₂, hb₄, hb₂, h₄₂⟩ := h₂
  simp only [valRel] at h₁₃ h₄₂
  obtain ⟨x₁, x₃, g₁, g₃, rfl, rfl, hc₁, hc₃, _⟩ := h₁₃
  obtain ⟨x₄, x₂, g₄, g₂, rfl, rfl, hc₄, hc₂, _⟩ := h₄₂
  refine ⟨.lamV x₁ g₁, .lamV x₂ g₂, hb₁, hb₂, ?_⟩
  simp only [valRel]
  refine ⟨x₁, x₂, g₁, g₂, rfl, rfl, hc₁, hc₂, fun v' w' hvw => ?_⟩
  obtain ⟨u₁, u₂, hu₁, hu₂, hu⟩ := hty v' w' hvw
  refine ⟨u₁, u₂, ?_, ?_, hu⟩
  · obtain ⟨r, hr, hs⟩ := big_step_bind_inv [.appLCtx v'] hu₁
    obtain rfl := big_step_det hr hb₁
    cases hs with
    | bs_app _ _ _ _ _ _ ha hb hc =>
      have hl := big_step_val ha
      injection hl with hx hg
      subst hx
      subst hg
      obtain rfl := big_step_val hb
      exact hc
  · obtain ⟨r, hr, hs⟩ := big_step_bind_inv [.appLCtx w'] hu₂
    obtain rfl := big_step_det hr hb₂
    cases hs with
    | bs_app _ _ _ _ _ _ ha hb hc =>
      have hl := big_step_val ha
      injection hl with hx hg
      subst hx
      subst hg
      obtain rfl := big_step_val hb
      exact hc

theorem bind (K₁ K₂ : Ectx) {e₁ e₂ : Expr} {δ δ' : TyVarInterp} {A B : Ty}
    (h : exprRel δ A e₁ e₂)
    (hcont : ∀ v w : Val, valRel δ A v w → exprRel δ' B (fill K₁ v.toExpr) (fill K₂ w.toExpr)) :
    exprRel δ' B (fill K₁ e₁) (fill K₂ e₂) := by
  obtain ⟨v, w, hb₁, hb₂, hv⟩ := h
  obtain ⟨u₁, u₂, h₁, h₂, hu⟩ := hcont v w hv
  exact ⟨u₁, u₂, big_step_bind K₁ hb₁ h₁, big_step_bind K₂ hb₂ h₂, hu⟩

/-! ## Faithfulness of the Church booleans -/

theorem bool_true_closed (X : List String) : closed X bool_true.toExpr := by
  simp [closed, bool_true, Val.toExpr, Expr.isClosed, Binder.cons]

theorem bool_false_closed (X : List String) : closed X bool_false.toExpr := by
  simp [closed, bool_false, Val.toExpr, Expr.isClosed, Binder.cons]

theorem bool_type_wf (n : Nat) : TypeWf n bool_type :=
  .all_wf (.fn_wf (.tVar_wf (by omega)) (.fn_wf (.tVar_wf (by omega)) (.tVar_wf (by omega))))

/-- `bool_true` applied (as a Church boolean) to two values returns the first. -/
theorem bool_true_app (a b : Val) (ha : closed [] a.toExpr) :
    BigStep (.app (.app (.tApp bool_true.toExpr) a.toExpr) b.toExpr) a := by
  refine .bs_app _ _ (.bNamed "f") a.toExpr b a ?_ (big_step_of_val rfl) ?_
  · refine .bs_app _ _ (.bNamed "t") (.lam (.bNamed "f") (.var "t")) a
      (.lamV (.bNamed "f") a.toExpr) ?_ (big_step_of_val rfl) ?_
    · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
    · simp +decide only [subst', subst]
      exact .bs_lam _ _
  · simp only [subst', subst_closed_nil ha]
    exact big_step_of_val rfl

/-- `bool_false` applied (as a Church boolean) to two values returns the second. -/
theorem bool_false_app (a b : Val) :
    BigStep (.app (.app (.tApp bool_false.toExpr) a.toExpr) b.toExpr) b := by
  refine .bs_app _ _ (.bNamed "f") (.var "f") b b ?_ (big_step_of_val rfl) ?_
  · refine .bs_app _ _ (.bNamed "t") (.lam (.bNamed "f") (.var "f")) a
      (.lamV (.bNamed "f") (.var "f")) ?_ (big_step_of_val rfl) ?_
    · exact .bs_tapp _ _ _ (big_step_of_val rfl) (.bs_lam _ _)
    · simp +decide only [subst', subst]
      exact .bs_lam _ _
  · simp +decide only [subst', subst]
    exact big_step_of_val rfl

def eta_bool (e : Expr) : Expr :=
  .app (.app (.tApp e) bool_true.toExpr) bool_false.toExpr

/-- The semantic type used to pin `bool_type` down to two inhabitants. -/
private def twoPoint (v w : Val) (hv : closed [] v.toExpr) (hw : closed [] w.toExpr) : SemType :=
  ⟨fun u₁ u₂ => (u₁ = u₂ ∧ u₂ = v) ∨ (u₁ = u₂ ∧ u₂ = w), by
    rintro u₁ u₂ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hv, hv⟩
    · exact ⟨hw, hw⟩⟩

/-- A semantic Church boolean, applied to two closed values, returns one
of them, and its partner returns the same one. -/
theorem bool_type_full (v w f g : Val) (δ : TyVarInterp) (hv : closed [] v.toExpr)
    (hw : closed [] w.toExpr) (h : valRel δ bool_type f g) :
    ∃ b : Val, (b = v ∨ b = w) ∧
      BigStep (.app (.app (.tApp f.toExpr) v.toExpr) w.toExpr) b ∧
      BigStep (.app (.app (.tApp g.toExpr) v.toExpr) w.toExpr) b := by
  simp only [bool_type, valRel] at h
  obtain ⟨e₁, e₂, rfl, rfl, _, _, hty⟩ := h
  obtain ⟨u₃, u₄, hb₁, hb₂, hu34⟩ := hty (twoPoint v w hv hw)
  obtain ⟨x₁, x₁', e₃, e₃', rfl, rfl, _, _, hty2⟩ := hu34
  obtain ⟨u₅, u₆, hb₃, hb₄, hu56⟩ := hty2 v v (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨x₂, x₂', e₄, e₄', rfl, rfl, _, _, hty3⟩ := hu56
  obtain ⟨u₇, u₈, hb₅, hb₆, hu78⟩ := hty3 w w (Or.inr ⟨rfl, rfl⟩)
  have step₁ : BigStep (.app (.app (.tApp (Val.tLamV e₁).toExpr) v.toExpr) w.toExpr) u₇ :=
    .bs_app _ _ x₂ e₄ w u₇
      (.bs_app _ _ x₁ e₃ v (.lamV x₂ e₄)
        (.bs_tapp _ e₁ _ (big_step_of_val rfl) hb₁) (big_step_of_val rfl) hb₃)
      (big_step_of_val rfl) hb₅
  have step₂ : BigStep (.app (.app (.tApp (Val.tLamV e₂).toExpr) v.toExpr) w.toExpr) u₈ :=
    .bs_app _ _ x₂' e₄' w u₈
      (.bs_app _ _ x₁' e₃' v (.lamV x₂' e₄')
        (.bs_tapp _ e₂ _ (big_step_of_val rfl) hb₂) (big_step_of_val rfl) hb₄)
      (big_step_of_val rfl) hb₆
  rcases hu78 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, Or.inl rfl, step₁, step₂⟩
  · exact ⟨_, Or.inr rfl, step₁, step₂⟩

theorem bool_true_sem_bool (δ : TyVarInterp) : valRel δ bool_type bool_true bool_true := by
  obtain ⟨_, _, hty⟩ :=
    sem_soundness (bool_true_typed 0 (PartialMap.empty (M := TyMapStr) (V := Ty)))
  have h := hty (PartialMap.empty (M := MapStr) (V := Expr))
    (PartialMap.empty (M := MapStr) (V := Expr)) δ .empty
  simp only [substMap_empty] at h
  exact sem_expr_rel_of_val bool_type δ bool_true bool_true h

theorem bool_false_sem_bool (δ : TyVarInterp) : valRel δ bool_type bool_false bool_false := by
  obtain ⟨_, _, hty⟩ :=
    sem_soundness (bool_false_typed 0 (PartialMap.empty (M := TyMapStr) (V := Ty)))
  have h := hty (PartialMap.empty (M := MapStr) (V := Expr))
    (PartialMap.empty (M := MapStr) (V := Expr)) δ .empty
  simp only [substMap_empty] at h
  exact sem_expr_rel_of_val bool_type δ bool_false bool_false h

/-- `eta_bool` preserves the typing. -/
theorem eta_bool_typed (n : Nat) (Γ : TypingContext) (e : Expr)
    (he : SynTyped n Γ e bool_type) : SynTyped n Γ (eta_bool e) bool_type :=
  .typed_app n Γ _ _ bool_type bool_type
    (.typed_app n Γ _ _ bool_type (.fn bool_type bool_type)
      (.typed_tApp n Γ e _ bool_type (bool_type_wf n) he) (bool_true_typed n Γ))
    (bool_false_typed n Γ)

/-- The semantic type that separates the two branch values inside `bool_faithful`. -/
private def branchSemType (a₁ b₁ : Val) (ha : closed [] a₁.toExpr) (hb : closed [] b₁.toExpr) :
    SemType :=
  ⟨fun u₁ u₂ => (u₁ = a₁ ∧ u₂ = bool_true) ∨ (u₁ = b₁ ∧ u₂ = bool_false), by
    rintro u₁ u₂ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨ha, bool_true_closed []⟩
    · exact ⟨hb, bool_false_closed []⟩⟩

/-- Every term of the Church boolean type is contextually equivalent to
its eta-expansion. -/
theorem bool_faithful (Δ : Nat) (Γ : TypingContext) (e : Expr)
    (hty : SynTyped Δ Γ e bool_type) : ctx_equiv Δ Γ e (eta_bool e) bool_type := by
  refine soundness_wrt_ctx_equiv hty (eta_bool_typed Δ Γ e hty) ?_
  obtain ⟨hcl, _, hsem⟩ := sem_soundness hty
  refine ⟨hcl, ?_, fun θ₁ θ₂ δ hctx => ?_⟩
  · simp only [eta_bool, closed, Expr.isClosed, Bool.and_eq_true]
    exact ⟨⟨hcl, bool_true_closed _⟩, bool_false_closed _⟩
  · have hsubst : substMap θ₂ (eta_bool e) = eta_bool (substMap θ₂ e) := by
      simp only [eta_bool, substMap]
      rw [substMap_is_closed (X := []) (bool_true_closed []) (by simp),
        substMap_is_closed (X := []) (bool_false_closed []) (by simp)]
    rw [hsubst]
    obtain ⟨v₁, v₂, hb₁, hb₂, hv⟩ := hsem θ₁ θ₂ δ hctx
    refine closure_under_partial_reduction []
      [.tAppCtx, .appLCtx bool_true, .appLCtx bool_false] hb₁ hb₂ ?_
    obtain ⟨b, hopt, _, hv2b⟩ :=
      bool_type_full bool_true bool_false v₁ v₂ δ (bool_true_closed []) (bool_false_closed []) hv
    refine closure_under_reduction (big_step_of_val (rfl : v₁.toExpr = v₁.toExpr)) hv2b ?_
    have hbb : valRel δ bool_type b b := by
      rcases hopt with rfl | rfl
      · exact bool_true_sem_bool δ
      · exact bool_false_sem_bool δ
    refine tforall_expand v₁ b v₂ b δ _ ?_ hv hbb
    intro R
    refine fun_expand ?_ (tforall_reduce v₁ v₂ δ _ R hv) (tforall_reduce b b δ _ R hbb)
    intro a₁ a₂ ha
    refine fun_expand ?_ (fun_reduce (tforall_reduce v₁ v₂ δ _ R hv) a₁ a₂ ha)
      (fun_reduce (tforall_reduce b b δ _ R hbb) a₁ a₂ ha)
    intro b₁ b₂ hbeta
    have hacl := R.closed_val a₁ a₂ (by simpa only [valRel, cons_zero] using ha)
    have hbcl := R.closed_val b₁ b₂ (by simpa only [valRel, cons_zero] using hbeta)
    refine closure_under_expansion [.tAppCtx, .appLCtx a₁, .appLCtx b₁]
      [.tAppCtx, .appLCtx a₂, .appLCtx b₂]
      (big_step_of_val (rfl : v₁.toExpr = v₁.toExpr)) hv2b ?_
    refine bind [] [.tAppCtx, .appLCtx a₂, .appLCtx b₂]
      (A := .tVar 0) (δ := (branchSemType a₁ b₁ hacl.1 hbcl.1) .:₂ δ)
      (fun_reduce (fun_reduce (tforall_reduce v₁ v₂ δ _ (branchSemType a₁ b₁ hacl.1 hbcl.1) hv)
          a₁ bool_true (by simp [valRel, branchSemType]))
        b₁ bool_false
        (by simp [valRel, branchSemType]))
      (fun u u' hu => ?_)
    simp only [valRel, cons_zero, branchSemType] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, a₂, big_step_of_val rfl, bool_true_app a₂ b₂ hacl.2, ha⟩
    · exact ⟨_, b₂, big_step_of_val rfl, bool_false_app a₂ b₂, hbeta⟩

end SystemF.Binary
