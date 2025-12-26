
import LeanLr.Lang
import LeanLr.Operational



namespace STLC

-- TODO: maybe switch to ExtTreeMap?
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/stdpp/near/563551375
-- Finite map substitution (like gmap in Coq)
abbrev Subst := List (String × Expr)

def Subst.empty : Subst := []

def Subst.delete (x : String) (σ : Subst) : Subst :=
  σ.filter (fun p => p.1 ≠ x)

def Subst.insert (x : String) (e : Expr) (σ : Subst) : Subst :=
  (x, e) :: σ.delete x

def Subst.lookup (σ : Subst) (x : String) : Option Expr :=
  List.lookup x σ

def Subst.dom (σ : Subst) : List String :=
  σ.map (·.1)

-- Apply finite map substitution to expression
def substMap (σ : Subst) : Expr → Expr
  | Expr.var x => match List.lookup x σ with
    | some e => e
    | none => Expr.var x
  | Expr.lam (Binder.named x) e =>
      Expr.lam (Binder.named x) (substMap (σ.delete x) e)
  | Expr.lam Binder.anon e => Expr.lam Binder.anon (substMap σ e)
  | Expr.app e₁ e₂ => Expr.app (substMap σ e₁) (substMap σ e₂)
  | Expr.litInt n => Expr.litInt n
  | Expr.plus e₁ e₂ => Expr.plus (substMap σ e₁) (substMap σ e₂)

-- Helper: applying empty substitution is identity
theorem substMap_empty (e : Expr) : substMap Subst.empty e = e := by
  sorry

-- Helper: substMap preserves closedness with the right context
theorem substMap_closed {X : List String} {σ : Subst} {e : Expr} :
    Expr.closed (X ++ σ.dom) e →
    (∀ x e, σ.lookup x = some e → Expr.closed X e) →
    Expr.closed X (substMap σ e) := by
  sorry

-- (** Lemma about the interaction with "normal" substitution. *)
-- Lemma subst_subst_map x es map e :
--   subst_closed [] map →
--   subst x es (subst_map (delete x map) e) =
--   subst_map (<[x:=es]> map) e.

-- Helper: composing substitutions
theorem subst_substMap_compose {x : String} {es : Expr} {θ : Subst} {e : Expr} :
    (∀ y e, θ.lookup y = some e → Expr.closed [] e) →
    subst x es (substMap (θ.delete x) e) = substMap (Subst.insert x es θ) e := by
  sorry

end STLC
