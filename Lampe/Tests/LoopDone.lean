import Lampe.Hoare.SepTotal

open Lampe

namespace LoopDoneRegression

theorem empty_loop_iff (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp}
    (Q : Option (State p × Unit) → Prop) (hle : lo ≥ hi) :
    Omni p Γ st (.loop lo hi body) Q ↔ Q (some (st, ())) := by
  constructor
  · intro h
    cases h with
    | loopDone _ hq => exact hq
    | loopNext hlt _ => exact False.elim ((STHoare.BitVec.not_lt.mpr hle) hlt)
  · exact Omni.loopDone hle

theorem empty_loop_preserves_state (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    Omni p Γ st (.loop lo hi body) (fun result => result = some (st, ())) := by
  exact Omni.loopDone hle rfl

theorem empty_loop_rejects_false (p : Prime) (Γ : Env) (st : State p)
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    ¬ Omni p Γ st (.loop lo hi body) (fun _ => False) := by
  intro h
  exact (empty_loop_iff p Γ st _ hle).mp h

theorem empty_loop_triple (p : Prime) (Γ : Env) (P : SLP (State p))
    {lo hi : U s} {body : U s → Expr (Tp.denote p) tp} (hle : lo ≥ hi) :
    STHoare p Γ P (.loop lo hi body) (fun _ => P) := by
  intro H st hp
  apply Omni.loopDone hle
  exact SLP.ent_star_top st hp

theorem empty_loop_rejects_false_triple (p : Prime) (Γ : Env) :
    ¬ STHoare p Γ ⟦⟧ (.loop (0 : U 32) 0 (fun _ => .skip)) (fun _ => ⟦False⟧) := by
  intro h
  have hrun := h ⟦⟧ ∅ (by simp [SLP.lift])
  have hpost := (empty_loop_iff p Γ ∅ _ (by simp)).mp hrun
  simp [SLP.star, SLP.lift] at hpost

#print axioms empty_loop_iff
#print axioms empty_loop_preserves_state
#print axioms empty_loop_rejects_false
#print axioms empty_loop_triple
#print axioms empty_loop_rejects_false_triple

end LoopDoneRegression
