import Lampe

namespace Checks.AsWitness
open Lampe

theorem asWitness_run {p Γ st} (x : Fp p) :
    Omni p Γ st (.callBuiltin [.field] .unit Builtin.asWitness h![x])
      (fun r => r = some (st, ())) := by
  apply Omni.callBuiltin
  exact Builtin.genericPureOmni.ok (a := ()) True.intro rfl

theorem asWitness_exact {p st} (x : Fp p) (Q) :
    Builtin.asWitness.omni p st [.field] .unit h![x] Q ↔ Q (some (st, ())) := by
  constructor
  · intro h
    cases h with
    | ok _ h => exact h
    | err h _ => exact False.elim (h True.intro)
  · intro h
    exact Builtin.genericPureOmni.ok (a := ()) True.intro h

theorem asWitness_cannot_fail {p st} (x : Fp p) :
    ¬ Builtin.asWitness.omni p st [.field] .unit h![x] (fun r => r = none) := by
  rw [asWitness_exact]
  simp

theorem asWitness_rejects_field_result {p st Q} (x : Fp p) :
    ¬ Builtin.asWitness.omni p st [.field] .field h![x] Q := by
  intro h
  cases h

theorem asWitness_rejects_integer {p st Q} (x : U 32) :
    ¬ Builtin.asWitness.omni p st [.u 32] .unit h![x] Q := by
  intro h
  cases h

theorem other_stubs_empty {p st argTps outTp args Q} :
    ¬ Builtin.arrayRefcount.omni p st argTps outTp args Q ∧
    ¬ Builtin.blackBox.omni p st argTps outTp args Q ∧
    ¬ Builtin.checkedTransmute.omni p st argTps outTp args Q ∧
    ¬ Builtin.fmtstrAsCtstring.omni p st argTps outTp args Q ∧
    ¬ Builtin.recursiveAggregation.omni p st argTps outTp args Q ∧
    ¬ Builtin.sliceRefcount.omni p st argTps outTp args Q ∧
    ¬ Builtin.strAsCtstring.omni p st argTps outTp args Q := by
  repeat' apply And.intro
  all_goals intro h; cases h

#print axioms Builtin.asWitness
#print axioms asWitness_run
#print axioms asWitness_exact
#print axioms asWitness_cannot_fail
#print axioms asWitness_rejects_field_result
#print axioms asWitness_rejects_integer
#print axioms other_stubs_empty
end Checks.AsWitness
