import Lampe.SeparationLogic.ValHeap
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Builtin.Basic
import Mathlib.Tactic.Lemma

namespace Lampe.Builtin

inductive StubOmni : Omni where

/--
This is a dummy builtin to stub out unimplemented builtins.

It is impossible to construct a proof of this and therefore any terms that use
this builtin will not type be provable, but they won't cause any unsoundness.
-/
def stub : Builtin := {
  omni := StubOmni,
  conseq := by
    unfold omni_conseq
    intros
    cases_type StubOmni,
  frame := by
    unfold omni_frame
    intros
    cases_type StubOmni
}

-- Note that many of the names here explicitly do not follow the Lean naming scheme, as they have
-- to match the name in extracted code that comes from Noir.
def arrayRefcount := stub
/-- Value-level semantics for the pinned Noir `as_witness(Field) -> Unit`.
It preserves the input value and heap and returns unit. Witness allocation is
outside this model. This is not `Field -> Field` and introduces no new choice.

Noir beta.21 documents forcing a value to a witness without changing its value:
https://github.com/noir-lang/noir/blob/89a0f0faf3a5f1273c8ac4843b7877882437e277/noir_stdlib/src/lib.nr#L113-L118
Its SSA interpreter explicitly treats this intrinsic as a no-op with no results:
https://github.com/noir-lang/noir/blob/89a0f0faf3a5f1273c8ac4843b7877882437e277/compiler/noirc_evaluator/src/ssa/interpreter/intrinsics.rs#L87-L91
The compiler may add an equality constraint for the new witness. We claim only
these value-level semantics, not correspondence with that constraint system.
-/
def asWitness := newTotalPureBuiltin
  ⟨[.field], .unit⟩
  (fun h![_] => ())
def blackBox := stub
def checkedTransmute := stub
def fmtstrAsCtstring := stub
def recursiveAggregation := stub
def sliceRefcount := stub
def strAsCtstring := stub

end Lampe.Builtin
