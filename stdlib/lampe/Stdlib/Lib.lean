import «std-1.0.0-beta.21».Extracted
import Lampe

namespace Lampe.Stdlib.Lib

open «std-1.0.0-beta.21»

set_option maxHeartbeats 800000 in
/--
Note that as printing is inherently an unconstrained-only operation, this theorem is not capable of
asserting actual properties about the printing operation. Instead it simply exists to make it easy
to step through print calls when verifying your programs.
-/
theorem println_spec {p T a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::println».call h![T] h![a])
    (fun r => r = ()) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Lib.env) (by solve_env_subset)
  enter_decl
  step_as (⟦⟧) (fun r => r = ())
  steps
  step_as (⟦⟧) (fun r => (r : Tp.denote p .unit) = ())
  · enter_decl
    steps
    all_goals rfl
  · steps
    simp_all
    all_goals rfl

set_option maxHeartbeats 800000 in
/--
Note that as printing is inherently an unconstrained-only operation, this theorem is not capable of
asserting actual properties about the printing operation. Instead it simply exists to make it easy
to step through print calls when verifying your programs.
-/
theorem print_spec {p T a}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::print».call h![T] h![a])
    (fun r => r = ()) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Lib.env) (by solve_env_subset)
  enter_decl
  step_as (⟦⟧) (fun r => r = ())
  steps
  step_as (⟦⟧) (fun r => (r : Tp.denote p .unit) = ())
  · enter_decl
    steps
    all_goals rfl
  · steps
    simp_all
    all_goals rfl

-- TODO (#108) verify_proof_with_type

