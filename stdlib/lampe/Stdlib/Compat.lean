import «std-1.0.0-beta.21».Extracted
import Lampe

namespace Lampe.Stdlib.Compat

open «std-1.0.0-beta.21»

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem is_bn254_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::compat::is_bn254».call h![] h![])
    (fun r => r = true) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Compat.env) (by solve_env_subset)
  enter_decl
  steps
  simp_all
  all_goals rfl

