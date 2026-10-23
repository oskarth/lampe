import «std-1.0.0-beta.21».Extracted
import Lampe

set_option backward.isDefEq.respectTransparency false

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.21»
open Lampe.Crypto

abbrev Poseidon2HasherTp : Tp :=
  «std-1.0.0-beta.21::hash::poseidon2::Poseidon2Hasher».tp h![]

abbrev Poseidon2HasherRepr (p : Prime) : Type := Tp.denote p Poseidon2HasherTp

def mkPoseidon2HasherRepr {p} (inputs : List (Fp p)) : Poseidon2HasherRepr p :=
  (inputs, ())

theorem default_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.21::default::Default».default h![] Poseidon2HasherTp h![] h![] h![])
      (fun r => r = mkPoseidon2HasherRepr []) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Hash.Poseidon2.env) (by solve_env_subset)
  resolve_trait
  simp only [Expr.literalArray, Expr.literalArgs]
  steps
  subst_vars
  rfl

theorem rate_spec {p} :
    STHoare p «std-1.0.0-beta.21».Hash.Poseidon2.env ⟦⟧
      («std-1.0.0-beta.21::hash::poseidon2::RATE».call h![] h![])
      (fun r => r = (3 : U 32)) := by
  enter_decl
  steps
  assumption

theorem poseidon2_permutation_builtin_spec {p Γ} {state : List.Vector (Fp p) 4} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [Tp.field.array (4 : U 32)] (Tp.field.array (4 : U 32))
        Builtin.poseidon2Permutation h![state])
      (fun r => r = Crypto.Poseidon2.noirPermutation4 state) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.poseidon2Permutation rfl () p Γ h![state]

theorem state_size_spec {p} :
    STHoare p «std-1.0.0-beta.21».Hash.Mod.env ⟦⟧
      («std-1.0.0-beta.21::hash::POSEIDON2_CONFIG_STATE_SIZE».call h![] h![])
      (fun r => r = (4 : U 32)) := by
  enter_decl
  steps
  assumption

theorem permutation4_spec {p} {input : List.Vector (Fp p) 4} :
    STHoare p «std-1.0.0-beta.21».Hash.Mod.env ⟦⟧
      («std-1.0.0-beta.21::hash::poseidon2_permutation».call h![(4 : U 32)] h![input])
      (fun r => r = Crypto.Poseidon2.noirPermutation4 input) := by
  enter_decl
  steps [state_size_spec, poseidon2_permutation_builtin_spec]
  assumption

theorem hasher_write_spec {p selfRef} {inputs : List (Fp p)} {input : Fp p} :
    STHoare p env
      [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩]
      («std-1.0.0-beta.21::hash::Hasher».write h![] Poseidon2HasherTp h![] h![] h![selfRef, input])
      (fun _ => [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr (inputs ++ [input])⟩]) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Hash.Poseidon2.env) (by solve_env_subset)
  resolve_trait
  steps


theorem hasher_finish_ref_empty_spec {p selfRef} :
    STHoare p env [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr []⟩]
      («std-1.0.0-beta.21::hash::Hasher».finish_ref h![] Poseidon2HasherTp h![] h![] h![selfRef])
      (fun r => [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr []⟩] ⋆
        ⟦r = (Crypto.Poseidon2.noirPermutation4 (List.Vector.replicate 4 0)).get ⟨0, by decide⟩⟧) := by
  apply STHoare.is_mono
    (Γ₁ := «std-1.0.0-beta.21».Hash.Poseidon2.env ++ «std-1.0.0-beta.21».Hash.Mod.env)
    (by apply Env.append_subset_iff.mpr; constructor <;> solve_env_subset)
  resolve_trait
  steps [rate_spec, permutation4_spec, STHoare.loopDone_intro]
  all_goals simp_all [mkPoseidon2HasherRepr]
  steps [rate_spec, permutation4_spec, STHoare.loopDone_intro]
  all_goals simp_all [mkPoseidon2HasherRepr]
  all_goals rfl

end Lampe.Stdlib.Hash.Poseidon2
