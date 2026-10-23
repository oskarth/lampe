import «std-1.0.0-beta.21».Extracted
import Lampe
import Stdlib.List
import Stdlib.TraitMethods

set_option backward.isDefEq.respectTransparency false

namespace Lampe.Stdlib.Vector
open «std-1.0.0-beta.21»

set_option maxRecDepth 2000

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem append_spec {p T a b}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::vector::append».call h![T] h![a, b])
    (fun r => r = a ++ b) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Vector.env) (by solve_env_subset)
  enter_decl
  steps
  step_as ([self ↦ ⟨T.vector, a⟩]) (fun _ => [self ↦ ⟨T.vector, a ++ b⟩])
  · steps

    loop_inv nat fun i hlo hhi => [self ↦ ⟨T.vector, a ++ (b.take i)⟩]
    · simp
    · simp
    · intro cond hlo hhi
      steps
      simp_all
    · steps
      simp_all
  · steps
    simp_all

theorem as_array_spec {p T N input}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::vector::as_array».call h![T, N] h![input])
    (fun r => r.toList = input) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Vector.env) (by solve_env_subset)
  enter_decl
  steps
  loop_inv nat fun i hlo hhi => ∃∃v, [array ↦ ⟨T.array N, v⟩] ⋆ (v.toList.take i = input.take i)
  · sl; simp
  · simp
  · intro i _ _
    steps
    simp_all only [beq_true, decide_eq_true_eq, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, Lens.modify, Lens.get, Access.modify,
      BitVec.toNat_ofNatLT, ↓reduceDIte, Builtin.CastTp.cast, BitVec.setWidth_eq, List.get_eq_getElem, Option.bind_eq_bind,
      Option.bind_some, Option.bind_fun_some, Option.get_some, List.Vector.toList_set]
    rename_i take_of_vec_eq_input
    rw [List.take_add_one]
    rw [List.take_set]
    rw [take_of_vec_eq_input]
    simp_all only [Lens.modify, Lens.get, Access.modify, BitVec.toNat_ofNatLT, ↓reduceDIte, Builtin.CastTp.cast, BitVec.setWidth_eq,
      List.get_eq_getElem, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.isSome_some, List.length_set, List.Vector.toList_length, getElem?_pos,
      List.getElem_set_self, Option.toList_some]

    have : i < input.length := by simp_all
    have h : (List.take i input).set i input[i] = List.take i input := by
      rw [List.set_eq_of_length_le (by simp_all)]
    rw [h, List.take_append_getElem]

  steps
  rename_i a v _
  subst_vars
  have h1 : input.length = BitVec.toNat N := by aesop
  have h2 : v.toList.length = BitVec.toNat N := by simp_all
  conv at a =>
    congr
    · arg 1; rw [←h2]
    · rw [←h1]

  rw [List.take_length] at a
  simp_all


end Lampe.Stdlib.Vector
