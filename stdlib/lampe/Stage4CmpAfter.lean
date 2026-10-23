import «std-1.0.0-beta.21».Extracted
import Lampe

import Mathlib.Order.Compare
import Batteries.Classes.Order

import Stdlib.Extra
import Stdlib.Integer
import Stdlib.List
import Stdlib.Tp
import Stdlib.Tuple

set_option backward.isDefEq.respectTransparency false

namespace Lampe.Stdlib.Cmp

open «std-1.0.0-beta.21»
open Lampe.Stdlib

namespace Eq

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

/-- A shorthand for a call to the `std::cmp::Eq::eq` method. -/
@[reducible]
def eq {p}
    (generics : HList Kind.denote «std-1.0.0-beta.21::cmp::Eq».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.21::cmp::Eq».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.21::cmp::Eq».«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.21::cmp::Eq».eq.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.21::cmp::Eq».eq.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.21::cmp::Eq».eq generics Self associatedTypes fnGenerics

/-- Asserts that the provided `tp` has an implementation of `std::cmp::Eq` in the environment. -/
@[reducible]
def hasImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.21::cmp::Eq».hasImpl env h![] tp

theorem field_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] .field h![] h![] h![a, b])
    fun r: Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem u128_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 128) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 64) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 32) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 16) h![] h![] h![a, b])
    (fun r : Bool => r ↔ a = b) := by
  resolve_trait
  steps
  simp_all

theorem u8_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.u 8) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i8_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 8) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i16_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 16) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i32_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 32) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem i64_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.i 64) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem unit_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.unit) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  simp_all

theorem bool_eq_spec {p a b}
  : STHoare p env ⟦⟧
    (eq h![] (.bool) h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  · simp_all
  · exact ()

theorem array_eq_pure_spec {p T N a b}
    {t_eq : hasImpl env T}
    {t_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] T h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (T.array N) h![] h![] h![a, b])
    (fun r : Bool => ⟦r ↔ a = b⟧) := by
  resolve_trait
  steps
  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v = (a.toList.take i = b.toList.take i))
  · sl
    simp only [eq_iff_iff, true_iff]
    norm_cast
  · simp
  · intro i _ _
    steps [t_eq_f]
    rotate_left
    · exact ()

    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, eq_iff_iff, Lens.modify, Option.get_some, Bool.and_eq_true]

    simp_all only [Lens.modify, Option.isSome_some]
    conv => rhs; rw [←List.reverse_inj]

    generalize_proofs
    simp only [List.take_add_one, List.reverse_append]
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]
    simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq, List.reverse_inj]
    tauto

  steps
  simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le, eq_iff_iff]

  have h_a : BitVec.toNat N = a.toList.length := by
    simp

  have h_b : BitVec.toNat N = b.toList.length := by
    simp

  conv =>
    lhs
    congr
    · lhs; rw [h_a]
    · lhs; rw [h_b]

  simp_rw [List.take_length]

  exact Iff.intro (fun eq => List.Vector.eq _ _ eq) (fun eq => congrArg _ eq)

theorem slice_eq_pure_spec {p T a b}
    (h_trait_res : hasImpl env T)
    (h_eq_child: ∀a b, STHoare p env ⟦⟧ (eq h![] T h![] h![] h![a, b]) fun r : Bool => ⟦r ↔ a = b⟧)
  : STHoare p env ⟦⟧
    (eq h![] T.vector h![] h![] h![a, b])
    fun r : Bool => ⟦r ↔ a = b⟧ := by
  resolve_trait
  steps
  by_cases a.length = b.length
  · step_as ([result ↦ ⟨Tp.bool, true⟩]) (fun _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v ↔ a = b))
    · simp only [*, decide_true]
    · simp only [*, decide_true]
      apply STHoare.iteTrue_intro
      steps
      loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨.bool, v⟩] ⋆ (v = (a.take i = b.take i))
      · sl
        simp
      · simp
      · intro i _ _
        steps [h_eq_child]
        simp_all only [Nat.reducePow, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
          Int.toNat_zero, zero_le, eq_iff_iff, List.get_eq_getElem,
          Lens.modify, Option.get_some, Bool.and_eq_true]
        conv => rhs; rw [←List.reverse_inj]
        generalize_proofs
        simp only [List.take_add_one, List.reverse_append]
        rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem]
        · simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, List.cons.injEq, List.reverse_inj]
          tauto
        · exact ()
      steps
      rename List.length _ = _ => hp
      simp_all only [Nat.reducePow, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
        Int.toNat_zero, BitVec.toNat_ofNatLT, zero_le, List.take_length, eq_iff_iff]
      rw [←hp]
      simp
    steps
    simp_all
  · step_as (⟦⟧) (fun _ => ⟦⟧)
    · simp only [BitVec.ofNatLT, Nat.reducePow, BitVec.ofFin.injEq, Fin.mk.injEq, *, decide_false]
      apply STHoare.iteFalse_intro
      steps
    simp only [BitVec.ofNatLT, Nat.reducePow, BitVec.ofFin.injEq, Fin.mk.injEq, *, decide_false]
    have : a ≠ b := by
      intro h
      apply_fun List.length at h
      contradiction
    steps
    simp_all

theorem string_eq_pure_spec {p N a b}
    {u8_eq : «std-1.0.0-beta.21::cmp::Eq».hasImpl env h![] (.u 8)}
  : STHoare p env ⟦⟧
    (eq h![] (.str N) h![] h![] h![a, b])
    (fun r : Bool => ⟦r ↔ a = b⟧) := by
  resolve_trait
  steps [array_eq_pure_spec (t_eq := u8_eq) (t_eq_f := fun _ _ => u8_eq_spec)]
  simp_all only

theorem tuple2_eq_pure_spec {p A B self other}
    {A_eq : hasImpl env A}
    {B_eq : hasImpl env B}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all

theorem tuple3_eq_pure_spec {p A B C self other}
    {A_eq : hasImpl env A}
    {B_eq : hasImpl env B}
    {C_eq : hasImpl env C}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

set_option maxHeartbeats 500000 in
theorem tuple4_eq_pure_spec {p A B C D self other}
    {A_eq : hasImpl env A}
    {B_eq : hasImpl env B}
    {C_eq : hasImpl env C}
    {D_eq : hasImpl env D}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] D h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C, D]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f, D_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

set_option maxHeartbeats 1000000 in
theorem tuple5_eq_pure_spec {p A B C D E self other}
    {A_eq : hasImpl env A}
    {B_eq : hasImpl env B}
    {C_eq : hasImpl env C}
    {D_eq : hasImpl env D}
    {E_eq : hasImpl env E}
    {A_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] A h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {B_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] B h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {C_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] C h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {D_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] D h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
    {E_eq_f : ∀a b, STHoare p env ⟦⟧ (eq h![] E h![] h![] h![a, b]) (fun r : Bool => ⟦r ↔ a = b⟧)}
  : STHoare p env ⟦⟧
    (eq h![] (Tp.tuple none [A, B, C, D, E]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps [A_eq_f, B_eq_f, C_eq_f, D_eq_f, E_eq_f]
  all_goals try exact ()
  subst_vars

  repeat rcases self with ⟨_, self⟩
  repeat rcases other with ⟨_, other⟩

  simp_all only [Bool.and_eq_true, Prod.mk.injEq, and_true]
  tauto

theorem ordering_eq_spec {p self other}
  : STHoare p env ⟦⟧
    (eq h![] («std-1.0.0-beta.21::cmp::Ordering».tp h![]) h![] h![] h![self, other])
    (fun r : Bool => ⟦r ↔ self = other⟧) := by
  resolve_trait
  steps
  rcases self with ⟨_, ⟨_⟩⟩
  rcases other with ⟨_, ⟨_⟩⟩
  simp_all only [decide_eq_true_eq]
  tauto

end Eq

namespace Ord

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

abbrev NoirOrdering := «std-1.0.0-beta.21::cmp::Ordering».tp h![]

/-- A shorthand for a call to the `std::cmp::Ord::cmp` method. -/
@[reducible]
def cmp {p}
    (generics : HList Kind.denote «std-1.0.0-beta.21::cmp::Ord».«#genericKinds»)
    (Self : Tp)
    (associatedTypes : HList Kind.denote «std-1.0.0-beta.21::cmp::Ord».«#associatedTypesKinds»)
    (fnGenerics : HList Kind.denote «std-1.0.0-beta.21::cmp::Ord».cmp.«#genericKinds»)
  : HList (Tp.denote p)
      («std-1.0.0-beta.21::cmp::Ord».cmp.«#inputs» generics Self associatedTypes fnGenerics)
  → Expr (Tp.denote p)
      («std-1.0.0-beta.21::cmp::Ord».cmp.«#output» generics Self associatedTypes fnGenerics) :=
  «std-1.0.0-beta.21::cmp::Ord».cmp generics Self associatedTypes fnGenerics

/--
Convert a Lean ordering into a Noir `std::cmp::Ordering`.

We recommend providng the user with `std::cmp::Ordering`s at the boundary of the theorem for any
ordering values 'created' by the theorem.
-/
@[reducible]
def fromOrdering {p} : Ordering → (NoirOrdering.denote p)
| .lt => (0, ())
| .eq => (1, ())
| .gt => (2, ())

theorem fromOrdering_inj {p} : Function.Injective (fromOrdering (p := p)) := by
  intros a1 a2 h

  have : (0 : Tp.field.denote p) ≠ 2 := by
    apply Ne.symm (Ring.two_ne_zero _)
    rw [ZMod.ringChar_zmod_n]
    have := p.prop.2
    unfold Prime.natVal
    omega

  have : (2 : Tp.field.denote p) ≠ 1 := by
    intro h
    apply sub_eq_zero_of_eq at h
    norm_num at h

  cases a1 <;> cases a2 <;> {
    simp only [fromOrdering] at h
    try injection h
    simp_all
  }

lemma fromOrdering_eq_eq_iff {p} {o} : @fromOrdering p o = fromOrdering .eq ↔ o = .eq := by
  cases o
  · simp only [fromOrdering, reduceCtorEq, iff_false]
    intro hp
    injection hp
    simp_all
  · simp [fromOrdering]
  · simp only [fromOrdering, reduceCtorEq, iff_false]
    intro hp
    injection hp with hp
    apply sub_eq_zero_of_eq at hp
    norm_num at hp

/--
Convert a Noir `std-1.0.0-beta.21::cmp::Ordering` into a Lean ordering.

We recommend converting user-provided `std-1.0.0-beta.21::cmp::Ordering`s from the user, and
converting them within the theorem.

Note that in order to ensure that `toOrdering` is total, we calculate the input field element that
represents the ordering modulo three.
-/
def toOrdering {p} : (NoirOrdering.denote p) → Ordering
| (n, ()) => match (n.cast : ZMod 3) with
  | 0 => .lt
  | 1 => .eq
  | 2 => .gt

/-- Asserts that the provided `tp` has an implementation of `std::cmp::Ord` in the environment. -/
@[reducible]
def hasImpl (env : Env) (tp : Tp) := «std-1.0.0-beta.21::cmp::Ord».hasImpl env h![] tp

/--
A shorthand of the pure semantics for calling an embedded function implementing the ordering
comparison between two `tp`s.
-/
@[reducible]
def pureOrdSemantics {p} {tp : Tp} (env : Env) (emb : (Tp.comparator p) tp) (a b : Tp.denote p tp) :=
  STHoare p env ⟦⟧ (cmp h![] tp h![] h![] h![a, b]) (fun r => r = fromOrdering (emb a b))

/--
Provides the embedded semantics of the `<` operator based on the provided semantics of the `cmp`
function embedding.

This is necessary as `<` on an arbitrary `T` exists as a virtual operator that is desugared during
compilation to have semantics that match those given by these definition. In other words, there is
no definition of the operator that can have a theorem stated about it.

This embedding assumes that the function whose semantics it represents is pure, as is the `cmp`
function on which it depends.
-/
abbrev lt_emb {p T} (t_cmp_emb : Tp.comparator p T) := fun a b => t_cmp_emb a b = .lt

/--
Provides the embedded semantics of the `<=` operator based on the provided semantics of the `cmp`
function embedding.

This is necessary as `<=` on an arbitrary `T` exists as a virtual operator that is desugared during
compilation to have semantics that match those given by these definition. In other words, there is
no definition of the operator that can have a theorem stated about it.

This embedding assumes that the function whose semantics it represents is pure, as is the `cmp`
function on which it depends.
-/
abbrev le_emb {p T} (t_cmp_emb : Tp.comparator p T) :=
    fun a b => t_cmp_emb a b = .lt || t_cmp_emb a b = .eq

lemma le_emb_trans {p T} (t_cmp_emb : Tp.comparator p T) (t_cmp_trans : Std.TransCmp t_cmp_emb)
  : Transitive fun a b => le_emb t_cmp_emb a b = true := by
  unfold le_emb
  intro x y z
  simp only [Bool.or_eq_true, decide_eq_true_eq, ←Ordering.isLE_iff_eq_lt_or_eq_eq]
  exact t_cmp_trans.isLE_trans

/--
Provides the embedded semantics of the `>` operator based on the provided semantics of the `cmp`
function embedding.

This is necessary as `>` on an arbitrary `T` exists as a virtual operator that is desugared during
compilation to have semantics that match those given by these definition. In other words, there is
no definition of the operator that can have a theorem stated about it.

This embedding assumes that the function whose semantics it represents is pure, as is the `cmp`
function on which it depends.
-/
abbrev gt_emb {p T} (t_cmp_emb : Tp.comparator p T) :=
    fun a b => t_cmp_emb a b = .gt

/--
Provides the embedded semantics of the `>` operator based on the provided semantics of the `cmp`
function embedding.

This is necessary as `>` on an arbitrary `T` exists as a virtual operator that is desugared during
compilation to have semantics that match those given by these definition. In other words, there is
no definition of the operator that can have a theorem stated about it.

This embedding assumes that the function whose semantics it represents is pure, as is the `cmp`
function on which it depends.
-/
abbrev ge_emb {p T} (t_cmp_emb : Tp.comparator p T) :=
    fun a b => t_cmp_emb a b = .gt || t_cmp_emb a b = .eq

lemma ge_emb_trans {p T} (t_cmp_emb : Tp.comparator p T) (t_cmp_trans : Std.TransCmp t_cmp_emb)
  : Transitive fun a b => ge_emb t_cmp_emb a b = true := by
  unfold ge_emb
  intro x y z
  simp only [Bool.or_eq_true, decide_eq_true_eq, ←Ordering.isGE_iff_eq_gt_or_eq_eq]
  exact t_cmp_trans.isGE_trans

theorem less_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::cmp::Ordering::less».call h![] h![])
    (fun r => r = fromOrdering .lt) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Cmp.env) (by solve_env_subset)
  enter_decl
  steps
  subst_vars
  rfl

theorem equal_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::cmp::Ordering::equal».call h![] h![])
    (fun r => r = fromOrdering .eq) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Cmp.env) (by solve_env_subset)
  enter_decl
  steps
  subst_vars
  rfl

theorem greater_spec {p}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.21::cmp::Ordering::greater».call h![] h![])
    (fun r => r = fromOrdering .gt) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Cmp.env) (by solve_env_subset)
  enter_decl
  steps
  subst_vars
  rfl


end Ord
end Lampe.Stdlib.Cmp
