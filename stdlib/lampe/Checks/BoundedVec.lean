import Stdlib.Collections.BoundedVec.Core

set_option backward.isDefEq.respectTransparency false

namespace Lampe

theorem SLP.exists_mono [LawfulHeap α] {H H' : β → SLP α}
    (h : ∀ v, H v ⊢ H' v) : (∃∃ v, H v) ⊢ (∃∃ v, H' v) := by
  intro st hst; unfold SLP.exists' at *; rcases hst with ⟨v, hv⟩; exact ⟨v, h v st hv⟩

theorem SLP.lift_mono [LawfulHeap α] {P Q : Prop}
    (h : P → Q) : (⟦P⟧ : SLP α) ⊢ ⟦Q⟧ := by
  intro st hst; unfold SLP.lift at *; exact ⟨h hst.1, hst.2⟩

theorem SLP.exists_star_lift_mono [LawfulHeap α] {H : β → SLP α} {P Q : β → Prop}
    (h : ∀ v, P v → Q v) :
    (∃∃ v, H v ⋆ ⟦P v⟧) ⊢ (∃∃ v, H v ⋆ ⟦Q v⟧) :=
  SLP.exists_mono fun v => SLP.star_mono_l (SLP.lift_mono (h v))

theorem STHoare.consequence_post
    {P : SLP (State p)} {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ P e Q₁) (h : ∀ v, Q₁ v ⊢ Q₂ v) :
    STHoare p Γ P e Q₂ :=
  STHoare.consequence SLP.entails_self (fun v => SLP.star_mono_r (h v)) h_hoare

end Lampe

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.21»

/-!
`collections::bounded_vec`

This file is the Hoare-logic layer for `BoundedVec`.

We are restarting the development to avoid baking in tuple-update helpers (`withLen`, `popped`, ...).
All method specs should be stated in terms of the semantic function `embed` and Lean `List`
operations; representation projections (`storage`, `len`) are used only as a bridge to the extracted
code during proofs.

First targets:
- `get_unchecked` (converges unconditionally, only constrained in-bounds, no storage mentioned in spec)
- `get` (requires in-bounds precondition, spec stated via `embed`)
-/

/-- The conclusion of one extend_from copy-loop step, stated in the exact form
that the goal takes after the loop body unfolds (i.e. with `Builtin.indexTpl`/
`% 4294967296` instead of `len`/`storage`).  Used by `extend_loop_step`. -/
private theorem extend_loop_body_eq {p T MaxLen : _} {self v : Repr p T MaxLen}
    {source : List (T.denote p)} {i : Nat}
    (hlenV : len v = len self)
    (hi_lt : (len self).toNat + i < 2 ^ 32)
    (htakeV : List.take ((len self).toNat + i) (storage v).toList =
              embed self ++ source.take i)
    (hiMax_v : (len self).toNat + i < (Builtin.indexTpl v Member.head).toList.length)
    (hi_src : i < source.length) :
    List.take (BitVec.toNat (Builtin.indexTpl self Member.head.tail) + (i + 1))
        ((Builtin.indexTpl v Member.head).toList.set
          ((BitVec.toNat (Builtin.indexTpl v Member.head.tail) + i) % 4294967296)
          (source[i]'hi_src)) =
      embed self ++ source.take (i + 1) := by
  -- The goal in `Builtin.indexTpl` form is defeq to the `len`/`storage` form.
  -- `BitVec.toNat (Builtin.indexTpl self Member.head.tail) = (len self).toNat` by def.
  -- `(Builtin.indexTpl v Member.head).toList = (storage v).toList` by def.
  -- `(BitVec.toNat (Builtin.indexTpl v Member.head.tail) + i) % 4294967296 = (len self).toNat + i`
  --   via `extend_loop_idx_mod`.
  have hbridge : (BitVec.toNat (Builtin.indexTpl v Member.head.tail) + i) % 4294967296
                  = (len self).toNat + i :=
    extend_loop_idx_mod (v := v) (self := self) hlenV hi_lt
  show List.take ((len self).toNat + (i + 1))
        ((storage v).toList.set
          ((BitVec.toNat (Builtin.indexTpl v Member.head.tail) + i) % 4294967296)
          (source[i]'hi_src)) = _
  rw [hbridge]
  exact List.take_set_extends htakeV hiMax_v hi_src

/-- Shared loop body step for `extend_from_*`. -/
local macro "extend_loop_step" hlenV:ident htakeV:ident
    hi32:ident hiMax:ident hMax_lt:ident
    hi_src:term : tactic =>
  `(tactic| (
    have _hi_lt := lt_of_lt_of_le $hiMax (Nat.le_of_lt $hMax_lt)
    have _hidx := extend_loop_idx_toNat $hlenV $hi32 _hi_lt
    constructor
    · simpa [len] using $hlenV
    · simp (config := {contextual := false})
        [storage, len, List.Vector.toList_set,
          (by simpa [len] using _hidx :
            (Builtin.indexTpl _ Member.head.tail +
              BitVec.ofNat 32 _).toNat = _),
          List.Vector.get_eq_get_toList,
          List.get_eq_getElem, nat_mod_4294967296 $hi32]
      try simp [extend_loop_idx_mod $hlenV _hi_lt]
      first
        | (simpa [len, Builtin.indexTpl_head_proj, Builtin.indexTpl_tail_proj,
                  nat_mod_4294967296 $hi32]
            using List.take_set_extends
              (by simpa [storage] using $htakeV)
              (by simpa [List.Vector.toList_length] using $hiMax)
              $hi_src)
        | exact extend_loop_body_eq $hlenV _hi_lt $htakeV
            (by simpa [storage] using $hiMax) $hi_src))

private theorem SLP.singleton_entails_exists_star_lift
    {ref : Ref (bvTp T MaxLen)} {tp : Tp}
    {v : Tp.denote p tp}
    {P : Tp.denote p tp → Prop}
    (h : P v) :
    ([ref ↦ ⟨tp, v⟩] : SLP (State p))
      ⊢ (∃∃ v', [ref ↦ ⟨tp, v'⟩] ⋆ ⟦P v'⟧) := by
  intro st hst
  exact ⟨v, st, ∅, by simp, by simp, hst, h, rfl⟩

private theorem get_unchecked_concrete_spec {p T MaxLen self index}
    {selfRef : Ref (bvTp T MaxLen)}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.21::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![selfRef, index])
      (fun (r : Tp.denote p T) => [selfRef ↦ ⟨bvTp T MaxLen, self⟩] ⋆
        ⟦r = (storage self).get ⟨index.toNat, hindex⟩⟧) := by
  apply STHoare.is_mono (Γ₁ := «std-1.0.0-beta.21».Collections.BoundedVec.env) (by solve_env_subset)
  enter_decl
  steps
  simp_all [storage]
  rfl

private theorem get_concrete_spec {p T MaxLen self index}
    {selfRef : Ref (bvTp T MaxLen)}
    (hbounded : bounded self)
    (hindex : index.toNat < (len self).toNat) :
    STHoare p env [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.21::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![selfRef, index])
      (fun (r : Tp.denote p T) => [selfRef ↦ ⟨bvTp T MaxLen, self⟩] ⋆
        ⟦r = (storage self).get ⟨index.toNat, lt_of_lt_of_le hindex hbounded⟩⟧) := by
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex hbounded
  enter_decl
  steps [get_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
    (self := self) (index := index) (hindex := hindex_max)]
  assumption

theorem get_unchecked_spec {p T MaxLen self index}
    {selfRef : Ref (bvTp T MaxLen)}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.21::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![selfRef, index])
      (fun (r : Tp.denote p T) => [selfRef ↦ ⟨bvTp T MaxLen, self⟩] ⋆
        ⟦∀ h : index.toNat < (embed self).length, r = (embed self).get ⟨index.toNat, h⟩⟧) := by
  apply STHoare.consequence_post (get_unchecked_concrete_spec (self := self) hindex)
  intro r
  apply SLP.star_mono_l
  apply SLP.lift_mono
  intro hr hlt
  have hstorage : index.toNat < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using hindex
  have hx := embed_getElem_toList (self := self) (i := index.toNat) (hxs := hlt) (hstorage := hstorage)
  simpa [List.Vector.get_eq_get_toList] using hr.trans hx.symm

theorem get_spec {p T MaxLen self index}
    {selfRef : Ref (bvTp T MaxLen)}
    (hwf : wellFormed self)
    (hindex : index.toNat < (embed self).length) :
    STHoare p env [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.21::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![selfRef, index])
      (fun (r : Tp.denote p T) => [selfRef ↦ ⟨bvTp T MaxLen, self⟩] ⋆
        ⟦r = (embed self).get ⟨index.toNat, hindex⟩⟧) := by
  have hb : bounded self := bounded_of_wellFormed hwf
  have hlen : (embed self).length = (len self).toNat := hwf
  have hi : index.toNat < (len self).toNat := by simpa [hlen] using hindex
  apply STHoare.consequence_post (get_concrete_spec (self := self) hb hi)
  intro r
  apply SLP.star_mono_l
  apply SLP.lift_mono
  intro hr
  have hstorage : index.toNat < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using lt_of_lt_of_le hi hb
  have hx := embed_getElem_toList (self := self) (i := index.toNat) (hxs := hindex) (hstorage := hstorage)
  simpa [List.Vector.get_eq_get_toList] using hr.trans hx.symm


end Lampe.Stdlib.Collections.BoundedVec
