import PEqualNP.Defs.Represents
import Mathlib.Data.Finset.Powerset

namespace RouteLower

abbrev Word := BitVec 24
abbrev Pool := Finset Word
def target : Word := 16434824
def combine (isAnd : Bool) (a b : Word) := if isAnd then a &&& b else a ||| b

-- An unrestricted straight-line program may reuse every earlier wire.
inductive Builds : Nat → Pool → Prop where
  | done {s} (h : target ∈ s) : Builds 0 s
  | gate {n s a b} (op : Bool) (ha : a ∈ s) (hb : b ∈ s)
      (tail : Builds n (insert (combine op a b) s)) : Builds (n+1) s

-- Trace back only the operands actually needed by the output.
inductive Needs : Nat → Pool → Prop where
  | done : Needs 0 {target}
  | gate {n u} (op : Bool) (a b : Word) (tail : Needs n u)
      (used : combine op a b ∈ u) :
      Needs (n+1) (insert a (insert b (u.erase (combine op a b))))

theorem extract {n s} (h : Builds n s) :
    ∃ k ≤ n, ∃ u ⊆ s, Needs k u := by
  induction h with
  | done h => exact ⟨0, le_rfl, {target}, Finset.singleton_subset_iff.mpr h, Needs.done⟩
  | @gate n s a b op ha hb tail ih =>
    obtain ⟨k,hk,u,hu,hn⟩ := ih
    by_cases hc : combine op a b ∈ u
    · refine ⟨k+1, by omega, _, ?_, Needs.gate op a b hn hc⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_erase] at hx
      rcases hx with rfl | rfl | ⟨hne,hx⟩
      · exact ha
      · exact hb
      · exact (Finset.mem_insert.mp (hu hx)).resolve_left hne
    · refine ⟨k, by omega, u, ?_, hn⟩
      intro x hx
      rcases Finset.mem_insert.mp (hu hx) with rfl | hx'
      · exact (hc hx).elim
      · exact hx'

theorem small {n s} (h : Needs n s) : s.card ≤ n+1 := by
  induction h with
  | done => simp
  | @gate n u op a b _ used ih =>
    have h1 := Finset.card_insert_le a (insert b (u.erase (combine op a b)))
    have h2 := Finset.card_insert_le b (u.erase (combine op a b))
    have h3 := Finset.card_erase_add_one used
    omega

def Separates (s : Pool) : Prop :=
  ∀ p q : Fin 24, target.getLsbD p = true → target.getLsbD q = false →
    ∃ w ∈ s, w.getLsbD p = true ∧ w.getLsbD q = false

instance (s : Pool) : Decidable (Separates s) := by unfold Separates; infer_instance

theorem separated {n s} (h : Needs n s) : Separates s := by
  induction h with
  | done => exact fun p q hp hq => ⟨target, by simp, hp, hq⟩
  | @gate n u op a b tail used ih =>
    intro p q hp hq
    obtain ⟨w,hw,wp,wq⟩ := ih p q hp hq
    by_cases he : w = combine op a b
    · subst w
      have h : (a.getLsbD p = true ∧ a.getLsbD q = false) ∨
          (b.getLsbD p = true ∧ b.getLsbD q = false) := by
        cases op <;> simp [combine] at wp wq <;> grind
      rcases h with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · exact ⟨w, by simp [Finset.mem_erase.mpr ⟨he,hw⟩], wp,wq⟩

-- For a binary gate the only other wires we may retire at this step
-- are its own two operands. Each can instead remain live for reuse.
def successors (s : Pool) : Finset Pool :=
  s.biUnion fun a => s.biUnion fun b =>
    (({a,b} : Pool).powerset).biUnion fun keep =>
      ({insert (combine false a b) (keep ∪ ((s.erase a).erase b)),
        insert (combine true a b) (keep ∪ ((s.erase a).erase b))} : Finset Pool)

theorem successor {u : Pool} {op : Bool} {a b : Word}
    (used : combine op a b ∈ u) :
    u ∈ successors (insert a (insert b (u.erase (combine op a b)))) := by
  let s := insert a (insert b (u.erase (combine op a b)))
  let keep := u ∩ ({a,b} : Pool)
  have hk : keep ⊆ ({a,b} : Pool) := Finset.inter_subset_right
  have hx : u = insert (combine op a b) (keep ∪ ((s.erase a).erase b)) := by
    ext w
    simp only [keep,s, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      Finset.mem_inter, Finset.mem_erase]
    grind
  apply Finset.mem_biUnion.mpr
  refine ⟨a, by simp, Finset.mem_biUnion.mpr ⟨b, by simp, ?_⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨keep, Finset.mem_powerset.mpr hk, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  cases op
  · exact Or.inl hx
  · exact Or.inr hx

end RouteLower
