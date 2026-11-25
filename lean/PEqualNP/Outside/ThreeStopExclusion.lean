import PEqualNP.Defs.Represents
import Mathlib.Data.Finset.Powerset

namespace PEqualNP.Outside.ThreeStopExclusion_aux

abbrev Word := BitVec 288
abbrev Pool := Finset Word
def target : Word := BitVec.ofNat 288 (2^144-1)
def combine (isAnd : Bool) (a b : Word) := if isAnd then a &&& b else a ||| b

-- An unrestricted straight-line program may reuse every earlier wire.
inductive Builds : Nat → Pool → Prop where
  | done {s} (h : target ∈ s) : Builds 0 s
  | gate {n s a b} (op : Bool) (ha : a ∈ s) (hb : b ∈ s)
      (tail : Builds n (insert (combine op a b) s)) : Builds (n+1) s

-- Trace back only the operands actually needed by the output.
inductive Needs : Nat → Pool → Prop where
  | done : Needs 0 {target}
  | gate {n u} (op : Bool) (a b : Word) (freshA : combine op a b ≠ a) (freshB : combine op a b ≠ b) (tail : Needs n u)
      (used : combine op a b ∈ u) :
      Needs (n+1) (insert a (insert b (u.erase (combine op a b))))

theorem extract {n s} (h : Builds n s) :
    ∃ k ≤ n, ∃ u ⊆ s, Needs k u := by
  induction h with
  | done h => exact ⟨0, le_rfl, {target}, Finset.singleton_subset_iff.mpr h, Needs.done⟩
  | @gate n s a b op ha hb tail ih =>
    obtain ⟨k,hk,u,hu,hn⟩ := ih
    by_cases old : combine op a b ∈ s
    · exact ⟨k, by omega, u, (by simpa [Finset.insert_eq_of_mem old] using hu), hn⟩
    by_cases hc : combine op a b ∈ u
    · refine ⟨k+1, by omega, _, ?_, Needs.gate op a b (fun e => old (e.symm ▸ ha)) (fun e => old (e.symm ▸ hb)) hn hc⟩
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
  | @gate n u op a b _ _ _ used ih =>
    have h1 := Finset.card_insert_le a (insert b (u.erase (combine op a b)))
    have h2 := Finset.card_insert_le b (u.erase (combine op a b))
    have h3 := Finset.card_erase_add_one used
    omega

def Separates (s : Pool) : Prop :=
  ∀ p q : Fin 288, target.getLsbD p = true → target.getLsbD q = false →
    ∃ w ∈ s, w.getLsbD p = true ∧ w.getLsbD q = false


theorem separated {n s} (h : Needs n s) : Separates s := by
  induction h with
  | done => exact fun p q hp hq => ⟨target, by simp, hp, hq⟩
  | @gate n u op a b freshA freshB tail used ih =>
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def positives : List Nat := [3,7,9,10,14,15,17,19,20,21,22,23]
def negatives : List Nat := [0,1,2,4,5,6,8,11,12,13,16,18]
def rowIndex (p : Fin 288) : Nat :=
  if p < 144 then positives.getD (p.val / 12) 0 else negatives.getD (p.val % 12) 0

def chunks (xs : List Nat) : Word := BitVec.ofNat 288 (xs.foldl (fun a b => (a <<< 32) + b) 0)
def pins : List Word :=
  [chunks [7341824,1879507056,117469191,7341824,1879506944,0,0,0,0],
   chunks [25171969,2149056896,402751512,25171969,2149056512,0,0,0,4095],
   chunks [100687878,6292992,1611006048,100687878,6291456,0,0,0,16773120],
   chunks [134250504,8390656,2148008064,134250504,8388608,0,0,65535,4278190080],
   chunks [805503024,50343939,3146496,805503024,50331648,0,0,268369920,0],
   chunks [1074004032,67125252,4195328,1074004032,67108864,0,1048575,4026531840,0],
   chunks [2148008064,134250504,8390656,2148008064,134217728,4095,4293918720,0,0],
   chunks [0,0,0,0,65535,4294963200,0,0,0],
   chunks [2451120530,421630489,563222817,2451120530,421593088,16773120,255,4026531855,4278194175],
   chunks [1621494368,2785697958,174106122,1621494368,2785673231,4278190080,4293918720,65520,16773120],
   chunks [222352397,1087638848,3557638356,222352397,1087700976,4095,1048320,268369920,0]]
def initial : Pool := insert 0 (insert (BitVec.allOnes 288) pins.toFinset)
def sample (p : Fin 288) := oneEach
  (Fin.ofNat 8 (rowIndex p / 3)) (Fin.ofNat 3 (rowIndex p % 3))
def bit (p : Fin 288) (w : Word) := w.getLsbD p.val
def run (gs : List Gate) (x : List Bool) :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) x

set_option maxRecDepth 10000 in
theorem operands (g : Gate) (ws : List Word) (s : Pool)
    (hs : ∀ w ∈ ws, w ∈ s) (hz : 0 ∈ s) (ho : BitVec.allOnes 288 ∈ s)
    (allowed : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ op a b, a ∈ s ∧ b ∈ s ∧ ∀ p : Fin 288,
      bit p (combine op a b) =
        g.op.eval (g.inputs.map fun i => (ws.map (bit p)).getD i false) := by
  have mem (i : Nat) : ws.getD i 0 ∈ s := by
    by_cases h : i < ws.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs ws[i] (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega : ws.length ≤ i)]; exact hz
  have readBit (p : Fin 288) (i : Nat) :
      (ws.map (bit p)).getD i false = bit p (ws.getD i 0) := by
    simpa [bit] using (List.getD_map (l := ws) (d := (0 : Word)) (n := i) (bit p))
  obtain ⟨o,ins⟩ := g
  obtain ⟨hop,hlen⟩ := allowed
  change o = GateOp.and ∨ o = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · have all : ∀ q : Fin 288, bit q (combine true (BitVec.allOnes 288) (BitVec.allOnes 288)) = true := by decide
      exact ⟨true,_,_,ho,ho,all⟩
    · exact ⟨false,_,_,hz,hz,fun p => by simp [bit,combine,GateOp.eval]⟩
  | cons i rest =>
    cases rest with
    | nil =>
      refine ⟨false,_,_,mem i,mem i,fun p => ?_⟩
      rcases hop with rfl | rfl <;> simp [ -List.getD_eq_getElem?_getD, combine,GateOp.eval,readBit]
    | cons j rest =>
      cases rest with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨true,_,_,mem i,mem j,fun p => by simp [ -List.getD_eq_getElem?_getD, combine,GateOp.eval,readBit,bit]⟩
        · exact ⟨false,_,_,mem i,mem j,fun p => by simp [ -List.getD_eq_getElem?_getD, combine,GateOp.eval,readBit,bit]⟩

theorem simulate (gs : List Gate) (ws : List Word) (s : Pool) (out : Nat)
    (hs : ∀ w ∈ ws, w ∈ s) (hz : 0 ∈ s) (ho : BitVec.allOnes 288 ∈ s)
    (allowed : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (correct : ∀ p, (run gs (ws.map (bit p))).getD out false = bit p target) :
    Builds gs.length s := by
  induction gs generalizing ws s with
  | nil =>
    have hw : ws.getD out 0 = target := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have h := correct ⟨i,hi⟩
      change (ws.map (bit ⟨i,hi⟩)).getD out false = _ at h
      have eq := List.getD_map (l := ws) (d := (0 : Word)) (n := out) (bit ⟨i,hi⟩)
      change bit ⟨i,hi⟩ (ws.getD out 0) = bit ⟨i,hi⟩ target
      rw [← eq]
      simpa [bit] using h
    apply Builds.done
    rw [← hw]
    by_cases h : out < ws.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs ws[out] (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega : ws.length ≤ out)]; exact hz
  | cons g gs ih =>
    obtain ⟨op,a,b,ha,hb,hbit⟩ := operands g ws s hs hz ho (allowed g (by simp))
    apply Builds.gate op ha hb
    apply ih (ws ++ [combine op a b])
    · intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Finset.mem_insert_of_mem (hs _ hw)
      · simp
    · exact Finset.mem_insert_of_mem hz
    · exact Finset.mem_insert_of_mem ho
    · exact fun g' hg => allowed g' (by simp [hg])
    · intro p
      simpa [run,List.map_append,hbit] using correct p

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem model_bridge {k : Nat}
    (ex : RepSizeAtMost (fun (u : Fin 8) (v : Fin 3) =>
      (16434824 : Nat).testBit (3*u.val + v.val)) k) :
    ∃ n ≤ k, ∃ s ⊆ initial, Needs n s := by
  obtain ⟨c,hm,hs,hc⟩ := ex
  have eq : ∀ p : Fin 288, pins.map (bit p) = sample p := by decide
  have h := simulate c.gates pins initial c.output (fun w hw => by simp [initial,hw])
    (by simp [initial]) (by simp [initial]) hm (fun p => by
      rw [eq]
      have h := hc (Fin.ofNat 8 (rowIndex p / 3)) (Fin.ofNat 3 (rowIndex p % 3))
      have t : ∀ q : Fin 288, (16434824 : Nat).testBit
        (3 * (Fin.ofNat 8 (rowIndex q / 3)).val + (Fin.ofNat 3 (rowIndex q % 3)).val) =
        bit q target := by decide
      exact h.trans (t p))
  obtain ⟨n,hn,s,hsub,hneed⟩ := extract h
  exact ⟨n,le_trans hn hs,s,hsub,hneed⟩

def full : Nat := 2^144-1
def score (w : Word) : Nat :=
  (w.toNat &&& ((w.toNat >>> 144) ^^^ full)) &&& full
def unionScore : List Word → Nat
  | [] => 0
  | w :: ws => score w ||| unionScore ws

theorem has_bit (xs : List Word) (i : Nat) :
    (unionScore xs).testBit i = true ↔ ∃ w ∈ xs, (score w).testBit i = true := by
  induction xs with
  | nil => simp [unionScore]
  | cons w ws ih => simp [unionScore,ih]

theorem complete_score (xs : List Word) (h : Separates xs.toFinset) :
    unionScore xs = full := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hf : full.testBit i = decide (i < 144) := Nat.testBit_two_pow_sub_one 144 i
  by_cases hi : i < 144
  · have lo : ∀ j : Fin 144, target.getLsbD j.val = true := by decide +kernel
    have high : ∀ j : Fin 144, target.getLsbD (j.val+144) = false := by decide +kernel
    obtain ⟨w,hw,ha,hb⟩ := h ⟨i,by omega⟩ ⟨i+144,by omega⟩ (lo ⟨i,hi⟩) (high ⟨i,hi⟩)
    simp only [List.mem_toFinset] at hw
    have hwa : w.toNat.testBit i = true := ha
    have hwb : w.toNat.testBit (144+i) = false := by rw [Nat.add_comm]; exact hb
    rw [show full.testBit i = true by simp [hf,hi]]
    exact (has_bit xs i).mpr ⟨w,hw,by simp [score,hf,hi,hwa,hwb]⟩
  · rw [show full.testBit i = false by simp [hf,hi]]
    apply Bool.eq_false_iff.mpr
    intro hx
    obtain ⟨w,_,hw⟩ := (has_bit xs i).mp hx
    simp [score,hf,hi] at hw

def keepOptions (a b : Word) : List (List Word) := [[],[a],[b],[a,b]]

-- Each list contains distinct wires. Once two operands are removed, keep
-- just those that are needed again. The score checks all 144 comparisons.
def nextPools (budget : Nat) (xs : List Word) : List (List Word) :=
  xs.flatMap fun a => xs.flatMap fun b =>
    if a.toNat < b.toNat then
      let rest := xs.filter fun w => w != a && w != b
      let cover := unionScore rest
      (keepOptions a b).flatMap fun keep =>
        if rest.length + keep.length + 1 ≤ budget+1 then
          let mask := unionScore keep ||| cover
          [combine false a b, combine true a b].filterMap fun z =>
            if (score z ||| mask) == full then some (z :: (keep ++ rest)) else none
        else []
    else []

theorem join_score (x y : List Word) : unionScore (x++y) = unionScore x ||| unionScore y := by
  induction x with
  | nil => simp [unionScore]
  | cons w ws ih => simp [unionScore,ih,Nat.or_assoc]

theorem next_complete (xs : List Word) (u : Pool) (op : Bool) (a b : Word)
    (hxs : xs.Nodup) (ha : combine op a b ≠ a) (hb : combine op a b ≠ b)
    (used : combine op a b ∈ u)
    (parent : xs.toFinset = insert a (insert b (u.erase (combine op a b))))
    (budget : Nat) (hc : u.card ≤ budget+1) (hs : Separates u) :
    ∃ ys ∈ nextPools budget xs, ys.Nodup ∧ ys.toFinset = u := by
  suffices ordered : ∀ (a b : Word), a.toNat < b.toNat →
      combine op a b ∈ u → combine op a b ≠ a → combine op a b ≠ b →
      xs.toFinset = insert a (insert b (u.erase (combine op a b))) →
      ∃ ys ∈ nextPools budget xs, ys.Nodup ∧ ys.toFinset = u by
    rcases lt_trichotomy a.toNat b.toNat with h | he | h
    · exact ordered a b h used ha hb parent
    · have := BitVec.eq_of_toNat_eq he; subst b; cases op <;> simp [combine] at ha
    · have comm : combine op b a = combine op a b := by
        cases op <;> simp [combine,BitVec.and_comm,BitVec.or_comm]
      apply ordered b a h
      · rwa [comm]
      · rwa [comm]
      · rwa [comm]
      · rwa [comm,Finset.insert_comm b a]
  intro a b hab used ha hb parent
  let rest := xs.filter fun w => w != a && w != b
  let keep := ([a,b] : List Word).filter fun w => decide (w ∈ u)
  let z := combine op a b
  let ys := z :: (keep ++ rest)
  have ab : a ≠ b := fun e => (ne_of_lt hab) (congrArg BitVec.toNat e)
  have ks : keep ∈ keepOptions a b := by
    by_cases x : a ∈ u <;> by_cases y : b ∈ u <;> simp [keepOptions,keep,x,y]
  have ma (w : Word) : w ∈ xs ↔ w = a ∨ w = b ∨ w ≠ z ∧ w ∈ u := by
    rw [← List.mem_toFinset, parent]
    simp [z]
  have mr (w : Word) : w ∈ rest ↔ w ≠ a ∧ w ≠ b ∧ w ≠ z ∧ w ∈ u := by
    simp [rest,ma]; tauto
  have mk (w : Word) : w ∈ keep ↔ (w = a ∨ w = b) ∧ w ∈ u := by simp [keep]
  have same : ys.toFinset = u := by
    ext w
    simp only [ys,List.mem_toFinset,List.mem_cons,List.mem_append,mr,mk]
    grind
  have nd : ys.Nodup := by
    have nk : keep.Nodup := (show ([a,b] : List Word).Nodup by simp [ab]).filter _
    have nr : rest.Nodup := hxs.filter _
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_append,mk,mr]
      change z ≠ a at ha
      change z ≠ b at hb
      tauto
    · apply List.nodup_append.mpr
      refine ⟨nk,nr,?_⟩
      intro x hx y hy eq
      subst y
      have h1 := (mk x).mp hx
      have h2 := (mr x).mp hy
      tauto
  have len := List.toFinset_card_of_nodup nd
  rw [same] at len
  have lim : rest.length + keep.length + 1 ≤ budget + 1 := by
    simp only [ys,List.length_cons,List.length_append] at len; omega
  have sc := complete_score ys (same ▸ hs)
  simp only [ys,unionScore,join_score] at sc
  refine ⟨ys,?_,nd,same⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,(ma a).mpr (Or.inl rfl),List.mem_flatMap.mpr ⟨b,(ma b).mpr (by simp),?_⟩⟩
  simp only [hab,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨keep,ks,?_⟩
  change ys ∈ (if rest.length + keep.length + 1 ≤ budget+1 then _ else _)
  rw [ite_eq_left lim]
  apply List.mem_filterMap.mpr
  refine ⟨z,by cases op <;> simp [z],?_⟩
  change (if (score z ||| (unionScore keep ||| unionScore rest)) == full then some ys else none) = some ys
  simp [sc]

def graph (u : Fin 8) (v : Fin 3) := (16434824 : Nat).testBit (3*u.val+v.val)

def subs : List Word → List (List Word)
  | [] => [[]]
  | x :: xs => let ss := subs xs; ss ++ ss.map (x :: ·)

theorem filter_subs (f : Word → Bool) (xs : List Word) : xs.filter f ∈ subs xs := by
  induction xs with
  | nil => simp [subs]
  | cons x xs ih =>
    cases e : f x <;> simp [subs,e,ih]

def seed := 0 :: BitVec.allOnes 288 :: pins
def roots := (subs seed).filter fun xs => decide (xs.length ≤ 11) && (unionScore xs == full)

def Dead (k : Nat) (xs : List Word) := ∀ n ≤ k, ¬ Needs n xs.toFinset
abbrev Certified (k : Nat) := {xs : List Word // Dead k xs}

def certify (k : Nat) (xs : List Word) (cs : List (Certified k))
    (ok : xs.Nodup ∧ target ∉ xs ∧
      ∀ ys ∈ nextPools k xs, ys.Nodup → ∃ zs ∈ cs.map Subtype.val, ys.toFinset = zs.toFinset) :
    Certified (k+1) := by
  refine ⟨xs,?_⟩
  intro n hn h
  generalize he : xs.toFinset = s at h
  cases h with
  | done =>
    exact ok.2.1 (List.mem_toFinset.mp (he ▸ Finset.mem_singleton_self _))
  | @gate m u op a b ha hb tail used =>
    have hm : m ≤ k := by omega
    obtain ⟨ys,hy,nd,same⟩ := next_complete xs u op a b ok.1 ha hb used he k
      (le_trans (small tail) (by omega)) (separated tail)
    obtain ⟨zs,hz,eq⟩ := ok.2.2 ys hy nd
    obtain ⟨node,hnode,rfl⟩ := List.mem_map.mp hz
    apply node.property m hm
    rwa [← eq,same]

theorem from_nodes (cs : List (Certified 10))
    (ok : ∀ xs ∈ roots, ∃ zs ∈ cs.map Subtype.val, xs.toFinset = zs.toFinset) :
    ¬ RepSizeAtMost graph 10 := by
  intro ex
  obtain ⟨n,hn,s,hs,h⟩ := model_bridge ex
  let xs := seed.filter fun w => decide (w ∈ s)
  have he : xs.toFinset = s := by
    have initEq : seed.toFinset = initial := by simp [seed,initial]
    ext w
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (initEq ▸ hs hw)
  have distinct : seed.Nodup := by decide
  have len := List.toFinset_card_of_nodup (distinct.filter (fun w => decide (w ∈ s)))
  change xs.toFinset.card = xs.length at len
  rw [he] at len
  have bound := small h
  have hx : xs ∈ roots := List.mem_filter.mpr ⟨filter_subs _ _,by
    simp [show xs.length ≤ 11 by omega,complete_score xs (he ▸ separated h)]⟩
  obtain ⟨zs,hz,eq⟩ := ok xs hx
  obtain ⟨node,_,rfl⟩ := List.mem_map.mp hz
  apply node.property n hn
  rwa [← eq,he]


def i0 : Word := pins.getD 0 0
def i1 : Word := pins.getD 1 0
def i2 : Word := pins.getD 2 0
def i3 : Word := pins.getD 3 0
def i4 : Word := pins.getD 4 0
def i5 : Word := pins.getD 5 0
def i6 : Word := pins.getD 6 0
def i7 : Word := pins.getD 7 0
def i8 : Word := pins.getD 8 0
def i9 : Word := pins.getD 9 0
def i10 : Word := pins.getD 10 0
def iZero : Word := 0
def iOnes : Word := BitVec.allOnes 288
def w13 : Word := i1 ||| i9
def w14 : Word := i1 ||| i10
def w15 : Word := i2 ||| i8
def w16 : Word := i2 ||| i10
def w17 : Word := i3 ||| i10
def w18 : Word := i4 ||| i8
def w19 : Word := i4 ||| i9
def w20 : Word := i5 ||| i9
def w21 : Word := i6 ||| i8
def w22 : Word := i0 ||| i8
def w23 : Word := i0 ||| i9
def w24 : Word := i0 ||| i10
def w25 : Word := i1 ||| i3
def w26 : Word := i1 ||| i5
def w27 : Word := i1 &&& i8
def w28 : Word := i1 ||| i7
def w29 : Word := i2 ||| i3
def w30 : Word := i2 ||| i6
def w31 : Word := i2 &&& i9
def w32 : Word := i2 ||| i7
def w33 : Word := i3 ||| i7
def w34 : Word := i4 ||| i5
def w35 : Word := i4 ||| i6
def w36 : Word := i4 &&& i10
def w37 : Word := i4 ||| i7
def w38 : Word := i5 ||| i7
def w39 : Word := i6 ||| i7
def w40 : Word := i8 ||| i7
def w41 : Word := i9 ||| i7
def w42 : Word := i10 ||| i7
def w43 : Word := w27 ||| i3
def w44 : Word := w27 ||| i5
def w45 : Word := w27 ||| i9
def w46 : Word := w27 ||| i10
def w47 : Word := w27 ||| i7
def w48 : Word := w31 ||| i3
def w49 : Word := w31 ||| i6
def w50 : Word := w31 ||| i8
def w51 : Word := w31 ||| i10
def w52 : Word := w31 ||| i7
def w53 : Word := w36 ||| i5
def w54 : Word := w36 ||| i6
def w55 : Word := w36 ||| i8
def w56 : Word := w36 ||| i9
def w57 : Word := w36 ||| i7
def w58 : Word := i1 ||| w17
def w59 : Word := i2 ||| w17
def w60 : Word := i1 ||| w42
def w61 : Word := i2 ||| w42
def w62 : Word := i3 ||| w42
def w63 : Word := i1 ||| w20
def w64 : Word := i4 ||| w20
def w65 : Word := i1 ||| w41
def w66 : Word := i4 ||| w41
def w67 : Word := i5 ||| w41
def w68 : Word := i2 ||| w21
def w69 : Word := i4 ||| w21
def w70 : Word := i2 ||| w40
def w71 : Word := i4 ||| w40
def w72 : Word := i6 ||| w40
def w73 : Word := w27 ||| w20
def w74 : Word := w27 ||| w17
def w75 : Word := w31 ||| w21
def w76 : Word := w31 ||| w17
def w77 : Word := w36 ||| w21
def w78 : Word := w36 ||| w20
def n5_0 := certify 4 [i1,i2,i4,w21,w67,w62] [] (by decide +kernel)
def n5_1 := certify 4 [i1,i2,i4,w20,w62,w72] [] (by decide +kernel)
def n5_2 := certify 4 [i1,i2,i4,w17,w67,w72] [] (by decide +kernel)
def n5_3 := certify 4 [i1,i2,w21,w20,w17,w57] [] (by decide +kernel)
def n5_4 := certify 4 [i1,i2,w21,w20,w37,w62] [] (by decide +kernel)
def n5_5 := certify 4 [i1,i2,w21,w78,w17,i7] [] (by decide +kernel)
def n5_6 := certify 4 [i1,i2,w77,w20,w17,i7] [] (by decide +kernel)
def n5_7 := certify 4 [i1,i4,w21,w20,w17,w52] [] (by decide +kernel)
def n5_8 := certify 4 [i1,i4,w21,w20,w76,i7] [] (by decide +kernel)
def n5_9 := certify 4 [i1,i4,w21,w17,w32,w67] [] (by decide +kernel)
def n5_10 := certify 4 [i1,i4,w75,w20,w17,i7] [] (by decide +kernel)
def n5_11 := certify 4 [i1,w21,w20,w17,w32,w37] [] (by decide +kernel)
def n5_12 := certify 4 [i1,w68,w69,w20,w17,i7] [] (by decide +kernel)
def n5_13 := certify 4 [i2,i4,w21,w20,w17,w47] [] (by decide +kernel)
def n5_14 := certify 4 [i2,i4,w21,w20,w74,i7] [] (by decide +kernel)
def n5_15 := certify 4 [i2,i4,w21,w73,w17,i7] [] (by decide +kernel)
def n5_16 := certify 4 [i2,i4,w20,w17,w28,w72] [] (by decide +kernel)
def n5_17 := certify 4 [i2,w21,w20,w17,w28,w37] [] (by decide +kernel)
def n5_18 := certify 4 [i2,w21,w63,w64,w17,i7] [] (by decide +kernel)
def n5_19 := certify 4 [i4,w21,w20,w17,w28,w32] [] (by decide +kernel)
def n5_20 := certify 4 [i4,w21,w20,w58,w59,i7] [] (by decide +kernel)
def n4_0 := certify 5 [w27,i2,i4,w21,w20,w17,i7] [n5_13,n5_14,n5_15] (by decide +kernel)
def n4_1 := certify 5 [i1,w31,i4,w21,w20,w17,i7] [n5_7,n5_8,n5_10] (by decide +kernel)
def n4_2 := certify 5 [i1,i2,i3,i4,w21,w67,w42] [n5_0] (by decide +kernel)
def n4_3 := certify 5 [i1,i2,i3,i4,w20,w42,w72] [n5_1] (by decide +kernel)
def n4_4 := certify 5 [i1,i2,i3,i4,i10,w67,w72] [n5_2] (by decide +kernel)
def n4_5 := certify 5 [i1,i2,i3,w21,w20,i10,w57] [n5_3] (by decide +kernel)
def n4_6 := certify 5 [i1,i2,i3,w21,w20,w37,w42] [n5_4] (by decide +kernel)
def n4_7 := certify 5 [i1,i2,i3,w21,w78,i10,i7] [n5_5] (by decide +kernel)
def n4_8 := certify 5 [i1,i2,i3,w77,w20,i10,i7] [n5_6] (by decide +kernel)
def n4_9 := certify 5 [i1,i2,w36,w21,w20,w17,i7] [n5_3,n5_5,n5_6] (by decide +kernel)
def n4_10 := certify 5 [i1,i2,i4,i5,w21,w41,w62] [n5_0] (by decide +kernel)
def n4_11 := certify 5 [i1,i2,i4,i5,i9,w62,w72] [n5_1] (by decide +kernel)
def n4_12 := certify 5 [i1,i2,i4,i5,w17,w41,w72] [n5_2] (by decide +kernel)
def n4_13 := certify 5 [i1,i2,i4,i6,i8,w67,w62] [n5_0] (by decide +kernel)
def n4_14 := certify 5 [i1,i2,i4,i6,w20,w40,w62] [n5_1] (by decide +kernel)
def n4_15 := certify 5 [i1,i2,i4,i6,w17,w40,w67] [n5_2] (by decide +kernel)
def n4_16 := certify 5 [i1,i2,i4,i8,w20,w62,w39] [n5_1] (by decide +kernel)
def n4_17 := certify 5 [i1,i2,i4,i8,w17,w67,w39] [n5_2] (by decide +kernel)
def n4_18 := certify 5 [i1,i2,i4,w21,i9,w38,w62] [n5_0] (by decide +kernel)
def n4_19 := certify 5 [i1,i2,i4,w21,w20,w17,i7] [] (by decide +kernel)
def n4_20 := certify 5 [i1,i2,i4,w21,w20,i7,w62] [n5_0,n5_1,n5_4] (by decide +kernel)
def n4_21 := certify 5 [i1,i2,i4,w21,i10,w33,w67] [n5_0] (by decide +kernel)
def n4_22 := certify 5 [i1,i2,i4,w21,w17,i7,w67] [n5_0,n5_2,n5_9] (by decide +kernel)
def n4_23 := certify 5 [i1,i2,i4,i9,w17,w38,w72] [n5_2] (by decide +kernel)
def n4_24 := certify 5 [i1,i2,i4,w20,i10,w33,w72] [n5_1] (by decide +kernel)
def n4_25 := certify 5 [i1,i2,i4,w20,w17,i7,w72] [n5_1,n5_2,n5_16] (by decide +kernel)
def n4_26 := certify 5 [i1,i2,i5,i6,i8,w66,w62] [] (by decide +kernel)
def n4_27 := certify 5 [i1,i2,i5,i6,w18,w41,w62] [] (by decide +kernel)
def n4_28 := certify 5 [i1,i2,i5,i6,i9,w71,w62] [] (by decide +kernel)
def n4_29 := certify 5 [i1,i2,i5,i6,w19,w40,w62] [] (by decide +kernel)
def n4_30 := certify 5 [i1,i2,i5,i8,w19,w62,w39] [] (by decide +kernel)
def n4_31 := certify 5 [i1,i2,i5,i8,w17,w66,w39] [] (by decide +kernel)
def n4_32 := certify 5 [i1,i2,i5,w18,i9,w62,w39] [] (by decide +kernel)
def n4_33 := certify 5 [i1,i2,i5,w18,w17,w41,w39] [] (by decide +kernel)
def n4_34 := certify 5 [i1,i2,i5,w21,i9,w17,w57] [n5_3] (by decide +kernel)
def n4_35 := certify 5 [i1,i2,i5,w21,i9,w37,w62] [n5_4] (by decide +kernel)
def n4_36 := certify 5 [i1,i2,i5,w21,w56,w17,i7] [n5_5] (by decide +kernel)
def n4_37 := certify 5 [i1,i2,i5,w77,i9,w17,i7] [n5_6] (by decide +kernel)
def n4_38 := certify 5 [i1,i2,w53,w21,i9,w17,i7] [n5_5] (by decide +kernel)
def n4_39 := certify 5 [i1,i2,w34,w21,w20,w17,i7] [] (by decide +kernel)
def n4_40 := certify 5 [i1,i2,i6,i8,w19,w38,w62] [] (by decide +kernel)
def n4_41 := certify 5 [i1,i2,i6,i8,w20,w17,w57] [n5_3] (by decide +kernel)
def n4_42 := certify 5 [i1,i2,i6,i8,w20,w37,w62] [n5_4] (by decide +kernel)
def n4_43 := certify 5 [i1,i2,i6,i8,w78,w17,i7] [n5_5] (by decide +kernel)
def n4_44 := certify 5 [i1,i2,i6,w55,w20,w17,i7] [n5_6] (by decide +kernel)
def n4_45 := certify 5 [i1,i2,i6,w18,i9,w38,w62] [] (by decide +kernel)
def n4_46 := certify 5 [i1,i2,i6,i9,w17,w38,w71] [] (by decide +kernel)
def n4_47 := certify 5 [i1,i2,i6,w19,w17,w38,w40] [] (by decide +kernel)
def n4_48 := certify 5 [i1,i2,w54,i8,w20,w17,i7] [n5_6] (by decide +kernel)
def n4_49 := certify 5 [i1,i2,w35,w21,w20,w17,i7] [] (by decide +kernel)
def n4_50 := certify 5 [i1,i2,i8,w19,w17,w38,w39] [] (by decide +kernel)
def n4_51 := certify 5 [i1,i2,i8,w20,w17,w37,w39] [] (by decide +kernel)
def n4_52 := certify 5 [i1,i2,w18,w21,w20,w17,i7] [] (by decide +kernel)
def n4_53 := certify 5 [i1,i2,w18,i9,w17,w38,w39] [] (by decide +kernel)
def n4_54 := certify 5 [i1,i2,w21,w69,w20,w17,i7] [n5_12] (by decide +kernel)
def n4_55 := certify 5 [i1,i2,w21,i9,w17,w37,w38] [] (by decide +kernel)
def n4_56 := certify 5 [i1,i2,w21,w19,w20,w17,i7] [] (by decide +kernel)
def n4_57 := certify 5 [i1,i2,w21,w20,w64,w17,i7] [n5_18] (by decide +kernel)
def n4_58 := certify 5 [i1,i2,w21,w20,i10,w33,w37] [n5_4] (by decide +kernel)
def n4_59 := certify 5 [i1,i2,w21,w20,w17,i7,w37] [n5_4,n5_11,n5_17] (by decide +kernel)
def n4_60 := certify 5 [i1,i3,i4,i6,i8,w67,w61] [] (by decide +kernel)
def n4_61 := certify 5 [i1,i3,i4,i6,w15,w67,w42] [] (by decide +kernel)
def n4_62 := certify 5 [i1,i3,i4,i6,i10,w70,w67] [] (by decide +kernel)
def n4_63 := certify 5 [i1,i3,i4,i6,w16,w40,w67] [] (by decide +kernel)
def n4_64 := certify 5 [i1,i3,i4,i8,w20,w61,w39] [] (by decide +kernel)
def n4_65 := certify 5 [i1,i3,i4,i8,w16,w67,w39] [] (by decide +kernel)
def n4_66 := certify 5 [i1,i3,i4,w15,w20,w42,w39] [] (by decide +kernel)
def n4_67 := certify 5 [i1,i3,i4,w15,i10,w67,w39] [] (by decide +kernel)
def n4_68 := certify 5 [i1,i3,i4,w21,w20,i10,w52] [n5_7] (by decide +kernel)
def n4_69 := certify 5 [i1,i3,i4,w21,w20,w51,i7] [n5_8] (by decide +kernel)
def n4_70 := certify 5 [i1,i3,i4,w21,i10,w32,w67] [n5_9] (by decide +kernel)
def n4_71 := certify 5 [i1,i3,i4,w75,w20,i10,i7] [n5_10] (by decide +kernel)
def n4_72 := certify 5 [i1,i3,i5,i6,i8,w66,w61] [] (by decide +kernel)
def n4_73 := certify 5 [i1,i3,i5,i8,w19,w61,w39] [] (by decide +kernel)
def n4_74 := certify 5 [i1,i3,i5,i8,w16,w66,w39] [] (by decide +kernel)
def n4_75 := certify 5 [i1,i3,i6,i8,w19,w38,w61] [] (by decide +kernel)
def n4_76 := certify 5 [i1,i3,i6,i8,w20,w16,w57] [] (by decide +kernel)
def n4_77 := certify 5 [i1,i3,i6,i8,w20,w37,w61] [] (by decide +kernel)
def n4_78 := certify 5 [i1,i3,i6,i8,w78,w16,i7] [] (by decide +kernel)
def n4_79 := certify 5 [i1,i3,i6,w15,w20,i10,w57] [] (by decide +kernel)
def n4_80 := certify 5 [i1,i3,i6,w15,w20,w37,w42] [] (by decide +kernel)
def n4_81 := certify 5 [i1,i3,i6,w15,w78,i10,i7] [] (by decide +kernel)
def n4_82 := certify 5 [i1,i3,i6,w19,w16,w38,w40] [] (by decide +kernel)
def n4_83 := certify 5 [i1,i3,w54,i8,w20,w16,i7] [] (by decide +kernel)
def n4_84 := certify 5 [i1,i3,w54,w15,w20,i10,i7] [] (by decide +kernel)
def n4_85 := certify 5 [i1,i3,w35,w21,w20,w16,i7] [] (by decide +kernel)
def n4_86 := certify 5 [i1,i3,w35,w68,w20,i10,i7] [] (by decide +kernel)
def n4_87 := certify 5 [i1,i3,i8,w19,w16,w38,w39] [] (by decide +kernel)
def n4_88 := certify 5 [i1,i3,i8,w20,w16,w37,w39] [] (by decide +kernel)
def n4_89 := certify 5 [i1,i3,w15,w20,i10,w37,w39] [] (by decide +kernel)
def n4_90 := certify 5 [i1,i3,w21,w20,i10,w32,w37] [n5_11] (by decide +kernel)
def n4_91 := certify 5 [i1,i3,w68,w69,w20,i10,i7] [n5_12] (by decide +kernel)
def n4_92 := certify 5 [i1,w48,i4,w21,w20,i10,i7] [n5_8] (by decide +kernel)
def n4_93 := certify 5 [i1,w29,i4,w21,w20,w17,i7] [] (by decide +kernel)
def n4_94 := certify 5 [i1,i4,i5,w21,i9,w17,w52] [n5_7] (by decide +kernel)
def n4_95 := certify 5 [i1,i4,i5,w21,i9,w76,i7] [n5_8] (by decide +kernel)
def n4_96 := certify 5 [i1,i4,i5,w21,w17,w32,w41] [n5_9] (by decide +kernel)
def n4_97 := certify 5 [i1,i4,i5,w75,i9,w17,i7] [n5_10] (by decide +kernel)
def n4_98 := certify 5 [i1,i4,i6,i8,w20,w17,w52] [n5_7] (by decide +kernel)
def n4_99 := certify 5 [i1,i4,i6,i8,w20,w76,i7] [n5_8] (by decide +kernel)
def n4_100 := certify 5 [i1,i4,i6,i8,w16,w33,w67] [] (by decide +kernel)
def n4_101 := certify 5 [i1,i4,i6,i8,w17,w32,w67] [n5_9] (by decide +kernel)
def n4_102 := certify 5 [i1,i4,i6,w50,w20,w17,i7] [n5_10] (by decide +kernel)
def n4_103 := certify 5 [i1,i4,i6,w15,i10,w33,w67] [] (by decide +kernel)
def n4_104 := certify 5 [i1,i4,i6,w20,i10,w33,w70] [] (by decide +kernel)
def n4_105 := certify 5 [i1,i4,i6,w20,w16,w33,w40] [] (by decide +kernel)
def n4_106 := certify 5 [i1,i4,w49,i8,w20,w17,i7] [n5_10] (by decide +kernel)
def n4_107 := certify 5 [i1,i4,w30,w21,w20,w17,i7] [] (by decide +kernel)
def n4_108 := certify 5 [i1,i4,i8,w20,w16,w33,w39] [] (by decide +kernel)
def n4_109 := certify 5 [i1,i4,i8,w20,w17,w32,w39] [] (by decide +kernel)
def n4_110 := certify 5 [i1,i4,w15,w21,w20,w17,i7] [] (by decide +kernel)
def n4_111 := certify 5 [i1,i4,w15,w20,i10,w33,w39] [] (by decide +kernel)
def n4_112 := certify 5 [i1,i4,w21,w68,w20,w17,i7] [n5_12] (by decide +kernel)
def n4_113 := certify 5 [i1,i4,w21,i9,w17,w32,w38] [n5_9] (by decide +kernel)
def n4_114 := certify 5 [i1,i4,w21,w20,i10,w32,w33] [] (by decide +kernel)
def n4_115 := certify 5 [i1,i4,w21,w20,w16,w17,i7] [] (by decide +kernel)
def n4_116 := certify 5 [i1,i4,w21,w20,w17,w59,i7] [n5_20] (by decide +kernel)
def n4_117 := certify 5 [i1,i4,w21,w20,w17,i7,w32] [n5_9,n5_11,n5_19] (by decide +kernel)
def n4_118 := certify 5 [i1,i5,i6,i8,w19,w17,w52] [] (by decide +kernel)
def n4_119 := certify 5 [i1,i5,i6,i8,w19,w76,i7] [] (by decide +kernel)
def n4_120 := certify 5 [i1,i5,i6,i8,w16,w33,w66] [] (by decide +kernel)
def n4_121 := certify 5 [i1,i5,i6,i8,w17,w32,w66] [] (by decide +kernel)
def n4_122 := certify 5 [i1,i5,i6,w18,i9,w17,w52] [] (by decide +kernel)
def n4_123 := certify 5 [i1,i5,i6,w18,i9,w76,i7] [] (by decide +kernel)
def n4_124 := certify 5 [i1,i5,i6,w18,w17,w32,w41] [] (by decide +kernel)
def n4_125 := certify 5 [i1,i5,i6,w19,w16,w33,w40] [] (by decide +kernel)
def n4_126 := certify 5 [i1,i5,w49,i8,w19,w17,i7] [] (by decide +kernel)
def n4_127 := certify 5 [i1,i5,w49,w18,i9,w17,i7] [] (by decide +kernel)
def n4_128 := certify 5 [i1,i5,w30,w21,w19,w17,i7] [] (by decide +kernel)
def n4_129 := certify 5 [i1,i5,w30,w69,i9,w17,i7] [] (by decide +kernel)
def n4_130 := certify 5 [i1,i5,i8,w19,w16,w33,w39] [] (by decide +kernel)
def n4_131 := certify 5 [i1,i5,i8,w19,w17,w32,w39] [] (by decide +kernel)
def n4_132 := certify 5 [i1,i5,w18,i9,w17,w32,w39] [] (by decide +kernel)
def n4_133 := certify 5 [i1,i5,w21,i9,w17,w32,w37] [n5_11] (by decide +kernel)
def n4_134 := certify 5 [i1,i5,w68,w69,i9,w17,i7] [n5_12] (by decide +kernel)
def n4_135 := certify 5 [i1,i6,i8,w19,w16,w33,w38] [] (by decide +kernel)
def n4_136 := certify 5 [i1,i6,i8,w19,w17,w32,w38] [] (by decide +kernel)
def n4_137 := certify 5 [i1,i6,i8,w20,w16,w33,w37] [] (by decide +kernel)
def n4_138 := certify 5 [i1,i6,i8,w20,w17,w32,w37] [n5_11] (by decide +kernel)
def n4_139 := certify 5 [i1,i6,w15,w18,w20,w17,i7] [] (by decide +kernel)
def n4_140 := certify 5 [i1,i6,w15,w20,i10,w33,w37] [] (by decide +kernel)
def n4_141 := certify 5 [i1,i6,w18,i9,w17,w32,w38] [] (by decide +kernel)
def n4_142 := certify 5 [i1,w30,w35,i8,w20,w17,i7] [] (by decide +kernel)
def n4_143 := certify 5 [i2,i3,i4,i5,i9,w60,w72] [] (by decide +kernel)
def n4_144 := certify 5 [i2,i3,i4,i5,w13,w42,w72] [] (by decide +kernel)
def n4_145 := certify 5 [i2,i3,i4,i5,i10,w65,w72] [] (by decide +kernel)
def n4_146 := certify 5 [i2,i3,i4,i5,w14,w41,w72] [] (by decide +kernel)
def n4_147 := certify 5 [i2,i3,i4,w21,i9,w38,w60] [] (by decide +kernel)
def n4_148 := certify 5 [i2,i3,i4,w21,w13,w38,w42] [] (by decide +kernel)
def n4_149 := certify 5 [i2,i3,i4,w21,w20,i10,w47] [n5_13] (by decide +kernel)
def n4_150 := certify 5 [i2,i3,i4,w21,w20,w46,i7] [n5_14] (by decide +kernel)
def n4_151 := certify 5 [i2,i3,i4,w21,w73,i10,i7] [n5_15] (by decide +kernel)
def n4_152 := certify 5 [i2,i3,i4,i9,w14,w38,w72] [] (by decide +kernel)
def n4_153 := certify 5 [i2,i3,i4,w13,i10,w38,w72] [] (by decide +kernel)
def n4_154 := certify 5 [i2,i3,i4,w20,i10,w28,w72] [n5_16] (by decide +kernel)
def n4_155 := certify 5 [i2,i3,i5,i6,i9,w71,w60] [] (by decide +kernel)
def n4_156 := certify 5 [i2,i3,i5,w18,i9,w60,w39] [] (by decide +kernel)
def n4_157 := certify 5 [i2,i3,i5,w18,w14,w41,w39] [] (by decide +kernel)
def n4_158 := certify 5 [i2,i3,i5,w21,i9,w14,w57] [] (by decide +kernel)
def n4_159 := certify 5 [i2,i3,i5,w21,i9,w37,w60] [] (by decide +kernel)
def n4_160 := certify 5 [i2,i3,i5,w21,w13,i10,w57] [] (by decide +kernel)
def n4_161 := certify 5 [i2,i3,i5,w21,w13,w37,w42] [] (by decide +kernel)
def n4_162 := certify 5 [i2,i3,i5,w77,i9,w14,i7] [] (by decide +kernel)
def n4_163 := certify 5 [i2,i3,i5,w77,w13,i10,i7] [] (by decide +kernel)
def n4_164 := certify 5 [i2,i3,w53,w21,i9,w14,i7] [] (by decide +kernel)
def n4_165 := certify 5 [i2,i3,w53,w21,w13,i10,i7] [] (by decide +kernel)
def n4_166 := certify 5 [i2,i3,w34,w21,w20,w14,i7] [] (by decide +kernel)
def n4_167 := certify 5 [i2,i3,w34,w21,w63,i10,i7] [] (by decide +kernel)
def n4_168 := certify 5 [i2,i3,i6,w18,i9,w38,w60] [] (by decide +kernel)
def n4_169 := certify 5 [i2,i3,i6,i9,w14,w38,w71] [] (by decide +kernel)
def n4_170 := certify 5 [i2,i3,w18,i9,w14,w38,w39] [] (by decide +kernel)
def n4_171 := certify 5 [i2,i3,w21,i9,w14,w37,w38] [] (by decide +kernel)
def n4_172 := certify 5 [i2,i3,w21,w13,i10,w37,w38] [] (by decide +kernel)
def n4_173 := certify 5 [i2,i3,w21,w20,i10,w28,w37] [n5_17] (by decide +kernel)
def n4_174 := certify 5 [i2,i3,w21,w63,w64,i10,i7] [n5_18] (by decide +kernel)
def n4_175 := certify 5 [i2,w43,i4,w21,w20,i10,i7] [n5_14] (by decide +kernel)
def n4_176 := certify 5 [i2,w25,i4,w21,w20,w17,i7] [] (by decide +kernel)
def n4_177 := certify 5 [i2,i4,i5,w21,i9,w17,w47] [n5_13] (by decide +kernel)
def n4_178 := certify 5 [i2,i4,i5,w21,i9,w74,i7] [n5_14] (by decide +kernel)
def n4_179 := certify 5 [i2,i4,i5,w21,w45,w17,i7] [n5_15] (by decide +kernel)
def n4_180 := certify 5 [i2,i4,i5,w21,i10,w33,w65] [] (by decide +kernel)
def n4_181 := certify 5 [i2,i4,i5,w21,w14,w33,w41] [] (by decide +kernel)
def n4_182 := certify 5 [i2,i4,i5,i9,w14,w33,w72] [] (by decide +kernel)
def n4_183 := certify 5 [i2,i4,i5,i9,w17,w28,w72] [n5_16] (by decide +kernel)
def n4_184 := certify 5 [i2,i4,i5,w13,i10,w33,w72] [] (by decide +kernel)
def n4_185 := certify 5 [i2,i4,w44,w21,i9,w17,i7] [n5_15] (by decide +kernel)
def n4_186 := certify 5 [i2,i4,w26,w21,w20,w17,i7] [] (by decide +kernel)
def n4_187 := certify 5 [i2,i4,i6,i8,w20,w17,w47] [n5_13] (by decide +kernel)
def n4_188 := certify 5 [i2,i4,i6,i8,w20,w74,i7] [n5_14] (by decide +kernel)
def n4_189 := certify 5 [i2,i4,i6,i8,w73,w17,i7] [n5_15] (by decide +kernel)
def n4_190 := certify 5 [i2,i4,i6,w20,w17,w28,w40] [n5_16] (by decide +kernel)
def n4_191 := certify 5 [i2,i4,i8,w20,w17,w28,w39] [n5_16] (by decide +kernel)
def n4_192 := certify 5 [i2,i4,w21,i9,w14,w33,w38] [] (by decide +kernel)
def n4_193 := certify 5 [i2,i4,w21,i9,w17,w28,w38] [] (by decide +kernel)
def n4_194 := certify 5 [i2,i4,w21,w13,w20,w17,i7] [] (by decide +kernel)
def n4_195 := certify 5 [i2,i4,w21,w13,i10,w33,w38] [] (by decide +kernel)
def n4_196 := certify 5 [i2,i4,w21,w20,w63,w17,i7] [n5_18] (by decide +kernel)
def n4_197 := certify 5 [i2,i4,w21,w20,i10,w28,w33] [] (by decide +kernel)
def n4_198 := certify 5 [i2,i4,w21,w20,w14,w17,i7] [] (by decide +kernel)
def n4_199 := certify 5 [i2,i4,w21,w20,w17,w58,i7] [n5_20] (by decide +kernel)
def n4_200 := certify 5 [i2,i4,w21,w20,w17,i7,w28] [n5_16,n5_17,n5_19] (by decide +kernel)
def n4_201 := certify 5 [i2,i5,i6,i8,w19,w17,w47] [] (by decide +kernel)
def n4_202 := certify 5 [i2,i5,i6,i8,w19,w74,i7] [] (by decide +kernel)
def n4_203 := certify 5 [i2,i5,i6,w18,i9,w17,w47] [] (by decide +kernel)
def n4_204 := certify 5 [i2,i5,i6,w18,i9,w74,i7] [] (by decide +kernel)
def n4_205 := certify 5 [i2,i5,i6,w18,w14,w33,w41] [] (by decide +kernel)
def n4_206 := certify 5 [i2,i5,i6,i9,w14,w33,w71] [] (by decide +kernel)
def n4_207 := certify 5 [i2,i5,i6,i9,w17,w28,w71] [] (by decide +kernel)
def n4_208 := certify 5 [i2,i5,i6,w19,w17,w28,w40] [] (by decide +kernel)
def n4_209 := certify 5 [i2,i5,i8,w19,w17,w28,w39] [] (by decide +kernel)
def n4_210 := certify 5 [i2,i5,w18,i9,w14,w33,w39] [] (by decide +kernel)
def n4_211 := certify 5 [i2,i5,w18,i9,w17,w28,w39] [] (by decide +kernel)
def n4_212 := certify 5 [i2,i5,w21,i9,w14,w33,w37] [] (by decide +kernel)
def n4_213 := certify 5 [i2,i5,w21,i9,w17,w28,w37] [n5_17] (by decide +kernel)
def n4_214 := certify 5 [i2,i5,w21,w13,w19,w17,i7] [] (by decide +kernel)
def n4_215 := certify 5 [i2,i5,w21,w13,i10,w33,w37] [] (by decide +kernel)
def n4_216 := certify 5 [i2,w44,i6,i8,w19,w17,i7] [] (by decide +kernel)
def n4_217 := certify 5 [i2,w44,i6,w18,i9,w17,i7] [] (by decide +kernel)
def n4_218 := certify 5 [i2,w26,w34,w21,i9,w17,i7] [] (by decide +kernel)
def n4_219 := certify 5 [i2,w26,i6,i8,w64,w17,i7] [] (by decide +kernel)
def n4_220 := certify 5 [i2,w26,i6,w18,w20,w17,i7] [] (by decide +kernel)
def n4_221 := certify 5 [i2,i6,i8,w19,w17,w28,w38] [] (by decide +kernel)
def n4_222 := certify 5 [i2,i6,i8,w20,w17,w28,w37] [n5_17] (by decide +kernel)
def n4_223 := certify 5 [i2,i6,i8,w63,w64,w17,i7] [n5_18] (by decide +kernel)
def n4_224 := certify 5 [i2,i6,w18,i9,w14,w33,w38] [] (by decide +kernel)
def n4_225 := certify 5 [i2,i6,w18,i9,w17,w28,w38] [] (by decide +kernel)
def n4_226 := certify 5 [i3,i4,i5,i6,i10,w70,w65] [] (by decide +kernel)
def n4_227 := certify 5 [i3,i4,i5,w15,w13,w42,w39] [] (by decide +kernel)
def n4_228 := certify 5 [i3,i4,i5,w15,i10,w65,w39] [] (by decide +kernel)
def n4_229 := certify 5 [i3,i4,i5,w21,i9,w14,w52] [] (by decide +kernel)
def n4_230 := certify 5 [i3,i4,i5,w21,w13,i10,w52] [] (by decide +kernel)
def n4_231 := certify 5 [i3,i4,i5,w21,i10,w32,w65] [] (by decide +kernel)
def n4_232 := certify 5 [i3,i4,i5,w21,w14,w32,w41] [] (by decide +kernel)
def n4_233 := certify 5 [i3,i4,i5,w75,i9,w14,i7] [] (by decide +kernel)
def n4_234 := certify 5 [i3,i4,i5,w75,w13,i10,i7] [] (by decide +kernel)
def n4_235 := certify 5 [i3,i4,i6,i8,w20,w16,w47] [] (by decide +kernel)
def n4_236 := certify 5 [i3,i4,i6,i8,w73,w16,i7] [] (by decide +kernel)
def n4_237 := certify 5 [i3,i4,i6,w15,w13,w38,w42] [] (by decide +kernel)
def n4_238 := certify 5 [i3,i4,i6,w15,w20,i10,w47] [] (by decide +kernel)
def n4_239 := certify 5 [i3,i4,i6,w15,w73,i10,i7] [] (by decide +kernel)
def n4_240 := certify 5 [i3,i4,i6,w13,i10,w38,w70] [] (by decide +kernel)
def n4_241 := certify 5 [i3,i4,i6,w20,i10,w28,w70] [] (by decide +kernel)
def n4_242 := certify 5 [i3,i4,i6,w20,w16,w28,w40] [] (by decide +kernel)
def n4_243 := certify 5 [i3,i4,i8,w20,w16,w28,w39] [] (by decide +kernel)
def n4_244 := certify 5 [i3,i4,w15,w13,i10,w38,w39] [] (by decide +kernel)
def n4_245 := certify 5 [i3,i4,w15,w20,i10,w28,w39] [] (by decide +kernel)
def n4_246 := certify 5 [i3,i4,w21,i9,w14,w32,w38] [] (by decide +kernel)
def n4_247 := certify 5 [i3,i4,w21,w13,i10,w32,w38] [] (by decide +kernel)
def n4_248 := certify 5 [i3,i4,w21,w20,i10,w28,w32] [n5_19] (by decide +kernel)
def n4_249 := certify 5 [i3,i4,w21,w20,w14,w16,i7] [] (by decide +kernel)
def n4_250 := certify 5 [i3,i5,i6,i8,w19,w16,w47] [] (by decide +kernel)
def n4_251 := certify 5 [i3,i5,i6,w15,w13,i10,w57] [] (by decide +kernel)
def n4_252 := certify 5 [i3,i5,i6,w15,w13,w37,w42] [] (by decide +kernel)
def n4_253 := certify 5 [i3,i5,i6,w18,i9,w14,w52] [] (by decide +kernel)
def n4_254 := certify 5 [i3,i5,i6,w18,w14,w32,w41] [] (by decide +kernel)
def n4_255 := certify 5 [i3,i5,i6,w19,w16,w28,w40] [] (by decide +kernel)
def n4_256 := certify 5 [i3,i5,w49,w18,i9,w14,i7] [] (by decide +kernel)
def n4_257 := certify 5 [i3,i5,w30,w69,i9,w14,i7] [] (by decide +kernel)
def n4_258 := certify 5 [i3,i5,w54,w15,w13,i10,i7] [] (by decide +kernel)
def n4_259 := certify 5 [i3,i5,w35,w68,w13,i10,i7] [] (by decide +kernel)
def n4_260 := certify 5 [i3,i5,i8,w19,w16,w28,w39] [] (by decide +kernel)
def n4_261 := certify 5 [i3,i5,w15,w13,i10,w37,w39] [] (by decide +kernel)
def n4_262 := certify 5 [i3,i5,w18,i9,w14,w32,w39] [] (by decide +kernel)
def n4_263 := certify 5 [i3,i5,w21,i9,w14,w32,w37] [] (by decide +kernel)
def n4_264 := certify 5 [i3,i5,w21,w13,i10,w32,w37] [] (by decide +kernel)
def n4_265 := certify 5 [i3,i5,w68,w69,i9,w14,i7] [] (by decide +kernel)
def n4_266 := certify 5 [i3,i5,w68,w69,w13,i10,i7] [] (by decide +kernel)
def n4_267 := certify 5 [i3,w44,i6,i8,w19,w16,i7] [] (by decide +kernel)
def n4_268 := certify 5 [i3,w26,i6,i8,w64,w16,i7] [] (by decide +kernel)
def n4_269 := certify 5 [i3,w53,i6,w15,w13,i10,i7] [] (by decide +kernel)
def n4_270 := certify 5 [i3,w34,i6,w15,w63,i10,i7] [] (by decide +kernel)
def n4_271 := certify 5 [i3,i6,i8,w19,w16,w28,w38] [] (by decide +kernel)
def n4_272 := certify 5 [i3,i6,i8,w20,w16,w28,w37] [] (by decide +kernel)
def n4_273 := certify 5 [i3,i6,i8,w63,w64,w16,i7] [] (by decide +kernel)
def n4_274 := certify 5 [i3,i6,w15,w13,i10,w37,w38] [] (by decide +kernel)
def n4_275 := certify 5 [i3,i6,w15,w20,i10,w28,w37] [] (by decide +kernel)
def n4_276 := certify 5 [i3,i6,w15,w63,w64,i10,i7] [] (by decide +kernel)
def n4_277 := certify 5 [i3,i6,w18,i9,w14,w32,w38] [] (by decide +kernel)
def n4_278 := certify 5 [w43,i4,i6,i8,w20,w16,i7] [] (by decide +kernel)
def n4_279 := certify 5 [w43,i4,i6,w15,w20,i10,i7] [] (by decide +kernel)
def n4_280 := certify 5 [w43,i5,i6,i8,w19,w16,i7] [] (by decide +kernel)
def n4_281 := certify 5 [w25,w29,i4,w21,w20,i10,i7] [] (by decide +kernel)
def n4_282 := certify 5 [w25,i4,i6,i8,w20,w59,i7] [] (by decide +kernel)
def n4_283 := certify 5 [w25,i4,i6,w15,w20,w17,i7] [] (by decide +kernel)
def n4_284 := certify 5 [w25,i5,i6,i8,w19,w59,i7] [] (by decide +kernel)
def n4_285 := certify 5 [w48,i4,i5,w21,i9,w14,i7] [] (by decide +kernel)
def n4_286 := certify 5 [w48,i4,i5,w21,w13,i10,i7] [] (by decide +kernel)
def n4_287 := certify 5 [w48,i5,i6,w18,i9,w14,i7] [] (by decide +kernel)
def n4_288 := certify 5 [w29,i4,i5,w21,i9,w58,i7] [] (by decide +kernel)
def n4_289 := certify 5 [w29,i4,i5,w21,w13,w17,i7] [] (by decide +kernel)
def n4_290 := certify 5 [w29,i5,i6,w18,i9,w58,i7] [] (by decide +kernel)
def n4_291 := certify 5 [i4,i5,i6,w15,i10,w33,w65] [] (by decide +kernel)
def n4_292 := certify 5 [i4,i5,i6,w13,i10,w33,w70] [] (by decide +kernel)
def n4_293 := certify 5 [i4,i5,w15,w13,i10,w33,w39] [] (by decide +kernel)
def n4_294 := certify 5 [i4,i5,w21,i9,w14,w32,w33] [] (by decide +kernel)
def n4_295 := certify 5 [i4,i5,w21,i9,w17,w28,w32] [n5_19] (by decide +kernel)
def n4_296 := certify 5 [i4,i5,w21,i9,w58,w59,i7] [n5_20] (by decide +kernel)
def n4_297 := certify 5 [i4,i5,w21,w13,i10,w32,w33] [] (by decide +kernel)
def n4_298 := certify 5 [i4,i6,i8,w20,w16,w28,w33] [] (by decide +kernel)
def n4_299 := certify 5 [i4,i6,i8,w20,w17,w28,w32] [n5_19] (by decide +kernel)
def n4_300 := certify 5 [i4,i6,i8,w20,w58,w59,i7] [n5_20] (by decide +kernel)
def n4_301 := certify 5 [i4,i6,w15,w13,i10,w33,w38] [] (by decide +kernel)
def n4_302 := certify 5 [i4,i6,w15,w20,i10,w28,w33] [] (by decide +kernel)
def n4_303 := certify 5 [i5,i6,i8,w19,w16,w28,w33] [] (by decide +kernel)
def n4_304 := certify 5 [i5,i6,i8,w19,w17,w28,w32] [] (by decide +kernel)
def n4_305 := certify 5 [i5,i6,i8,w19,w58,w59,i7] [] (by decide +kernel)
def n4_306 := certify 5 [i5,i6,w15,w13,i10,w33,w37] [] (by decide +kernel)
def n4_307 := certify 5 [i5,i6,w18,i9,w14,w32,w33] [] (by decide +kernel)
def n4_308 := certify 5 [i5,i6,w18,i9,w17,w28,w32] [] (by decide +kernel)
def n4_309 := certify 5 [i5,i6,w18,i9,w58,w59,i7] [] (by decide +kernel)
def n3_0 := certify 6 [iZero,i1,i2,i4,w21,w20,w17,i7] [n4_19] (by decide +kernel)
def n3_1 := certify 6 [i0,i1,i2,i4,w21,w20,w17,i7] [] (by decide +kernel)
def n3_2 := certify 6 [w27,i2,i3,i4,w21,w20,i10,i7] [n4_0,n4_149,n4_150,n4_151,n4_175] (by decide +kernel)
def n3_3 := certify 6 [w27,i2,i4,i5,w21,i9,w17,i7] [n4_0,n4_177,n4_178,n4_179,n4_185] (by decide +kernel)
def n3_4 := certify 6 [w27,i2,i4,i6,i8,w20,w17,i7] [n4_0,n4_187,n4_188,n4_189] (by decide +kernel)
def n3_5 := certify 6 [w27,i2,i5,i6,i8,w19,w17,i7] [n4_201,n4_202,n4_216] (by decide +kernel)
def n3_6 := certify 6 [w27,i2,i5,i6,w18,i9,w17,i7] [n4_203,n4_204,n4_217] (by decide +kernel)
def n3_7 := certify 6 [w27,i3,i4,i6,i8,w20,w16,i7] [n4_235,n4_236,n4_278] (by decide +kernel)
def n3_8 := certify 6 [w27,i3,i4,i6,w15,w20,i10,i7] [n4_238,n4_239,n4_279] (by decide +kernel)
def n3_9 := certify 6 [w27,i3,i5,i6,i8,w19,w16,i7] [n4_250,n4_267,n4_280] (by decide +kernel)
def n3_10 := certify 6 [i1,w31,i3,i4,w21,w20,i10,i7] [n4_1,n4_68,n4_69,n4_71,n4_92] (by decide +kernel)
def n3_11 := certify 6 [i1,w31,i4,i5,w21,i9,w17,i7] [n4_1,n4_94,n4_95,n4_97] (by decide +kernel)
def n3_12 := certify 6 [i1,w31,i4,i6,i8,w20,w17,i7] [n4_1,n4_98,n4_99,n4_102,n4_106] (by decide +kernel)
def n3_13 := certify 6 [i1,w31,i5,i6,i8,w19,w17,i7] [n4_118,n4_119,n4_126] (by decide +kernel)
def n3_14 := certify 6 [i1,w31,i5,i6,w18,i9,w17,i7] [n4_122,n4_123,n4_127] (by decide +kernel)
def n3_15 := certify 6 [i1,i2,i3,w36,w21,w20,i10,i7] [n4_5,n4_7,n4_8,n4_9] (by decide +kernel)
def n3_16 := certify 6 [i1,i2,i3,i4,i5,w21,w41,w42] [n4_2,n4_10] (by decide +kernel)
def n3_17 := certify 6 [i1,i2,i3,i4,i5,i9,w42,w72] [n4_3,n4_11,n4_143,n4_144] (by decide +kernel)
def n3_18 := certify 6 [i1,i2,i3,i4,i5,i10,w41,w72] [n4_4,n4_12,n4_145,n4_146] (by decide +kernel)
def n3_19 := certify 6 [i1,i2,i3,i4,i6,i8,w67,w42] [n4_2,n4_13,n4_60,n4_61] (by decide +kernel)
def n3_20 := certify 6 [i1,i2,i3,i4,i6,w20,w40,w42] [n4_3,n4_14] (by decide +kernel)
def n3_21 := certify 6 [i1,i2,i3,i4,i6,i10,w40,w67] [n4_4,n4_15,n4_62,n4_63] (by decide +kernel)
def n3_22 := certify 6 [i1,i2,i3,i4,i8,w20,w42,w39] [n4_3,n4_16,n4_64,n4_66] (by decide +kernel)
def n3_23 := certify 6 [i1,i2,i3,i4,i8,i10,w67,w39] [n4_4,n4_17,n4_65,n4_67] (by decide +kernel)
def n3_24 := certify 6 [i1,i2,i3,i4,w21,i9,w38,w42] [n4_2,n4_18,n4_147,n4_148] (by decide +kernel)
def n3_25 := certify 6 [i1,i2,i3,i4,w21,w20,i10,i7] [n4_19] (by decide +kernel)
def n3_26 := certify 6 [i1,i2,i3,i4,w21,w20,w17,i7] [n4_19,n4_93,n4_176] (by decide +kernel)
def n3_27 := certify 6 [i1,i2,i3,i4,w21,w20,i7,w42] [n4_2,n4_3,n4_6,n4_20] (by decide +kernel)
def n3_28 := certify 6 [i1,i2,i3,i4,w21,i10,i7,w67] [n4_2,n4_4,n4_21,n4_22,n4_70] (by decide +kernel)
def n3_29 := certify 6 [i1,i2,i3,i4,i9,i10,w38,w72] [n4_4,n4_23,n4_152,n4_153] (by decide +kernel)
def n3_30 := certify 6 [i1,i2,i3,i4,w20,i10,i7,w72] [n4_3,n4_4,n4_24,n4_25,n4_154] (by decide +kernel)
def n3_31 := certify 6 [i1,i2,i3,i5,i6,i8,w66,w42] [n4_26,n4_72] (by decide +kernel)
def n3_32 := certify 6 [i1,i2,i3,i5,i6,w18,w41,w42] [n4_27] (by decide +kernel)
def n3_33 := certify 6 [i1,i2,i3,i5,i6,i9,w71,w42] [n4_28,n4_155] (by decide +kernel)
def n3_34 := certify 6 [i1,i2,i3,i5,i6,w19,w40,w42] [n4_29] (by decide +kernel)
def n3_35 := certify 6 [i1,i2,i3,i5,i8,w19,w42,w39] [n4_30,n4_73] (by decide +kernel)
def n3_36 := certify 6 [i1,i2,i3,i5,i8,i10,w66,w39] [n4_31,n4_74] (by decide +kernel)
def n3_37 := certify 6 [i1,i2,i3,i5,w18,i9,w42,w39] [n4_32,n4_156] (by decide +kernel)
def n3_38 := certify 6 [i1,i2,i3,i5,w18,i10,w41,w39] [n4_33,n4_157] (by decide +kernel)
def n3_39 := certify 6 [i1,i2,i3,i5,w21,i9,i10,w57] [n4_5,n4_34,n4_158,n4_160] (by decide +kernel)
def n3_40 := certify 6 [i1,i2,i3,i5,w21,i9,w37,w42] [n4_6,n4_35,n4_159,n4_161] (by decide +kernel)
def n3_41 := certify 6 [i1,i2,i3,i5,w21,w56,i10,i7] [n4_7,n4_36] (by decide +kernel)
def n3_42 := certify 6 [i1,i2,i3,i5,w77,i9,i10,i7] [n4_8,n4_37,n4_162,n4_163] (by decide +kernel)
def n3_43 := certify 6 [i1,i2,i3,w53,w21,i9,i10,i7] [n4_7,n4_38,n4_164,n4_165] (by decide +kernel)
def n3_44 := certify 6 [i1,i2,i3,w34,w21,w20,i10,i7] [n4_39,n4_166,n4_167] (by decide +kernel)
def n3_45 := certify 6 [i1,i2,i3,i6,i8,w19,w38,w42] [n4_40,n4_75] (by decide +kernel)
def n3_46 := certify 6 [i1,i2,i3,i6,i8,w20,i10,w57] [n4_5,n4_41,n4_76,n4_79] (by decide +kernel)
def n3_47 := certify 6 [i1,i2,i3,i6,i8,w20,w37,w42] [n4_6,n4_42,n4_77,n4_80] (by decide +kernel)
def n3_48 := certify 6 [i1,i2,i3,i6,i8,w78,i10,i7] [n4_7,n4_43,n4_78,n4_81] (by decide +kernel)
def n3_49 := certify 6 [i1,i2,i3,i6,w55,w20,i10,i7] [n4_8,n4_44] (by decide +kernel)
def n3_50 := certify 6 [i1,i2,i3,i6,w18,i9,w38,w42] [n4_45,n4_168] (by decide +kernel)
def n3_51 := certify 6 [i1,i2,i3,i6,i9,i10,w38,w71] [n4_46,n4_169] (by decide +kernel)
def n3_52 := certify 6 [i1,i2,i3,i6,w19,i10,w38,w40] [n4_47,n4_82] (by decide +kernel)
def n3_53 := certify 6 [i1,i2,i3,w54,i8,w20,i10,i7] [n4_8,n4_48,n4_83,n4_84] (by decide +kernel)
def n3_54 := certify 6 [i1,i2,i3,w35,w21,w20,i10,i7] [n4_49,n4_85,n4_86] (by decide +kernel)
def n3_55 := certify 6 [i1,i2,i3,i8,w19,i10,w38,w39] [n4_50,n4_87] (by decide +kernel)
def n3_56 := certify 6 [i1,i2,i3,i8,w20,i10,w37,w39] [n4_51,n4_88,n4_89] (by decide +kernel)
def n3_57 := certify 6 [i1,i2,i3,w18,w21,w20,i10,i7] [n4_52] (by decide +kernel)
def n3_58 := certify 6 [i1,i2,i3,w18,i9,i10,w38,w39] [n4_53,n4_170] (by decide +kernel)
def n3_59 := certify 6 [i1,i2,i3,w21,w69,w20,i10,i7] [n4_54,n4_91] (by decide +kernel)
def n3_60 := certify 6 [i1,i2,i3,w21,i9,i10,w37,w38] [n4_55,n4_171,n4_172] (by decide +kernel)
def n3_61 := certify 6 [i1,i2,i3,w21,w19,w20,i10,i7] [n4_56] (by decide +kernel)
def n3_62 := certify 6 [i1,i2,i3,w21,w20,w64,i10,i7] [n4_57,n4_174] (by decide +kernel)
def n3_63 := certify 6 [i1,i2,i3,w21,w20,i10,i7,w37] [n4_6,n4_58,n4_59,n4_90,n4_173] (by decide +kernel)
def n3_64 := certify 6 [i1,i2,w36,i5,w21,i9,w17,i7] [n4_9,n4_34,n4_36,n4_37,n4_38] (by decide +kernel)
def n3_65 := certify 6 [i1,i2,w36,i6,i8,w20,w17,i7] [n4_9,n4_41,n4_43,n4_44,n4_48] (by decide +kernel)
def n3_66 := certify 6 [i1,i2,i4,i5,i6,i8,w41,w62] [n4_10,n4_13,n4_26,n4_27] (by decide +kernel)
def n3_67 := certify 6 [i1,i2,i4,i5,i6,i9,w40,w62] [n4_11,n4_14,n4_28,n4_29] (by decide +kernel)
def n3_68 := certify 6 [i1,i2,i4,i5,i6,w17,w40,w41] [n4_12,n4_15] (by decide +kernel)
def n3_69 := certify 6 [i1,i2,i4,i5,i8,i9,w62,w39] [n4_11,n4_16,n4_30,n4_32] (by decide +kernel)
def n3_70 := certify 6 [i1,i2,i4,i5,i8,w17,w41,w39] [n4_12,n4_17,n4_31,n4_33] (by decide +kernel)
def n3_71 := certify 6 [i1,i2,i4,i5,w21,i9,w17,i7] [n4_19] (by decide +kernel)
def n3_72 := certify 6 [i1,i2,i4,i5,w21,i9,i7,w62] [n4_10,n4_11,n4_18,n4_20,n4_35] (by decide +kernel)
def n3_73 := certify 6 [i1,i2,i4,i5,w21,w20,w17,i7] [n4_19,n4_39,n4_186] (by decide +kernel)
def n3_74 := certify 6 [i1,i2,i4,i5,w21,i10,w33,w41] [n4_10,n4_21,n4_180,n4_181] (by decide +kernel)
def n3_75 := certify 6 [i1,i2,i4,i5,w21,w17,i7,w41] [n4_10,n4_12,n4_22,n4_96] (by decide +kernel)
def n3_76 := certify 6 [i1,i2,i4,i5,i9,i10,w33,w72] [n4_11,n4_24,n4_182,n4_184] (by decide +kernel)
def n3_77 := certify 6 [i1,i2,i4,i5,i9,w17,i7,w72] [n4_11,n4_12,n4_23,n4_25,n4_183] (by decide +kernel)
def n3_78 := certify 6 [i1,i2,i4,i6,i8,i9,w38,w62] [n4_13,n4_18,n4_40,n4_45] (by decide +kernel)
def n3_79 := certify 6 [i1,i2,i4,i6,i8,w20,w17,i7] [n4_19] (by decide +kernel)
def n3_80 := certify 6 [i1,i2,i4,i6,i8,w20,i7,w62] [n4_13,n4_14,n4_16,n4_20,n4_42] (by decide +kernel)
def n3_81 := certify 6 [i1,i2,i4,i6,i8,i10,w33,w67] [n4_13,n4_21,n4_100,n4_103] (by decide +kernel)
def n3_82 := certify 6 [i1,i2,i4,i6,i8,w17,i7,w67] [n4_13,n4_15,n4_17,n4_22,n4_101] (by decide +kernel)
def n3_83 := certify 6 [i1,i2,i4,i6,w21,w20,w17,i7] [n4_19,n4_49,n4_107] (by decide +kernel)
def n3_84 := certify 6 [i1,i2,i4,i6,i9,w17,w38,w40] [n4_15,n4_23,n4_46,n4_47] (by decide +kernel)
def n3_85 := certify 6 [i1,i2,i4,i6,w20,i10,w33,w40] [n4_14,n4_24,n4_104,n4_105] (by decide +kernel)
def n3_86 := certify 6 [i1,i2,i4,i6,w20,w17,i7,w40] [n4_14,n4_15,n4_25,n4_190] (by decide +kernel)
def n3_87 := certify 6 [i1,i2,i4,i8,w21,w20,w17,i7] [n4_0,n4_19,n4_52,n4_110] (by decide +kernel)
def n3_88 := certify 6 [i1,i2,i4,i8,i9,w17,w38,w39] [n4_17,n4_23,n4_50,n4_53] (by decide +kernel)
def n3_89 := certify 6 [i1,i2,i4,i8,w20,i10,w33,w39] [n4_16,n4_24,n4_108,n4_111] (by decide +kernel)
def n3_90 := certify 6 [i1,i2,i4,i8,w20,w17,i7,w39] [n4_16,n4_17,n4_25,n4_51,n4_109,n4_191] (by decide +kernel)
def n3_91 := certify 6 [i1,i2,i4,w21,i9,w20,w17,i7] [n4_1,n4_19,n4_56,n4_194] (by decide +kernel)
def n3_92 := certify 6 [i1,i2,i4,w21,i9,i10,w33,w38] [n4_18,n4_21,n4_192,n4_195] (by decide +kernel)
def n3_93 := certify 6 [i1,i2,i4,w21,i9,w17,i7,w38] [n4_18,n4_22,n4_23,n4_55,n4_113,n4_193] (by decide +kernel)
def n3_94 := certify 6 [i1,i2,i4,w21,w20,i10,w17,i7] [n4_9,n4_19,n4_115,n4_198] (by decide +kernel)
def n3_95 := certify 6 [i1,i2,i4,w21,w20,i10,i7,w33] [n4_20,n4_21,n4_24,n4_58,n4_114,n4_197] (by decide +kernel)
def n3_96 := certify 6 [i1,i2,i4,w21,w20,w17,i7] [n4_0,n4_1,n4_9,n4_20,n4_22,n4_25,n4_54,n4_57,n4_59,n4_112,n4_116,n4_117,n4_196,n4_199,n4_200] (by decide +kernel)
def n3_97 := certify 6 [i1,i2,i4,w21,w20,w17,i7,iOnes] [n4_19] (by decide +kernel)
def n3_98 := certify 6 [i1,i2,i5,w34,w21,i9,w17,i7] [n4_39,n4_218] (by decide +kernel)
def n3_99 := certify 6 [i1,i2,i5,i6,i8,i9,w17,w57] [n4_34,n4_41] (by decide +kernel)
def n3_100 := certify 6 [i1,i2,i5,i6,i8,i9,w37,w62] [n4_26,n4_28,n4_35,n4_42] (by decide +kernel)
def n3_101 := certify 6 [i1,i2,i5,i6,i8,w56,w17,i7] [n4_36,n4_43] (by decide +kernel)
def n3_102 := certify 6 [i1,i2,i5,i6,i8,w19,w17,i7] [] (by decide +kernel)
def n3_103 := certify 6 [i1,i2,i5,i6,i8,w19,i7,w62] [n4_26,n4_29,n4_30,n4_40] (by decide +kernel)
def n3_104 := certify 6 [i1,i2,i5,i6,i8,w64,w17,i7] [n4_219] (by decide +kernel)
def n3_105 := certify 6 [i1,i2,i5,i6,i8,i10,w33,w66] [n4_26,n4_120] (by decide +kernel)
def n3_106 := certify 6 [i1,i2,i5,i6,i8,w17,i7,w66] [n4_26,n4_31,n4_121] (by decide +kernel)
def n3_107 := certify 6 [i1,i2,i5,i6,w55,i9,w17,i7] [n4_37,n4_44] (by decide +kernel)
def n3_108 := certify 6 [i1,i2,i5,i6,w18,i9,w17,i7] [] (by decide +kernel)
def n3_109 := certify 6 [i1,i2,i5,i6,w18,i9,i7,w62] [n4_27,n4_28,n4_32,n4_45] (by decide +kernel)
def n3_110 := certify 6 [i1,i2,i5,i6,w18,w19,w17,i7] [] (by decide +kernel)
def n3_111 := certify 6 [i1,i2,i5,i6,w18,w20,w17,i7] [n4_220] (by decide +kernel)
def n3_112 := certify 6 [i1,i2,i5,i6,w18,i10,w33,w41] [n4_27,n4_205] (by decide +kernel)
def n3_113 := certify 6 [i1,i2,i5,i6,w18,w17,i7,w41] [n4_27,n4_33,n4_124] (by decide +kernel)
def n3_114 := certify 6 [i1,i2,i5,i6,w21,w19,w17,i7] [n4_128] (by decide +kernel)
def n3_115 := certify 6 [i1,i2,i5,i6,w69,i9,w17,i7] [n4_129] (by decide +kernel)
def n3_116 := certify 6 [i1,i2,i5,i6,i9,i10,w33,w71] [n4_28,n4_206] (by decide +kernel)
def n3_117 := certify 6 [i1,i2,i5,i6,i9,w17,i7,w71] [n4_28,n4_46,n4_207] (by decide +kernel)
def n3_118 := certify 6 [i1,i2,i5,i6,w19,i10,w33,w40] [n4_29,n4_125] (by decide +kernel)
def n3_119 := certify 6 [i1,i2,i5,i6,w19,w17,i7,w40] [n4_29,n4_47,n4_208] (by decide +kernel)
def n3_120 := certify 6 [i1,i2,i5,w54,i8,i9,w17,i7] [n4_37,n4_48] (by decide +kernel)
def n3_121 := certify 6 [i1,i2,i5,w35,w21,i9,w17,i7] [n4_49] (by decide +kernel)
def n3_122 := certify 6 [i1,i2,i5,i8,i9,w17,w37,w39] [n4_31,n4_51] (by decide +kernel)
def n3_123 := certify 6 [i1,i2,i5,i8,w19,i10,w33,w39] [n4_30,n4_130] (by decide +kernel)
def n3_124 := certify 6 [i1,i2,i5,i8,w19,w17,i7,w39] [n4_30,n4_31,n4_50,n4_131,n4_209] (by decide +kernel)
def n3_125 := certify 6 [i1,i2,i5,w18,w21,i9,w17,i7] [n4_52] (by decide +kernel)
def n3_126 := certify 6 [i1,i2,i5,w18,i9,i10,w33,w39] [n4_32,n4_210] (by decide +kernel)
def n3_127 := certify 6 [i1,i2,i5,w18,i9,w17,i7,w39] [n4_32,n4_33,n4_53,n4_132,n4_211] (by decide +kernel)
def n3_128 := certify 6 [i1,i2,i5,w21,w69,i9,w17,i7] [n4_54,n4_134] (by decide +kernel)
def n3_129 := certify 6 [i1,i2,i5,w21,i9,w19,w17,i7] [n4_56,n4_214] (by decide +kernel)
def n3_130 := certify 6 [i1,i2,i5,w21,i9,i10,w33,w37] [n4_35,n4_58,n4_212,n4_215] (by decide +kernel)
def n3_131 := certify 6 [i1,i2,i5,w21,i9,w17,i7,w37] [n4_35,n4_55,n4_59,n4_133,n4_213] (by decide +kernel)
def n3_132 := certify 6 [i1,i2,w53,i6,i8,i9,w17,i7] [n4_38,n4_43] (by decide +kernel)
def n3_133 := certify 6 [i1,i2,w34,i6,i8,w20,w17,i7] [n4_39] (by decide +kernel)
def n3_134 := certify 6 [i1,i2,i6,w35,i8,w20,w17,i7] [n4_49,n4_142] (by decide +kernel)
def n3_135 := certify 6 [i1,i2,i6,i8,w18,w20,w17,i7] [n4_52,n4_139] (by decide +kernel)
def n3_136 := certify 6 [i1,i2,i6,i8,i9,w17,w37,w38] [n4_46,n4_55] (by decide +kernel)
def n3_137 := certify 6 [i1,i2,i6,i8,w19,w20,w17,i7] [n4_56] (by decide +kernel)
def n3_138 := certify 6 [i1,i2,i6,i8,w19,i10,w33,w38] [n4_40,n4_135] (by decide +kernel)
def n3_139 := certify 6 [i1,i2,i6,i8,w19,w17,i7,w38] [n4_40,n4_47,n4_50,n4_136,n4_221] (by decide +kernel)
def n3_140 := certify 6 [i1,i2,i6,i8,w20,w64,w17,i7] [n4_57,n4_223] (by decide +kernel)
def n3_141 := certify 6 [i1,i2,i6,i8,w20,i10,w33,w37] [n4_42,n4_58,n4_137,n4_140] (by decide +kernel)
def n3_142 := certify 6 [i1,i2,i6,i8,w20,w17,i7,w37] [n4_42,n4_51,n4_59,n4_138,n4_222] (by decide +kernel)
def n3_143 := certify 6 [i1,i2,i6,w18,i9,i10,w33,w38] [n4_45,n4_224] (by decide +kernel)
def n3_144 := certify 6 [i1,i2,i6,w18,i9,w17,i7,w38] [n4_45,n4_46,n4_53,n4_141,n4_225] (by decide +kernel)
def n3_145 := certify 6 [i1,i3,w29,i4,w21,w20,i10,i7] [n4_93,n4_281] (by decide +kernel)
def n3_146 := certify 6 [i1,i3,w36,i6,i8,w20,w16,i7] [n4_76,n4_78,n4_83] (by decide +kernel)
def n3_147 := certify 6 [i1,i3,w36,i6,w15,w20,i10,i7] [n4_79,n4_81,n4_84] (by decide +kernel)
def n3_148 := certify 6 [i1,i3,i4,i5,i6,i8,w41,w61] [n4_60,n4_72] (by decide +kernel)
def n3_149 := certify 6 [i1,i3,i4,i5,i6,w15,w41,w42] [n4_61] (by decide +kernel)
def n3_150 := certify 6 [i1,i3,i4,i5,i6,i10,w70,w41] [n4_62,n4_226] (by decide +kernel)
def n3_151 := certify 6 [i1,i3,i4,i5,i6,w16,w40,w41] [n4_63] (by decide +kernel)
def n3_152 := certify 6 [i1,i3,i4,i5,i8,i9,w61,w39] [n4_64,n4_73] (by decide +kernel)
def n3_153 := certify 6 [i1,i3,i4,i5,i8,w16,w41,w39] [n4_65,n4_74] (by decide +kernel)
def n3_154 := certify 6 [i1,i3,i4,i5,w15,i9,w42,w39] [n4_66,n4_227] (by decide +kernel)
def n3_155 := certify 6 [i1,i3,i4,i5,w15,i10,w41,w39] [n4_67,n4_228] (by decide +kernel)
def n3_156 := certify 6 [i1,i3,i4,i5,w21,i9,i10,w52] [n4_68,n4_94,n4_229,n4_230] (by decide +kernel)
def n3_157 := certify 6 [i1,i3,i4,i5,w21,i9,w51,i7] [n4_69,n4_95] (by decide +kernel)
def n3_158 := certify 6 [i1,i3,i4,i5,w21,i10,w32,w41] [n4_70,n4_96,n4_231,n4_232] (by decide +kernel)
def n3_159 := certify 6 [i1,i3,i4,i5,w75,i9,i10,i7] [n4_71,n4_97,n4_233,n4_234] (by decide +kernel)
def n3_160 := certify 6 [i1,i3,i4,i6,i8,i9,w38,w61] [n4_60,n4_75] (by decide +kernel)
def n3_161 := certify 6 [i1,i3,i4,i6,i8,w20,i10,w52] [n4_68,n4_98] (by decide +kernel)
def n3_162 := certify 6 [i1,i3,i4,i6,i8,w20,w51,i7] [n4_69,n4_99] (by decide +kernel)
def n3_163 := certify 6 [i1,i3,i4,i6,i8,w20,w16,i7] [] (by decide +kernel)
def n3_164 := certify 6 [i1,i3,i4,i6,i8,w20,w59,i7] [n4_282] (by decide +kernel)
def n3_165 := certify 6 [i1,i3,i4,i6,i8,w20,i7,w61] [n4_60,n4_64,n4_77] (by decide +kernel)
def n3_166 := certify 6 [i1,i3,i4,i6,i8,i10,w32,w67] [n4_60,n4_62,n4_70,n4_101] (by decide +kernel)
def n3_167 := certify 6 [i1,i3,i4,i6,i8,w16,i7,w67] [n4_60,n4_63,n4_65,n4_100] (by decide +kernel)
def n3_168 := certify 6 [i1,i3,i4,i6,w50,w20,i10,i7] [n4_71,n4_102] (by decide +kernel)
def n3_169 := certify 6 [i1,i3,i4,i6,w15,i9,w38,w42] [n4_61,n4_237] (by decide +kernel)
def n3_170 := certify 6 [i1,i3,i4,i6,w15,w20,i10,i7] [] (by decide +kernel)
def n3_171 := certify 6 [i1,i3,i4,i6,w15,w20,w16,i7] [] (by decide +kernel)
def n3_172 := certify 6 [i1,i3,i4,i6,w15,w20,w17,i7] [n4_283] (by decide +kernel)
def n3_173 := certify 6 [i1,i3,i4,i6,w15,w20,i7,w42] [n4_61,n4_66,n4_80] (by decide +kernel)
def n3_174 := certify 6 [i1,i3,i4,i6,w15,i10,i7,w67] [n4_61,n4_62,n4_67,n4_103] (by decide +kernel)
def n3_175 := certify 6 [i1,i3,i4,i6,w21,w20,w16,i7] [n4_85] (by decide +kernel)
def n3_176 := certify 6 [i1,i3,i4,i6,w68,w20,i10,i7] [n4_86] (by decide +kernel)
def n3_177 := certify 6 [i1,i3,i4,i6,i9,i10,w38,w70] [n4_62,n4_240] (by decide +kernel)
def n3_178 := certify 6 [i1,i3,i4,i6,i9,w16,w38,w40] [n4_63,n4_82] (by decide +kernel)
def n3_179 := certify 6 [i1,i3,i4,i6,w20,i10,i7,w70] [n4_62,n4_104,n4_241] (by decide +kernel)
def n3_180 := certify 6 [i1,i3,i4,i6,w20,w16,i7,w40] [n4_63,n4_105,n4_242] (by decide +kernel)
def n3_181 := certify 6 [i1,i3,i4,w49,i8,w20,i10,i7] [n4_71,n4_106] (by decide +kernel)
def n3_182 := certify 6 [i1,i3,i4,w30,w21,w20,i10,i7] [n4_107] (by decide +kernel)
def n3_183 := certify 6 [i1,i3,i4,i8,i9,w16,w38,w39] [n4_65,n4_87] (by decide +kernel)
def n3_184 := certify 6 [i1,i3,i4,i8,w20,i10,w32,w39] [n4_64,n4_109] (by decide +kernel)
def n3_185 := certify 6 [i1,i3,i4,i8,w20,w16,i7,w39] [n4_64,n4_65,n4_88,n4_108,n4_243] (by decide +kernel)
def n3_186 := certify 6 [i1,i3,i4,w15,w21,w20,i10,i7] [n4_110] (by decide +kernel)
def n3_187 := certify 6 [i1,i3,i4,w15,i9,i10,w38,w39] [n4_67,n4_244] (by decide +kernel)
def n3_188 := certify 6 [i1,i3,i4,w15,w20,i10,i7,w39] [n4_66,n4_67,n4_89,n4_111,n4_245] (by decide +kernel)
def n3_189 := certify 6 [i1,i3,i4,w21,w68,w20,i10,i7] [n4_91,n4_112] (by decide +kernel)
def n3_190 := certify 6 [i1,i3,i4,w21,i9,i10,w32,w38] [n4_70,n4_113,n4_246,n4_247] (by decide +kernel)
def n3_191 := certify 6 [i1,i3,i4,w21,w20,i10,w16,i7] [n4_115,n4_249] (by decide +kernel)
def n3_192 := certify 6 [i1,i3,i4,w21,w20,i10,i7,w32] [n4_70,n4_90,n4_114,n4_117,n4_248] (by decide +kernel)
def n3_193 := certify 6 [i1,i3,i5,i6,i8,i9,w16,w57] [n4_76] (by decide +kernel)
def n3_194 := certify 6 [i1,i3,i5,i6,i8,i9,w37,w61] [n4_72,n4_77] (by decide +kernel)
def n3_195 := certify 6 [i1,i3,i5,i6,i8,w56,w16,i7] [n4_78] (by decide +kernel)
def n3_196 := certify 6 [i1,i3,i5,i6,i8,w19,i10,w52] [n4_118] (by decide +kernel)
def n3_197 := certify 6 [i1,i3,i5,i6,i8,w19,w51,i7] [n4_119] (by decide +kernel)
def n3_198 := certify 6 [i1,i3,i5,i6,i8,w19,w16,i7] [] (by decide +kernel)
def n3_199 := certify 6 [i1,i3,i5,i6,i8,w19,w59,i7] [n4_284] (by decide +kernel)
def n3_200 := certify 6 [i1,i3,i5,i6,i8,w19,i7,w61] [n4_72,n4_73,n4_75] (by decide +kernel)
def n3_201 := certify 6 [i1,i3,i5,i6,i8,w64,w16,i7] [n4_268] (by decide +kernel)
def n3_202 := certify 6 [i1,i3,i5,i6,i8,i10,w32,w66] [n4_72,n4_121] (by decide +kernel)
def n3_203 := certify 6 [i1,i3,i5,i6,i8,w16,i7,w66] [n4_72,n4_74,n4_120] (by decide +kernel)
def n3_204 := certify 6 [i1,i3,i5,i6,w22,w19,w16,i7] [] (by decide +kernel)
def n3_205 := certify 6 [i1,i3,i5,i6,w15,i9,i10,w57] [n4_79,n4_251] (by decide +kernel)
def n3_206 := certify 6 [i1,i3,i5,i6,w15,i9,w37,w42] [n4_80,n4_252] (by decide +kernel)
def n3_207 := certify 6 [i1,i3,i5,i6,w15,w56,i10,i7] [n4_81] (by decide +kernel)
def n3_208 := certify 6 [i1,i3,i5,i6,w15,w19,w16,i7] [] (by decide +kernel)
def n3_209 := certify 6 [i1,i3,i5,i6,w18,i9,i10,w52] [n4_122,n4_253] (by decide +kernel)
def n3_210 := certify 6 [i1,i3,i5,i6,w18,i9,w51,i7] [n4_123] (by decide +kernel)
def n3_211 := certify 6 [i1,i3,i5,i6,w18,w19,w16,i7] [] (by decide +kernel)
def n3_212 := certify 6 [i1,i3,i5,i6,w18,i10,w32,w41] [n4_124,n4_254] (by decide +kernel)
def n3_213 := certify 6 [i1,i3,i5,i6,w21,w19,w16,i7] [] (by decide +kernel)
def n3_214 := certify 6 [i1,i3,i5,i6,w19,w16,i7,w40] [n4_82,n4_125,n4_255] (by decide +kernel)
def n3_215 := certify 6 [i1,i3,i5,w49,i8,w19,i10,i7] [n4_126] (by decide +kernel)
def n3_216 := certify 6 [i1,i3,i5,w49,w18,i9,i10,i7] [n4_127,n4_256] (by decide +kernel)
def n3_217 := certify 6 [i1,i3,i5,w30,w21,w19,i10,i7] [n4_128] (by decide +kernel)
def n3_218 := certify 6 [i1,i3,i5,w30,w69,i9,i10,i7] [n4_129,n4_257] (by decide +kernel)
def n3_219 := certify 6 [i1,i3,i5,w54,i8,i9,w16,i7] [n4_83] (by decide +kernel)
def n3_220 := certify 6 [i1,i3,i5,w54,w15,i9,i10,i7] [n4_84,n4_258] (by decide +kernel)
def n3_221 := certify 6 [i1,i3,i5,w35,w21,i9,w16,i7] [n4_85] (by decide +kernel)
def n3_222 := certify 6 [i1,i3,i5,w35,w68,i9,i10,i7] [n4_86,n4_259] (by decide +kernel)
def n3_223 := certify 6 [i1,i3,i5,i8,i9,w16,w37,w39] [n4_74,n4_88] (by decide +kernel)
def n3_224 := certify 6 [i1,i3,i5,i8,w19,i10,w32,w39] [n4_73,n4_131] (by decide +kernel)
def n3_225 := certify 6 [i1,i3,i5,i8,w19,w16,i7,w39] [n4_73,n4_74,n4_87,n4_130,n4_260] (by decide +kernel)
def n3_226 := certify 6 [i1,i3,i5,w15,i9,i10,w37,w39] [n4_89,n4_261] (by decide +kernel)
def n3_227 := certify 6 [i1,i3,i5,w18,i9,i10,w32,w39] [n4_132,n4_262] (by decide +kernel)
def n3_228 := certify 6 [i1,i3,i5,w21,i9,i10,w32,w37] [n4_90,n4_133,n4_263,n4_264] (by decide +kernel)
def n3_229 := certify 6 [i1,i3,i5,w68,w69,i9,i10,i7] [n4_91,n4_134,n4_265,n4_266] (by decide +kernel)
def n3_230 := certify 6 [i1,i3,w53,i6,i8,i9,w16,i7] [n4_78] (by decide +kernel)
def n3_231 := certify 6 [i1,i3,w53,i6,w15,i9,i10,i7] [n4_81,n4_269] (by decide +kernel)
def n3_232 := certify 6 [i1,i3,w34,i6,i8,w20,w16,i7] [] (by decide +kernel)
def n3_233 := certify 6 [i1,i3,w34,i6,w15,w20,i10,i7] [n4_270] (by decide +kernel)
def n3_234 := certify 6 [i1,i3,i6,w35,i8,w20,w16,i7] [n4_85] (by decide +kernel)
def n3_235 := certify 6 [i1,i3,i6,w35,w15,w20,i10,i7] [n4_86] (by decide +kernel)
def n3_236 := certify 6 [i1,i3,i6,i8,i9,w16,w37,w38] [] (by decide +kernel)
def n3_237 := certify 6 [i1,i3,i6,i8,w19,w20,w16,i7] [] (by decide +kernel)
def n3_238 := certify 6 [i1,i3,i6,i8,w19,i10,w32,w38] [n4_75,n4_136] (by decide +kernel)
def n3_239 := certify 6 [i1,i3,i6,i8,w19,w16,i7,w38] [n4_75,n4_82,n4_87,n4_135,n4_271] (by decide +kernel)
def n3_240 := certify 6 [i1,i3,i6,i8,w20,w64,w16,i7] [n4_273] (by decide +kernel)
def n3_241 := certify 6 [i1,i3,i6,i8,w20,i10,w32,w37] [n4_77,n4_90,n4_138] (by decide +kernel)
def n3_242 := certify 6 [i1,i3,i6,i8,w20,w16,i7,w37] [n4_77,n4_88,n4_137,n4_272] (by decide +kernel)
def n3_243 := certify 6 [i1,i3,i6,w15,w18,w20,i10,i7] [n4_139] (by decide +kernel)
def n3_244 := certify 6 [i1,i3,i6,w15,i9,i10,w37,w38] [n4_274] (by decide +kernel)
def n3_245 := certify 6 [i1,i3,i6,w15,w19,w20,i10,i7] [] (by decide +kernel)
def n3_246 := certify 6 [i1,i3,i6,w15,w20,w64,i10,i7] [n4_276] (by decide +kernel)
def n3_247 := certify 6 [i1,i3,i6,w15,w20,i10,i7,w37] [n4_80,n4_89,n4_140,n4_275] (by decide +kernel)
def n3_248 := certify 6 [i1,i3,i6,w18,i9,i10,w32,w38] [n4_141,n4_277] (by decide +kernel)
def n3_249 := certify 6 [i1,i3,w30,w35,i8,w20,i10,i7] [n4_86,n4_142] (by decide +kernel)
def n3_250 := certify 6 [i1,w48,i4,i5,w21,i9,i10,i7] [n4_92,n4_95,n4_285,n4_286] (by decide +kernel)
def n3_251 := certify 6 [i1,w48,i4,i6,i8,w20,i10,i7] [n4_92,n4_99] (by decide +kernel)
def n3_252 := certify 6 [i1,w48,i5,i6,i8,w19,i10,i7] [n4_119] (by decide +kernel)
def n3_253 := certify 6 [i1,w48,i5,i6,w18,i9,i10,i7] [n4_123,n4_287] (by decide +kernel)
def n3_254 := certify 6 [i1,w29,i4,i5,w21,i9,w17,i7] [n4_93,n4_288,n4_289] (by decide +kernel)
def n3_255 := certify 6 [i1,w29,i4,i6,i8,w20,w17,i7] [n4_93] (by decide +kernel)
def n3_256 := certify 6 [i1,w29,i5,i6,i8,w19,w17,i7] [] (by decide +kernel)
def n3_257 := certify 6 [i1,w29,i5,i6,w18,i9,w17,i7] [n4_290] (by decide +kernel)
def n3_258 := certify 6 [i1,i4,i5,i6,i8,i9,w17,w52] [n4_94,n4_98,n4_118,n4_122] (by decide +kernel)
def n3_259 := certify 6 [i1,i4,i5,i6,i8,i9,w76,i7] [n4_95,n4_99,n4_119,n4_123] (by decide +kernel)
def n3_260 := certify 6 [i1,i4,i5,i6,i8,w16,w33,w41] [n4_100,n4_120] (by decide +kernel)
def n3_261 := certify 6 [i1,i4,i5,i6,i8,w17,w32,w41] [n4_96,n4_101,n4_121,n4_124] (by decide +kernel)
def n3_262 := certify 6 [i1,i4,i5,i6,w50,i9,w17,i7] [n4_97,n4_102] (by decide +kernel)
def n3_263 := certify 6 [i1,i4,i5,i6,w15,i10,w33,w41] [n4_103,n4_291] (by decide +kernel)
def n3_264 := certify 6 [i1,i4,i5,i6,i9,i10,w33,w70] [n4_104,n4_292] (by decide +kernel)
def n3_265 := certify 6 [i1,i4,i5,i6,i9,w16,w33,w40] [n4_105,n4_125] (by decide +kernel)
def n3_266 := certify 6 [i1,i4,i5,w49,i8,i9,w17,i7] [n4_97,n4_106,n4_126,n4_127] (by decide +kernel)
def n3_267 := certify 6 [i1,i4,i5,w30,w21,i9,w17,i7] [n4_107,n4_128,n4_129] (by decide +kernel)
def n3_268 := certify 6 [i1,i4,i5,i8,i9,w16,w33,w39] [n4_108,n4_130] (by decide +kernel)
def n3_269 := certify 6 [i1,i4,i5,i8,i9,w17,w32,w39] [n4_109,n4_131,n4_132] (by decide +kernel)
def n3_270 := certify 6 [i1,i4,i5,w15,w21,i9,w17,i7] [n4_110] (by decide +kernel)
def n3_271 := certify 6 [i1,i4,i5,w15,i9,i10,w33,w39] [n4_111,n4_293] (by decide +kernel)
def n3_272 := certify 6 [i1,i4,i5,w21,w68,i9,w17,i7] [n4_112,n4_134] (by decide +kernel)
def n3_273 := certify 6 [i1,i4,i5,w21,i9,i10,w32,w33] [n4_114,n4_294,n4_297] (by decide +kernel)
def n3_274 := certify 6 [i1,i4,i5,w21,i9,w16,w17,i7] [n4_115] (by decide +kernel)
def n3_275 := certify 6 [i1,i4,i5,w21,i9,w17,w59,i7] [n4_116,n4_296] (by decide +kernel)
def n3_276 := certify 6 [i1,i4,i5,w21,i9,w17,i7,w32] [n4_96,n4_113,n4_117,n4_133,n4_295] (by decide +kernel)
def n3_277 := certify 6 [i1,i4,i6,w30,i8,w20,w17,i7] [n4_107,n4_142] (by decide +kernel)
def n3_278 := certify 6 [i1,i4,i6,i8,w15,w20,w17,i7] [n4_110,n4_139] (by decide +kernel)
def n3_279 := certify 6 [i1,i4,i6,i8,i9,w16,w33,w38] [n4_100,n4_135] (by decide +kernel)
def n3_280 := certify 6 [i1,i4,i6,i8,i9,w17,w32,w38] [n4_101,n4_113,n4_136,n4_141] (by decide +kernel)
def n3_281 := certify 6 [i1,i4,i6,i8,w20,i10,w32,w33] [n4_104,n4_114] (by decide +kernel)
def n3_282 := certify 6 [i1,i4,i6,i8,w20,w16,w17,i7] [n4_115] (by decide +kernel)
def n3_283 := certify 6 [i1,i4,i6,i8,w20,w16,i7,w33] [n4_100,n4_105,n4_108,n4_137,n4_298] (by decide +kernel)
def n3_284 := certify 6 [i1,i4,i6,i8,w20,w17,w59,i7] [n4_116,n4_300] (by decide +kernel)
def n3_285 := certify 6 [i1,i4,i6,i8,w20,w17,i7,w32] [n4_101,n4_109,n4_117,n4_138,n4_299] (by decide +kernel)
def n3_286 := certify 6 [i1,i4,i6,w15,i9,i10,w33,w38] [n4_103,n4_301] (by decide +kernel)
def n3_287 := certify 6 [i1,i4,i6,w15,w20,i10,i7,w33] [n4_103,n4_104,n4_111,n4_140,n4_302] (by decide +kernel)
def n3_288 := certify 6 [i1,i5,i6,w30,i8,w19,w17,i7] [n4_128] (by decide +kernel)
def n3_289 := certify 6 [i1,i5,i6,w30,w18,i9,w17,i7] [n4_129] (by decide +kernel)
def n3_290 := certify 6 [i1,i5,i6,i8,i9,w16,w33,w37] [n4_120,n4_137] (by decide +kernel)
def n3_291 := certify 6 [i1,i5,i6,i8,i9,w17,w32,w37] [n4_121,n4_133,n4_138] (by decide +kernel)
def n3_292 := certify 6 [i1,i5,i6,i8,w19,i10,w32,w33] [] (by decide +kernel)
def n3_293 := certify 6 [i1,i5,i6,i8,w19,w16,w17,i7] [] (by decide +kernel)
def n3_294 := certify 6 [i1,i5,i6,i8,w19,w16,i7,w33] [n4_120,n4_125,n4_130,n4_135,n4_303] (by decide +kernel)
def n3_295 := certify 6 [i1,i5,i6,i8,w19,w17,w59,i7] [n4_305] (by decide +kernel)
def n3_296 := certify 6 [i1,i5,i6,i8,w19,w17,i7,w32] [n4_121,n4_131,n4_136,n4_304] (by decide +kernel)
def n3_297 := certify 6 [i1,i5,i6,w15,w18,i9,w17,i7] [n4_139] (by decide +kernel)
def n3_298 := certify 6 [i1,i5,i6,w15,i9,i10,w33,w37] [n4_140,n4_306] (by decide +kernel)
def n3_299 := certify 6 [i1,i5,i6,w18,i9,i10,w32,w33] [n4_307] (by decide +kernel)
def n3_300 := certify 6 [i1,i5,i6,w18,i9,w16,w17,i7] [] (by decide +kernel)
def n3_301 := certify 6 [i1,i5,i6,w18,i9,w17,w59,i7] [n4_309] (by decide +kernel)
def n3_302 := certify 6 [i1,i5,i6,w18,i9,w17,i7,w32] [n4_124,n4_132,n4_141,n4_308] (by decide +kernel)
def n3_303 := certify 6 [i1,i5,w30,w35,i8,i9,w17,i7] [n4_129,n4_142] (by decide +kernel)
def n3_304 := certify 6 [w31,i3,i4,i5,w21,i9,w14,i7] [n4_229,n4_233,n4_285] (by decide +kernel)
def n3_305 := certify 6 [w31,i3,i4,i5,w21,w13,i10,i7] [n4_230,n4_234,n4_286] (by decide +kernel)
def n3_306 := certify 6 [w31,i3,i5,i6,w18,i9,w14,i7] [n4_253,n4_256,n4_287] (by decide +kernel)
def n3_307 := certify 6 [i2,i3,w25,i4,w21,w20,i10,i7] [n4_176,n4_281] (by decide +kernel)
def n3_308 := certify 6 [i2,i3,w36,i5,w21,i9,w14,i7] [n4_158,n4_162,n4_164] (by decide +kernel)
def n3_309 := certify 6 [i2,i3,w36,i5,w21,w13,i10,i7] [n4_160,n4_163,n4_165] (by decide +kernel)
def n3_310 := certify 6 [i2,i3,i4,i5,i6,i9,w40,w60] [n4_143,n4_155] (by decide +kernel)
def n3_311 := certify 6 [i2,i3,i4,i5,i6,w13,w40,w42] [n4_144] (by decide +kernel)
def n3_312 := certify 6 [i2,i3,i4,i5,i6,i10,w40,w65] [n4_145,n4_226] (by decide +kernel)
def n3_313 := certify 6 [i2,i3,i4,i5,i6,w14,w40,w41] [n4_146] (by decide +kernel)
def n3_314 := certify 6 [i2,i3,i4,i5,i8,i9,w60,w39] [n4_143,n4_156] (by decide +kernel)
def n3_315 := certify 6 [i2,i3,i4,i5,i8,w13,w42,w39] [n4_144,n4_227] (by decide +kernel)
def n3_316 := certify 6 [i2,i3,i4,i5,i8,i10,w65,w39] [n4_145,n4_228] (by decide +kernel)
def n3_317 := certify 6 [i2,i3,i4,i5,i8,w14,w41,w39] [n4_146,n4_157] (by decide +kernel)
def n3_318 := certify 6 [i2,i3,i4,i5,w21,i9,i10,w47] [n4_149,n4_177] (by decide +kernel)
def n3_319 := certify 6 [i2,i3,i4,i5,w21,i9,w46,i7] [n4_150,n4_178] (by decide +kernel)
def n3_320 := certify 6 [i2,i3,i4,i5,w21,i9,w14,i7] [] (by decide +kernel)
def n3_321 := certify 6 [i2,i3,i4,i5,w21,i9,w58,i7] [n4_288] (by decide +kernel)
def n3_322 := certify 6 [i2,i3,i4,i5,w21,i9,i7,w60] [n4_143,n4_147,n4_159] (by decide +kernel)
def n3_323 := certify 6 [i2,i3,i4,i5,w21,w45,i10,i7] [n4_151,n4_179] (by decide +kernel)
def n3_324 := certify 6 [i2,i3,i4,i5,w21,w13,i10,i7] [] (by decide +kernel)
def n3_325 := certify 6 [i2,i3,i4,i5,w21,w13,w14,i7] [] (by decide +kernel)
def n3_326 := certify 6 [i2,i3,i4,i5,w21,w13,w17,i7] [n4_289] (by decide +kernel)
def n3_327 := certify 6 [i2,i3,i4,i5,w21,w13,i7,w42] [n4_144,n4_148,n4_161] (by decide +kernel)
def n3_328 := certify 6 [i2,i3,i4,i5,w21,w20,w14,i7] [n4_166] (by decide +kernel)
def n3_329 := certify 6 [i2,i3,i4,i5,w21,w63,i10,i7] [n4_167] (by decide +kernel)
def n3_330 := certify 6 [i2,i3,i4,i5,w21,i10,i7,w65] [n4_145,n4_180,n4_231] (by decide +kernel)
def n3_331 := certify 6 [i2,i3,i4,i5,w21,w14,i7,w41] [n4_146,n4_181,n4_232] (by decide +kernel)
def n3_332 := certify 6 [i2,i3,i4,i5,i9,i10,w28,w72] [n4_143,n4_145,n4_154,n4_183] (by decide +kernel)
def n3_333 := certify 6 [i2,i3,i4,i5,i9,w14,i7,w72] [n4_143,n4_146,n4_152,n4_182] (by decide +kernel)
def n3_334 := certify 6 [i2,i3,i4,i5,w13,i10,i7,w72] [n4_144,n4_145,n4_153,n4_184] (by decide +kernel)
def n3_335 := certify 6 [i2,i3,i4,w44,w21,i9,i10,i7] [n4_151,n4_185] (by decide +kernel)
def n3_336 := certify 6 [i2,i3,i4,w26,w21,w20,i10,i7] [n4_186] (by decide +kernel)
def n3_337 := certify 6 [i2,i3,i4,i6,i8,i9,w38,w60] [n4_147,n4_168] (by decide +kernel)
def n3_338 := certify 6 [i2,i3,i4,i6,i8,w13,w38,w42] [n4_148,n4_237] (by decide +kernel)
def n3_339 := certify 6 [i2,i3,i4,i6,i8,w20,i10,w47] [n4_149,n4_187,n4_235,n4_238] (by decide +kernel)
def n3_340 := certify 6 [i2,i3,i4,i6,i8,w20,w46,i7] [n4_150,n4_188] (by decide +kernel)
def n3_341 := certify 6 [i2,i3,i4,i6,i8,w73,i10,i7] [n4_151,n4_189,n4_236,n4_239] (by decide +kernel)
def n3_342 := certify 6 [i2,i3,i4,i6,i9,w14,w38,w40] [n4_152,n4_169] (by decide +kernel)
def n3_343 := certify 6 [i2,i3,i4,i6,w13,i10,w38,w40] [n4_153,n4_240] (by decide +kernel)
def n3_344 := certify 6 [i2,i3,i4,i6,w20,i10,w28,w40] [n4_154,n4_190,n4_241,n4_242] (by decide +kernel)
def n3_345 := certify 6 [i2,i3,i4,i8,i9,w14,w38,w39] [n4_152,n4_170] (by decide +kernel)
def n3_346 := certify 6 [i2,i3,i4,i8,w13,i10,w38,w39] [n4_153,n4_244] (by decide +kernel)
def n3_347 := certify 6 [i2,i3,i4,i8,w20,i10,w28,w39] [n4_154,n4_191,n4_243,n4_245] (by decide +kernel)
def n3_348 := certify 6 [i2,i3,i4,w21,i9,i10,w28,w38] [n4_147,n4_193] (by decide +kernel)
def n3_349 := certify 6 [i2,i3,i4,w21,i9,w14,i7,w38] [n4_147,n4_152,n4_171,n4_192,n4_246] (by decide +kernel)
def n3_350 := certify 6 [i2,i3,i4,w21,w13,w20,i10,i7] [n4_194] (by decide +kernel)
def n3_351 := certify 6 [i2,i3,i4,w21,w13,i10,i7,w38] [n4_148,n4_153,n4_172,n4_195,n4_247] (by decide +kernel)
def n3_352 := certify 6 [i2,i3,i4,w21,w20,w63,i10,i7] [n4_174,n4_196] (by decide +kernel)
def n3_353 := certify 6 [i2,i3,i4,w21,w20,i10,w14,i7] [n4_198,n4_249] (by decide +kernel)
def n3_354 := certify 6 [i2,i3,i4,w21,w20,i10,i7,w28] [n4_154,n4_173,n4_197,n4_200,n4_248] (by decide +kernel)
def n3_355 := certify 6 [i2,i3,i5,w34,w21,i9,w14,i7] [n4_166] (by decide +kernel)
def n3_356 := certify 6 [i2,i3,i5,w34,w21,w13,i10,i7] [n4_167] (by decide +kernel)
def n3_357 := certify 6 [i2,i3,i5,i6,i8,i9,w14,w57] [n4_158] (by decide +kernel)
def n3_358 := certify 6 [i2,i3,i5,i6,i8,i9,w37,w60] [n4_155,n4_159] (by decide +kernel)
def n3_359 := certify 6 [i2,i3,i5,i6,i8,w13,i10,w57] [n4_160,n4_251] (by decide +kernel)
def n3_360 := certify 6 [i2,i3,i5,i6,i8,w13,w37,w42] [n4_161,n4_252] (by decide +kernel)
def n3_361 := certify 6 [i2,i3,i5,i6,i8,w19,i10,w47] [n4_201,n4_250] (by decide +kernel)
def n3_362 := certify 6 [i2,i3,i5,i6,i8,w19,w46,i7] [n4_202] (by decide +kernel)
def n3_363 := certify 6 [i2,i3,i5,i6,w55,i9,w14,i7] [n4_162] (by decide +kernel)
def n3_364 := certify 6 [i2,i3,i5,i6,w55,w13,i10,i7] [n4_163] (by decide +kernel)
def n3_365 := certify 6 [i2,i3,i5,i6,w18,i9,i10,w47] [n4_203] (by decide +kernel)
def n3_366 := certify 6 [i2,i3,i5,i6,w18,i9,w46,i7] [n4_204] (by decide +kernel)
def n3_367 := certify 6 [i2,i3,i5,i6,w18,i9,w14,i7] [] (by decide +kernel)
def n3_368 := certify 6 [i2,i3,i5,i6,w18,i9,w58,i7] [n4_290] (by decide +kernel)
def n3_369 := certify 6 [i2,i3,i5,i6,w18,i9,i7,w60] [n4_155,n4_156,n4_168] (by decide +kernel)
def n3_370 := certify 6 [i2,i3,i5,i6,w18,w23,w14,i7] [] (by decide +kernel)
def n3_371 := certify 6 [i2,i3,i5,i6,w18,w13,w14,i7] [] (by decide +kernel)
def n3_372 := certify 6 [i2,i3,i5,i6,w18,w19,w14,i7] [] (by decide +kernel)
def n3_373 := certify 6 [i2,i3,i5,i6,w18,w20,w14,i7] [] (by decide +kernel)
def n3_374 := certify 6 [i2,i3,i5,i6,w18,w14,i7,w41] [n4_157,n4_205,n4_254] (by decide +kernel)
def n3_375 := certify 6 [i2,i3,i5,i6,w69,i9,w14,i7] [n4_257] (by decide +kernel)
def n3_376 := certify 6 [i2,i3,i5,i6,i9,i10,w28,w71] [n4_155,n4_207] (by decide +kernel)
def n3_377 := certify 6 [i2,i3,i5,i6,i9,w14,i7,w71] [n4_155,n4_169,n4_206] (by decide +kernel)
def n3_378 := certify 6 [i2,i3,i5,i6,w19,i10,w28,w40] [n4_208,n4_255] (by decide +kernel)
def n3_379 := certify 6 [i2,i3,i5,w54,i8,i9,w14,i7] [n4_162] (by decide +kernel)
def n3_380 := certify 6 [i2,i3,i5,w54,i8,w13,i10,i7] [n4_163,n4_258] (by decide +kernel)
def n3_381 := certify 6 [i2,i3,i5,w35,w21,i9,w14,i7] [] (by decide +kernel)
def n3_382 := certify 6 [i2,i3,i5,w35,w21,w13,i10,i7] [n4_259] (by decide +kernel)
def n3_383 := certify 6 [i2,i3,i5,i8,i9,w14,w37,w39] [] (by decide +kernel)
def n3_384 := certify 6 [i2,i3,i5,i8,w13,i10,w37,w39] [n4_261] (by decide +kernel)
def n3_385 := certify 6 [i2,i3,i5,i8,w19,i10,w28,w39] [n4_209,n4_260] (by decide +kernel)
def n3_386 := certify 6 [i2,i3,i5,w18,w21,i9,w14,i7] [] (by decide +kernel)
def n3_387 := certify 6 [i2,i3,i5,w18,w21,w13,i10,i7] [] (by decide +kernel)
def n3_388 := certify 6 [i2,i3,i5,w18,i9,i10,w28,w39] [n4_156,n4_211] (by decide +kernel)
def n3_389 := certify 6 [i2,i3,i5,w18,i9,w14,i7,w39] [n4_156,n4_157,n4_170,n4_210,n4_262] (by decide +kernel)
def n3_390 := certify 6 [i2,i3,i5,w21,w69,i9,w14,i7] [n4_265] (by decide +kernel)
def n3_391 := certify 6 [i2,i3,i5,w21,w69,w13,i10,i7] [n4_266] (by decide +kernel)
def n3_392 := certify 6 [i2,i3,i5,w21,i9,i10,w28,w37] [n4_159,n4_173,n4_213] (by decide +kernel)
def n3_393 := certify 6 [i2,i3,i5,w21,i9,w14,i7,w37] [n4_159,n4_171,n4_212,n4_263] (by decide +kernel)
def n3_394 := certify 6 [i2,i3,i5,w21,w13,w19,i10,i7] [n4_214] (by decide +kernel)
def n3_395 := certify 6 [i2,i3,i5,w21,w13,i10,i7,w37] [n4_161,n4_172,n4_215,n4_264] (by decide +kernel)
def n3_396 := certify 6 [i2,i3,w44,i6,i8,w19,i10,i7] [n4_216,n4_267] (by decide +kernel)
def n3_397 := certify 6 [i2,i3,w44,i6,w18,i9,i10,i7] [n4_217] (by decide +kernel)
def n3_398 := certify 6 [i2,i3,w26,w34,w21,i9,i10,i7] [n4_167,n4_218] (by decide +kernel)
def n3_399 := certify 6 [i2,i3,w26,i6,i8,w64,i10,i7] [n4_219,n4_268] (by decide +kernel)
def n3_400 := certify 6 [i2,i3,w26,i6,w18,w20,i10,i7] [n4_220] (by decide +kernel)
def n3_401 := certify 6 [i2,i3,w53,i6,i8,i9,w14,i7] [n4_164] (by decide +kernel)
def n3_402 := certify 6 [i2,i3,w53,i6,i8,w13,i10,i7] [n4_165,n4_269] (by decide +kernel)
def n3_403 := certify 6 [i2,i3,w34,i6,i8,w20,w14,i7] [n4_166] (by decide +kernel)
def n3_404 := certify 6 [i2,i3,w34,i6,i8,w63,i10,i7] [n4_167,n4_270] (by decide +kernel)
def n3_405 := certify 6 [i2,i3,i6,i8,i9,w14,w37,w38] [n4_169,n4_171] (by decide +kernel)
def n3_406 := certify 6 [i2,i3,i6,i8,w13,i10,w37,w38] [n4_172,n4_274] (by decide +kernel)
def n3_407 := certify 6 [i2,i3,i6,i8,w19,i10,w28,w38] [n4_221,n4_271] (by decide +kernel)
def n3_408 := certify 6 [i2,i3,i6,i8,w20,i10,w28,w37] [n4_173,n4_222,n4_272,n4_275] (by decide +kernel)
def n3_409 := certify 6 [i2,i3,i6,i8,w63,w64,i10,i7] [n4_174,n4_223,n4_273,n4_276] (by decide +kernel)
def n3_410 := certify 6 [i2,i3,i6,w18,i9,i10,w28,w38] [n4_168,n4_225] (by decide +kernel)
def n3_411 := certify 6 [i2,i3,i6,w18,i9,w14,i7,w38] [n4_168,n4_169,n4_170,n4_224,n4_277] (by decide +kernel)
def n3_412 := certify 6 [i2,w43,i4,i5,w21,i9,i10,i7] [n4_175,n4_178] (by decide +kernel)
def n3_413 := certify 6 [i2,w43,i4,i6,i8,w20,i10,i7] [n4_175,n4_188,n4_278,n4_279] (by decide +kernel)
def n3_414 := certify 6 [i2,w43,i5,i6,i8,w19,i10,i7] [n4_202,n4_280] (by decide +kernel)
def n3_415 := certify 6 [i2,w43,i5,i6,w18,i9,i10,i7] [n4_204] (by decide +kernel)
def n3_416 := certify 6 [i2,w25,i4,i5,w21,i9,w17,i7] [n4_176] (by decide +kernel)
def n3_417 := certify 6 [i2,w25,i4,i6,i8,w20,w17,i7] [n4_176,n4_282,n4_283] (by decide +kernel)
def n3_418 := certify 6 [i2,w25,i5,i6,i8,w19,w17,i7] [n4_284] (by decide +kernel)
def n3_419 := certify 6 [i2,w25,i5,i6,w18,i9,w17,i7] [] (by decide +kernel)
def n3_420 := certify 6 [i2,i4,i5,w26,w21,i9,w17,i7] [n4_186,n4_218] (by decide +kernel)
def n3_421 := certify 6 [i2,i4,i5,i6,i8,i9,w17,w47] [n4_177,n4_187,n4_201,n4_203] (by decide +kernel)
def n3_422 := certify 6 [i2,i4,i5,i6,i8,i9,w74,i7] [n4_178,n4_188,n4_202,n4_204] (by decide +kernel)
def n3_423 := certify 6 [i2,i4,i5,i6,i8,w45,w17,i7] [n4_179,n4_189] (by decide +kernel)
def n3_424 := certify 6 [i2,i4,i5,i6,i8,i10,w33,w65] [n4_180,n4_291] (by decide +kernel)
def n3_425 := certify 6 [i2,i4,i5,i6,i8,w14,w33,w41] [n4_181,n4_205] (by decide +kernel)
def n3_426 := certify 6 [i2,i4,i5,i6,i9,w14,w33,w40] [n4_182,n4_206] (by decide +kernel)
def n3_427 := certify 6 [i2,i4,i5,i6,i9,w17,w28,w40] [n4_183,n4_190,n4_207,n4_208] (by decide +kernel)
def n3_428 := certify 6 [i2,i4,i5,i6,w13,i10,w33,w40] [n4_184,n4_292] (by decide +kernel)
def n3_429 := certify 6 [i2,i4,i5,i8,i9,w14,w33,w39] [n4_182,n4_210] (by decide +kernel)
def n3_430 := certify 6 [i2,i4,i5,i8,i9,w17,w28,w39] [n4_183,n4_191,n4_209,n4_211] (by decide +kernel)
def n3_431 := certify 6 [i2,i4,i5,i8,w13,i10,w33,w39] [n4_184,n4_293] (by decide +kernel)
def n3_432 := certify 6 [i2,i4,i5,w21,i9,w13,w17,i7] [n4_194,n4_214] (by decide +kernel)
def n3_433 := certify 6 [i2,i4,i5,w21,i9,i10,w28,w33] [n4_180,n4_197] (by decide +kernel)
def n3_434 := certify 6 [i2,i4,i5,w21,i9,w14,w17,i7] [n4_198] (by decide +kernel)
def n3_435 := certify 6 [i2,i4,i5,w21,i9,w14,i7,w33] [n4_181,n4_182,n4_192,n4_212,n4_294] (by decide +kernel)
def n3_436 := certify 6 [i2,i4,i5,w21,i9,w17,w58,i7] [n4_199,n4_296] (by decide +kernel)
def n3_437 := certify 6 [i2,i4,i5,w21,i9,w17,i7,w28] [n4_183,n4_193,n4_200,n4_213,n4_295] (by decide +kernel)
def n3_438 := certify 6 [i2,i4,i5,w21,w13,i10,i7,w33] [n4_180,n4_184,n4_195,n4_215,n4_297] (by decide +kernel)
def n3_439 := certify 6 [i2,i4,w44,i6,i8,i9,w17,i7] [n4_185,n4_189,n4_216,n4_217] (by decide +kernel)
def n3_440 := certify 6 [i2,i4,w26,i6,i8,w20,w17,i7] [n4_186,n4_219,n4_220] (by decide +kernel)
def n3_441 := certify 6 [i2,i4,i6,i8,i9,w14,w33,w38] [n4_192,n4_224] (by decide +kernel)
def n3_442 := certify 6 [i2,i4,i6,i8,i9,w17,w28,w38] [n4_193,n4_221,n4_225] (by decide +kernel)
def n3_443 := certify 6 [i2,i4,i6,i8,w13,w20,w17,i7] [n4_194] (by decide +kernel)
def n3_444 := certify 6 [i2,i4,i6,i8,w13,i10,w33,w38] [n4_195,n4_301] (by decide +kernel)
def n3_445 := certify 6 [i2,i4,i6,i8,w20,w63,w17,i7] [n4_196,n4_223] (by decide +kernel)
def n3_446 := certify 6 [i2,i4,i6,i8,w20,i10,w28,w33] [n4_197,n4_298,n4_302] (by decide +kernel)
def n3_447 := certify 6 [i2,i4,i6,i8,w20,w14,w17,i7] [n4_198] (by decide +kernel)
def n3_448 := certify 6 [i2,i4,i6,i8,w20,w17,w58,i7] [n4_199,n4_300] (by decide +kernel)
def n3_449 := certify 6 [i2,i4,i6,i8,w20,w17,i7,w28] [n4_190,n4_191,n4_200,n4_222,n4_299] (by decide +kernel)
def n3_450 := certify 6 [i2,i5,w26,i6,i8,w19,w17,i7] [n4_219] (by decide +kernel)
def n3_451 := certify 6 [i2,i5,w26,i6,w18,i9,w17,i7] [n4_220] (by decide +kernel)
def n3_452 := certify 6 [i2,i5,i6,i8,i9,w14,w33,w37] [n4_206,n4_212] (by decide +kernel)
def n3_453 := certify 6 [i2,i5,i6,i8,i9,w17,w28,w37] [n4_207,n4_213,n4_222] (by decide +kernel)
def n3_454 := certify 6 [i2,i5,i6,i8,w13,w19,w17,i7] [n4_214] (by decide +kernel)
def n3_455 := certify 6 [i2,i5,i6,i8,w13,i10,w33,w37] [n4_215,n4_306] (by decide +kernel)
def n3_456 := certify 6 [i2,i5,i6,i8,w19,i10,w28,w33] [n4_303] (by decide +kernel)
def n3_457 := certify 6 [i2,i5,i6,i8,w19,w14,w17,i7] [] (by decide +kernel)
def n3_458 := certify 6 [i2,i5,i6,i8,w19,w17,w58,i7] [n4_305] (by decide +kernel)
def n3_459 := certify 6 [i2,i5,i6,i8,w19,w17,i7,w28] [n4_208,n4_209,n4_221,n4_304] (by decide +kernel)
def n3_460 := certify 6 [i2,i5,i6,w18,i9,i10,w28,w33] [] (by decide +kernel)
def n3_461 := certify 6 [i2,i5,i6,w18,i9,w14,w17,i7] [] (by decide +kernel)
def n3_462 := certify 6 [i2,i5,i6,w18,i9,w14,i7,w33] [n4_205,n4_206,n4_210,n4_224,n4_307] (by decide +kernel)
def n3_463 := certify 6 [i2,i5,i6,w18,i9,w17,w58,i7] [n4_309] (by decide +kernel)
def n3_464 := certify 6 [i2,i5,i6,w18,i9,w17,i7,w28] [n4_207,n4_211,n4_225,n4_308] (by decide +kernel)
def n3_465 := certify 6 [i2,w26,w34,i6,i8,i9,w17,i7] [n4_218,n4_219] (by decide +kernel)
def n3_466 := certify 6 [i3,w25,i4,i6,i8,w20,w16,i7] [n4_282] (by decide +kernel)
def n3_467 := certify 6 [i3,w25,i4,i6,w15,w20,i10,i7] [n4_283] (by decide +kernel)
def n3_468 := certify 6 [i3,w25,i5,i6,i8,w19,w16,i7] [n4_284] (by decide +kernel)
def n3_469 := certify 6 [i3,w29,i4,i5,w21,i9,w14,i7] [n4_288] (by decide +kernel)
def n3_470 := certify 6 [i3,w29,i4,i5,w21,w13,i10,i7] [n4_289] (by decide +kernel)
def n3_471 := certify 6 [i3,w29,i5,i6,w18,i9,w14,i7] [n4_290] (by decide +kernel)
def n3_472 := certify 6 [i3,w36,i5,i6,w15,w13,i10,i7] [n4_251,n4_258,n4_269] (by decide +kernel)
def n3_473 := certify 6 [i3,i4,i5,i6,i8,i9,w14,w52] [n4_229,n4_253] (by decide +kernel)
def n3_474 := certify 6 [i3,i4,i5,i6,i8,i9,w16,w47] [n4_235,n4_250] (by decide +kernel)
def n3_475 := certify 6 [i3,i4,i5,i6,i8,w45,w16,i7] [n4_236] (by decide +kernel)
def n3_476 := certify 6 [i3,i4,i5,i6,i8,w13,i10,w52] [n4_230] (by decide +kernel)
def n3_477 := certify 6 [i3,i4,i5,i6,i8,i10,w32,w65] [n4_226,n4_231] (by decide +kernel)
def n3_478 := certify 6 [i3,i4,i5,i6,i8,w14,w32,w41] [n4_232,n4_254] (by decide +kernel)
def n3_479 := certify 6 [i3,i4,i5,i6,w50,i9,w14,i7] [n4_233] (by decide +kernel)
def n3_480 := certify 6 [i3,i4,i5,i6,w50,w13,i10,i7] [n4_234] (by decide +kernel)
def n3_481 := certify 6 [i3,i4,i5,i6,w15,i9,i10,w47] [n4_238] (by decide +kernel)
def n3_482 := certify 6 [i3,i4,i5,i6,w15,w45,i10,i7] [n4_239] (by decide +kernel)
def n3_483 := certify 6 [i3,i4,i5,i6,w15,w13,i10,i7] [] (by decide +kernel)
def n3_484 := certify 6 [i3,i4,i5,i6,w15,w13,w24,i7] [] (by decide +kernel)
def n3_485 := certify 6 [i3,i4,i5,i6,w15,w13,w14,i7] [] (by decide +kernel)
def n3_486 := certify 6 [i3,i4,i5,i6,w15,w13,w16,i7] [] (by decide +kernel)
def n3_487 := certify 6 [i3,i4,i5,i6,w15,w13,w17,i7] [] (by decide +kernel)
def n3_488 := certify 6 [i3,i4,i5,i6,w15,w13,i7,w42] [n4_227,n4_237,n4_252] (by decide +kernel)
def n3_489 := certify 6 [i3,i4,i5,i6,w15,w63,i10,i7] [n4_270] (by decide +kernel)
def n3_490 := certify 6 [i3,i4,i5,i6,w15,i10,i7,w65] [n4_226,n4_228,n4_291] (by decide +kernel)
def n3_491 := certify 6 [i3,i4,i5,i6,w68,w13,i10,i7] [n4_259] (by decide +kernel)
def n3_492 := certify 6 [i3,i4,i5,i6,i9,i10,w28,w70] [n4_226,n4_241] (by decide +kernel)
def n3_493 := certify 6 [i3,i4,i5,i6,i9,w16,w28,w40] [n4_242,n4_255] (by decide +kernel)
def n3_494 := certify 6 [i3,i4,i5,i6,w13,i10,i7,w70] [n4_226,n4_240,n4_292] (by decide +kernel)
def n3_495 := certify 6 [i3,i4,i5,w49,i8,i9,w14,i7] [n4_233,n4_256] (by decide +kernel)
def n3_496 := certify 6 [i3,i4,i5,w49,i8,w13,i10,i7] [n4_234] (by decide +kernel)
def n3_497 := certify 6 [i3,i4,i5,w30,w21,i9,w14,i7] [n4_257] (by decide +kernel)
def n3_498 := certify 6 [i3,i4,i5,w30,w21,w13,i10,i7] [] (by decide +kernel)
def n3_499 := certify 6 [i3,i4,i5,i8,i9,w14,w32,w39] [n4_262] (by decide +kernel)
def n3_500 := certify 6 [i3,i4,i5,i8,i9,w16,w28,w39] [n4_243,n4_260] (by decide +kernel)
def n3_501 := certify 6 [i3,i4,i5,i8,w13,i10,w32,w39] [] (by decide +kernel)
def n3_502 := certify 6 [i3,i4,i5,w15,w21,i9,w14,i7] [] (by decide +kernel)
def n3_503 := certify 6 [i3,i4,i5,w15,w21,w13,i10,i7] [] (by decide +kernel)
def n3_504 := certify 6 [i3,i4,i5,w15,i9,i10,w28,w39] [n4_228,n4_245] (by decide +kernel)
def n3_505 := certify 6 [i3,i4,i5,w15,w13,i10,i7,w39] [n4_227,n4_228,n4_244,n4_261,n4_293] (by decide +kernel)
def n3_506 := certify 6 [i3,i4,i5,w21,w68,i9,w14,i7] [n4_265] (by decide +kernel)
def n3_507 := certify 6 [i3,i4,i5,w21,w68,w13,i10,i7] [n4_266] (by decide +kernel)
def n3_508 := certify 6 [i3,i4,i5,w21,i9,i10,w28,w32] [n4_231,n4_248,n4_295] (by decide +kernel)
def n3_509 := certify 6 [i3,i4,i5,w21,i9,w14,w16,i7] [n4_249] (by decide +kernel)
def n3_510 := certify 6 [i3,i4,i5,w21,i9,w14,i7,w32] [n4_232,n4_246,n4_263,n4_294] (by decide +kernel)
def n3_511 := certify 6 [i3,i4,i5,w21,w13,i10,i7,w32] [n4_231,n4_247,n4_264,n4_297] (by decide +kernel)
def n3_512 := certify 6 [i3,i4,w44,i6,i8,i9,w16,i7] [n4_236,n4_267] (by decide +kernel)
def n3_513 := certify 6 [i3,i4,w44,i6,w15,i9,i10,i7] [n4_239] (by decide +kernel)
def n3_514 := certify 6 [i3,i4,w26,i6,i8,w20,w16,i7] [n4_268] (by decide +kernel)
def n3_515 := certify 6 [i3,i4,w26,i6,w15,w20,i10,i7] [] (by decide +kernel)
def n3_516 := certify 6 [i3,i4,i6,i8,i9,w14,w32,w38] [n4_246,n4_277] (by decide +kernel)
def n3_517 := certify 6 [i3,i4,i6,i8,i9,w16,w28,w38] [n4_271] (by decide +kernel)
def n3_518 := certify 6 [i3,i4,i6,i8,w13,w20,w16,i7] [] (by decide +kernel)
def n3_519 := certify 6 [i3,i4,i6,i8,w13,i10,w32,w38] [n4_240,n4_247] (by decide +kernel)
def n3_520 := certify 6 [i3,i4,i6,i8,w20,w63,w16,i7] [n4_273] (by decide +kernel)
def n3_521 := certify 6 [i3,i4,i6,i8,w20,i10,w28,w32] [n4_241,n4_248,n4_299] (by decide +kernel)
def n3_522 := certify 6 [i3,i4,i6,i8,w20,w14,w16,i7] [n4_249] (by decide +kernel)
def n3_523 := certify 6 [i3,i4,i6,i8,w20,w16,i7,w28] [n4_242,n4_243,n4_272,n4_298] (by decide +kernel)
def n3_524 := certify 6 [i3,i4,i6,w15,i9,i10,w28,w38] [] (by decide +kernel)
def n3_525 := certify 6 [i3,i4,i6,w15,w13,w20,i10,i7] [] (by decide +kernel)
def n3_526 := certify 6 [i3,i4,i6,w15,w13,i10,i7,w38] [n4_237,n4_240,n4_244,n4_274,n4_301] (by decide +kernel)
def n3_527 := certify 6 [i3,i4,i6,w15,w20,w63,i10,i7] [n4_276] (by decide +kernel)
def n3_528 := certify 6 [i3,i4,i6,w15,w20,i10,i7,w28] [n4_241,n4_245,n4_275,n4_302] (by decide +kernel)
def n3_529 := certify 6 [i3,i5,w26,i6,i8,w19,w16,i7] [n4_268] (by decide +kernel)
def n3_530 := certify 6 [i3,i5,w34,i6,w15,w13,i10,i7] [n4_270] (by decide +kernel)
def n3_531 := certify 6 [i3,i5,i6,w30,w18,i9,w14,i7] [n4_257] (by decide +kernel)
def n3_532 := certify 6 [i3,i5,i6,w35,w15,w13,i10,i7] [n4_259] (by decide +kernel)
def n3_533 := certify 6 [i3,i5,i6,i8,i9,w14,w32,w37] [n4_263] (by decide +kernel)
def n3_534 := certify 6 [i3,i5,i6,i8,i9,w16,w28,w37] [n4_272] (by decide +kernel)
def n3_535 := certify 6 [i3,i5,i6,i8,w13,w19,w16,i7] [] (by decide +kernel)
def n3_536 := certify 6 [i3,i5,i6,i8,w13,i10,w32,w37] [n4_264] (by decide +kernel)
def n3_537 := certify 6 [i3,i5,i6,i8,w19,i10,w28,w32] [n4_304] (by decide +kernel)
def n3_538 := certify 6 [i3,i5,i6,i8,w19,w14,w16,i7] [] (by decide +kernel)
def n3_539 := certify 6 [i3,i5,i6,i8,w19,w16,i7,w28] [n4_255,n4_260,n4_271,n4_303] (by decide +kernel)
def n3_540 := certify 6 [i3,i5,i6,w15,w18,i9,w14,i7] [] (by decide +kernel)
def n3_541 := certify 6 [i3,i5,i6,w15,w18,w13,i10,i7] [] (by decide +kernel)
def n3_542 := certify 6 [i3,i5,i6,w15,i9,i10,w28,w37] [n4_275] (by decide +kernel)
def n3_543 := certify 6 [i3,i5,i6,w15,w13,w19,i10,i7] [] (by decide +kernel)
def n3_544 := certify 6 [i3,i5,i6,w15,w13,i10,i7,w37] [n4_252,n4_261,n4_274,n4_306] (by decide +kernel)
def n3_545 := certify 6 [i3,i5,i6,w18,i9,i10,w28,w32] [n4_308] (by decide +kernel)
def n3_546 := certify 6 [i3,i5,i6,w18,i9,w14,w16,i7] [] (by decide +kernel)
def n3_547 := certify 6 [i3,i5,i6,w18,i9,w14,i7,w32] [n4_254,n4_262,n4_277,n4_307] (by decide +kernel)
def n3_548 := certify 6 [i3,i5,w30,w35,i8,i9,w14,i7] [n4_257] (by decide +kernel)
def n3_549 := certify 6 [i3,i5,w30,w35,i8,w13,i10,i7] [n4_259] (by decide +kernel)
def n3_550 := certify 6 [i3,w26,w34,i6,i8,i9,w16,i7] [n4_268] (by decide +kernel)
def n3_551 := certify 6 [i3,w26,w34,i6,w15,i9,i10,i7] [n4_270] (by decide +kernel)
def n3_552 := certify 6 [w43,i4,i5,i6,i8,i9,w16,i7] [n4_278,n4_280] (by decide +kernel)
def n3_553 := certify 6 [w43,i4,i5,i6,w15,i9,i10,i7] [n4_279] (by decide +kernel)
def n3_554 := certify 6 [w25,w29,i4,i5,w21,i9,i10,i7] [n4_281,n4_288] (by decide +kernel)
def n3_555 := certify 6 [w25,w29,i4,i6,i8,w20,i10,i7] [n4_281,n4_282] (by decide +kernel)
def n3_556 := certify 6 [w25,w29,i5,i6,i8,w19,i10,i7] [n4_284] (by decide +kernel)
def n3_557 := certify 6 [w25,w29,i5,i6,w18,i9,i10,i7] [n4_290] (by decide +kernel)
def n3_558 := certify 6 [w25,i4,i5,i6,i8,i9,w59,i7] [n4_282,n4_284] (by decide +kernel)
def n3_559 := certify 6 [w25,i4,i5,i6,w15,i9,w17,i7] [n4_283] (by decide +kernel)
def n3_560 := certify 6 [w48,i4,i5,i6,i8,i9,w14,i7] [n4_285,n4_287] (by decide +kernel)
def n3_561 := certify 6 [w48,i4,i5,i6,i8,w13,i10,i7] [n4_286] (by decide +kernel)
def n3_562 := certify 6 [w29,i4,i5,i6,i8,i9,w58,i7] [n4_288,n4_290] (by decide +kernel)
def n3_563 := certify 6 [w29,i4,i5,i6,i8,w13,w17,i7] [n4_289] (by decide +kernel)
def n3_564 := certify 6 [i4,i5,i6,i8,i9,w14,w32,w33] [n4_294,n4_307] (by decide +kernel)
def n3_565 := certify 6 [i4,i5,i6,i8,i9,w16,w28,w33] [n4_298,n4_303] (by decide +kernel)
def n3_566 := certify 6 [i4,i5,i6,i8,i9,w17,w28,w32] [n4_295,n4_299,n4_304,n4_308] (by decide +kernel)
def n3_567 := certify 6 [i4,i5,i6,i8,i9,w58,w59,i7] [n4_296,n4_300,n4_305,n4_309] (by decide +kernel)
def n3_568 := certify 6 [i4,i5,i6,i8,w13,i10,w32,w33] [n4_292,n4_297] (by decide +kernel)
def n3_569 := certify 6 [i4,i5,i6,w15,i9,i10,w28,w33] [n4_291,n4_302] (by decide +kernel)
def n3_570 := certify 6 [i4,i5,i6,w15,w13,i10,i7,w33] [n4_291,n4_292,n4_293,n4_301,n4_306] (by decide +kernel)
def n2_0 := certify 7 [iZero,i1,i2,i3,i4,w21,w20,i10,i7] [n3_0,n3_25] (by decide +kernel)
def n2_1 := certify 7 [iZero,i1,i2,i4,i5,w21,i9,w17,i7] [n3_0,n3_71] (by decide +kernel)
def n2_2 := certify 7 [iZero,i1,i2,i4,i6,i8,w20,w17,i7] [n3_0,n3_79] (by decide +kernel)
def n2_3 := certify 7 [iZero,i1,i2,i5,i6,i8,w19,w17,i7] [n3_102] (by decide +kernel)
def n2_4 := certify 7 [iZero,i1,i2,i5,i6,w18,i9,w17,i7] [n3_108] (by decide +kernel)
def n2_5 := certify 7 [iZero,i1,i3,i4,i6,i8,w20,w16,i7] [n3_163] (by decide +kernel)
def n2_6 := certify 7 [iZero,i1,i3,i4,i6,w15,w20,i10,i7] [n3_170] (by decide +kernel)
def n2_7 := certify 7 [iZero,i1,i3,i5,i6,i8,w19,w16,i7] [n3_198] (by decide +kernel)
def n2_8 := certify 7 [iZero,i2,i3,i4,i5,w21,i9,w14,i7] [n3_320] (by decide +kernel)
def n2_9 := certify 7 [iZero,i2,i3,i4,i5,w21,w13,i10,i7] [n3_324] (by decide +kernel)
def n2_10 := certify 7 [iZero,i2,i3,i5,i6,w18,i9,w14,i7] [n3_367] (by decide +kernel)
def n2_11 := certify 7 [iZero,i3,i4,i5,i6,w15,w13,i10,i7] [n3_483] (by decide +kernel)
def n2_12 := certify 7 [i0,i1,i2,i3,i4,w21,w20,i10,i7] [n3_1] (by decide +kernel)
def n2_13 := certify 7 [i0,i1,i2,i4,i5,w21,i9,w17,i7] [n3_1] (by decide +kernel)
def n2_14 := certify 7 [i0,i1,i2,i4,i6,i8,w20,w17,i7] [n3_1] (by decide +kernel)
def n2_15 := certify 7 [i0,i1,i2,i5,i6,i8,w19,w17,i7] [] (by decide +kernel)
def n2_16 := certify 7 [i0,i1,i2,i5,i6,w18,i9,w17,i7] [] (by decide +kernel)
def n2_17 := certify 7 [i0,i1,i3,i4,i6,i8,w20,w16,i7] [] (by decide +kernel)
def n2_18 := certify 7 [i0,i1,i3,i4,i6,w15,w20,i10,i7] [] (by decide +kernel)
def n2_19 := certify 7 [i0,i1,i3,i5,i6,i8,w19,w16,i7] [n3_204] (by decide +kernel)
def n2_20 := certify 7 [i0,i2,i3,i4,i5,w21,i9,w14,i7] [] (by decide +kernel)
def n2_21 := certify 7 [i0,i2,i3,i4,i5,w21,w13,i10,i7] [] (by decide +kernel)
def n2_22 := certify 7 [i0,i2,i3,i5,i6,w18,i9,w14,i7] [n3_370] (by decide +kernel)
def n2_23 := certify 7 [i0,i3,i4,i5,i6,w15,w13,i10,i7] [n3_484] (by decide +kernel)
def n2_24 := certify 7 [w27,i2,i3,i4,i5,w21,i9,i10,i7] [n3_2,n3_3,n3_318,n3_319,n3_323,n3_335,n3_412] (by decide +kernel)
def n2_25 := certify 7 [w27,i2,i3,i4,i6,i8,w20,i10,i7] [n3_2,n3_4,n3_7,n3_8,n3_339,n3_340,n3_341,n3_413] (by decide +kernel)
def n2_26 := certify 7 [w27,i2,i3,i5,i6,i8,w19,i10,i7] [n3_5,n3_9,n3_361,n3_362,n3_396,n3_414] (by decide +kernel)
def n2_27 := certify 7 [w27,i2,i3,i5,i6,w18,i9,i10,i7] [n3_6,n3_365,n3_366,n3_397,n3_415] (by decide +kernel)
def n2_28 := certify 7 [w27,i2,i4,i5,i6,i8,i9,w17,i7] [n3_3,n3_4,n3_5,n3_6,n3_421,n3_422,n3_423,n3_439] (by decide +kernel)
def n2_29 := certify 7 [w27,i3,i4,i5,i6,i8,i9,w16,i7] [n3_7,n3_9,n3_474,n3_475,n3_512,n3_552] (by decide +kernel)
def n2_30 := certify 7 [w27,i3,i4,i5,i6,w15,i9,i10,i7] [n3_8,n3_481,n3_482,n3_513,n3_553] (by decide +kernel)
def n2_31 := certify 7 [i1,w31,i3,i4,i5,w21,i9,i10,i7] [n3_10,n3_11,n3_156,n3_157,n3_159,n3_250,n3_304,n3_305] (by decide +kernel)
def n2_32 := certify 7 [i1,w31,i3,i4,i6,i8,w20,i10,i7] [n3_10,n3_12,n3_161,n3_162,n3_168,n3_181,n3_251] (by decide +kernel)
def n2_33 := certify 7 [i1,w31,i3,i5,i6,i8,w19,i10,i7] [n3_13,n3_196,n3_197,n3_215,n3_252] (by decide +kernel)
def n2_34 := certify 7 [i1,w31,i3,i5,i6,w18,i9,i10,i7] [n3_14,n3_209,n3_210,n3_216,n3_253,n3_306] (by decide +kernel)
def n2_35 := certify 7 [i1,w31,i4,i5,i6,i8,i9,w17,i7] [n3_11,n3_12,n3_13,n3_14,n3_258,n3_259,n3_262,n3_266] (by decide +kernel)
def n2_36 := certify 7 [i1,i2,i3,w36,i5,w21,i9,i10,i7] [n3_15,n3_39,n3_41,n3_42,n3_43,n3_64,n3_308,n3_309] (by decide +kernel)
def n2_37 := certify 7 [i1,i2,i3,w36,i6,i8,w20,i10,i7] [n3_15,n3_46,n3_48,n3_49,n3_53,n3_65,n3_146,n3_147] (by decide +kernel)
def n2_38 := certify 7 [i1,i2,i3,i4,i5,i6,i8,w41,w42] [n3_16,n3_19,n3_31,n3_32,n3_66,n3_148,n3_149] (by decide +kernel)
def n2_39 := certify 7 [i1,i2,i3,i4,i5,i6,i9,w40,w42] [n3_17,n3_20,n3_33,n3_34,n3_67,n3_310,n3_311] (by decide +kernel)
def n2_40 := certify 7 [i1,i2,i3,i4,i5,i6,i10,w40,w41] [n3_18,n3_21,n3_68,n3_150,n3_151,n3_312,n3_313] (by decide +kernel)
def n2_41 := certify 7 [i1,i2,i3,i4,i5,i8,i9,w42,w39] [n3_17,n3_22,n3_35,n3_37,n3_69,n3_152,n3_154,n3_314,n3_315] (by decide +kernel)
def n2_42 := certify 7 [i1,i2,i3,i4,i5,i8,i10,w41,w39] [n3_18,n3_23,n3_36,n3_38,n3_70,n3_153,n3_155,n3_316,n3_317] (by decide +kernel)
def n2_43 := certify 7 [i1,i2,i3,i4,i5,w21,i9,i10,i7] [n3_25,n3_71,n3_320,n3_324] (by decide +kernel)
def n2_44 := certify 7 [i1,i2,i3,i4,i5,w21,i9,w14,i7] [n3_320,n3_325] (by decide +kernel)
def n2_45 := certify 7 [i1,i2,i3,i4,i5,w21,i9,w17,i7] [n3_26,n3_71,n3_254,n3_321,n3_326,n3_416] (by decide +kernel)
def n2_46 := certify 7 [i1,i2,i3,i4,i5,w21,i9,i7,w42] [n3_16,n3_17,n3_24,n3_27,n3_40,n3_72,n3_322,n3_327] (by decide +kernel)
def n2_47 := certify 7 [i1,i2,i3,i4,i5,w21,w13,i10,i7] [n3_324,n3_325] (by decide +kernel)
def n2_48 := certify 7 [i1,i2,i3,i4,i5,w21,w20,i10,i7] [n3_25,n3_44,n3_73,n3_328,n3_329,n3_336] (by decide +kernel)
def n2_49 := certify 7 [i1,i2,i3,i4,i5,w21,i10,i7,w41] [n3_16,n3_18,n3_28,n3_74,n3_75,n3_158,n3_330,n3_331] (by decide +kernel)
def n2_50 := certify 7 [i1,i2,i3,i4,i5,i9,i10,i7,w72] [n3_17,n3_18,n3_29,n3_30,n3_76,n3_77,n3_332,n3_333,n3_334] (by decide +kernel)
def n2_51 := certify 7 [i1,i2,i3,i4,i6,i8,i9,w38,w42] [n3_19,n3_24,n3_45,n3_50,n3_78,n3_160,n3_169,n3_337,n3_338] (by decide +kernel)
def n2_52 := certify 7 [i1,i2,i3,i4,i6,i8,w20,i10,i7] [n3_25,n3_79,n3_163,n3_170] (by decide +kernel)
def n2_53 := certify 7 [i1,i2,i3,i4,i6,i8,w20,w16,i7] [n3_163,n3_171] (by decide +kernel)
def n2_54 := certify 7 [i1,i2,i3,i4,i6,i8,w20,w17,i7] [n3_26,n3_79,n3_164,n3_172,n3_255,n3_417] (by decide +kernel)
def n2_55 := certify 7 [i1,i2,i3,i4,i6,i8,w20,i7,w42] [n3_19,n3_20,n3_22,n3_27,n3_47,n3_80,n3_165,n3_173] (by decide +kernel)
def n2_56 := certify 7 [i1,i2,i3,i4,i6,i8,i10,i7,w67] [n3_19,n3_21,n3_23,n3_28,n3_81,n3_82,n3_166,n3_167,n3_174] (by decide +kernel)
def n2_57 := certify 7 [i1,i2,i3,i4,i6,w15,w20,i10,i7] [n3_170,n3_171] (by decide +kernel)
def n2_58 := certify 7 [i1,i2,i3,i4,i6,w21,w20,i10,i7] [n3_25,n3_54,n3_83,n3_175,n3_176,n3_182] (by decide +kernel)
def n2_59 := certify 7 [i1,i2,i3,i4,i6,i9,i10,w38,w40] [n3_21,n3_29,n3_51,n3_52,n3_84,n3_177,n3_178,n3_342,n3_343] (by decide +kernel)
def n2_60 := certify 7 [i1,i2,i3,i4,i6,w20,i10,i7,w40] [n3_20,n3_21,n3_30,n3_85,n3_86,n3_179,n3_180,n3_344] (by decide +kernel)
def n2_61 := certify 7 [i1,i2,i3,i4,i8,w21,w20,i10,i7] [n3_2,n3_25,n3_57,n3_87,n3_186] (by decide +kernel)
def n2_62 := certify 7 [i1,i2,i3,i4,i8,i9,i10,w38,w39] [n3_23,n3_29,n3_55,n3_58,n3_88,n3_183,n3_187,n3_345,n3_346] (by decide +kernel)
def n2_63 := certify 7 [i1,i2,i3,i4,i8,w20,i10,i7,w39] [n3_22,n3_23,n3_30,n3_56,n3_89,n3_90,n3_184,n3_185,n3_188,n3_347] (by decide +kernel)
def n2_64 := certify 7 [i1,i2,i3,i4,w21,i9,w20,i10,i7] [n3_10,n3_25,n3_61,n3_91,n3_350] (by decide +kernel)
def n2_65 := certify 7 [i1,i2,i3,i4,w21,i9,i10,i7,w38] [n3_24,n3_28,n3_29,n3_60,n3_92,n3_93,n3_190,n3_348,n3_349,n3_351] (by decide +kernel)
def n2_66 := certify 7 [i1,i2,i3,i4,w21,w20,i10,i7] [n3_2,n3_10,n3_15,n3_26,n3_27,n3_28,n3_30,n3_59,n3_62,n3_63,n3_94,n3_95,n3_96,n3_145,n3_189,n3_191,n3_192,n3_307,n3_352,n3_353,n3_354] (by decide +kernel)
def n2_67 := certify 7 [i1,i2,i3,i4,w21,w20,i10,i7,iOnes] [n3_25,n3_97] (by decide +kernel)
def n2_68 := certify 7 [i1,i2,i3,i5,w34,w21,i9,i10,i7] [n3_44,n3_98,n3_355,n3_356,n3_398] (by decide +kernel)
def n2_69 := certify 7 [i1,i2,i3,i5,i6,i8,i9,i10,w57] [n3_39,n3_46,n3_99,n3_193,n3_205,n3_357,n3_359] (by decide +kernel)
def n2_70 := certify 7 [i1,i2,i3,i5,i6,i8,i9,w37,w42] [n3_31,n3_33,n3_40,n3_47,n3_100,n3_194,n3_206,n3_358,n3_360] (by decide +kernel)
def n2_71 := certify 7 [i1,i2,i3,i5,i6,i8,w56,i10,i7] [n3_41,n3_48,n3_101,n3_195,n3_207] (by decide +kernel)
def n2_72 := certify 7 [i1,i2,i3,i5,i6,i8,w19,i10,i7] [n3_102,n3_198] (by decide +kernel)
def n2_73 := certify 7 [i1,i2,i3,i5,i6,i8,w19,w16,i7] [n3_198,n3_208] (by decide +kernel)
def n2_74 := certify 7 [i1,i2,i3,i5,i6,i8,w19,w17,i7] [n3_102,n3_199,n3_256,n3_418] (by decide +kernel)
def n2_75 := certify 7 [i1,i2,i3,i5,i6,i8,w19,i7,w42] [n3_31,n3_34,n3_35,n3_45,n3_103,n3_200] (by decide +kernel)
def n2_76 := certify 7 [i1,i2,i3,i5,i6,i8,w64,i10,i7] [n3_104,n3_201,n3_399] (by decide +kernel)
def n2_77 := certify 7 [i1,i2,i3,i5,i6,i8,i10,i7,w66] [n3_31,n3_36,n3_105,n3_106,n3_202,n3_203] (by decide +kernel)
def n2_78 := certify 7 [i1,i2,i3,i5,i6,w22,w19,i10,i7] [n3_204] (by decide +kernel)
def n2_79 := certify 7 [i1,i2,i3,i5,i6,w15,w19,i10,i7] [n3_208] (by decide +kernel)
def n2_80 := certify 7 [i1,i2,i3,i5,i6,w55,i9,i10,i7] [n3_42,n3_49,n3_107,n3_363,n3_364] (by decide +kernel)
def n2_81 := certify 7 [i1,i2,i3,i5,i6,w18,i9,i10,i7] [n3_108,n3_367] (by decide +kernel)
def n2_82 := certify 7 [i1,i2,i3,i5,i6,w18,i9,w14,i7] [n3_367,n3_371] (by decide +kernel)
def n2_83 := certify 7 [i1,i2,i3,i5,i6,w18,i9,w17,i7] [n3_108,n3_257,n3_368,n3_419] (by decide +kernel)
def n2_84 := certify 7 [i1,i2,i3,i5,i6,w18,i9,i7,w42] [n3_32,n3_33,n3_37,n3_50,n3_109,n3_369] (by decide +kernel)
def n2_85 := certify 7 [i1,i2,i3,i5,i6,w18,w23,i10,i7] [n3_370] (by decide +kernel)
def n2_86 := certify 7 [i1,i2,i3,i5,i6,w18,w13,i10,i7] [n3_371] (by decide +kernel)
def n2_87 := certify 7 [i1,i2,i3,i5,i6,w18,w19,i10,i7] [n3_110,n3_211,n3_372] (by decide +kernel)
def n2_88 := certify 7 [i1,i2,i3,i5,i6,w18,w20,i10,i7] [n3_111,n3_373,n3_400] (by decide +kernel)
def n2_89 := certify 7 [i1,i2,i3,i5,i6,w18,i10,i7,w41] [n3_32,n3_38,n3_112,n3_113,n3_212,n3_374] (by decide +kernel)
def n2_90 := certify 7 [i1,i2,i3,i5,i6,w21,w19,i10,i7] [n3_114,n3_213,n3_217] (by decide +kernel)
def n2_91 := certify 7 [i1,i2,i3,i5,i6,w69,i9,i10,i7] [n3_115,n3_218,n3_375] (by decide +kernel)
def n2_92 := certify 7 [i1,i2,i3,i5,i6,i9,i10,i7,w71] [n3_33,n3_51,n3_116,n3_117,n3_376,n3_377] (by decide +kernel)
def n2_93 := certify 7 [i1,i2,i3,i5,i6,w19,i10,i7,w40] [n3_34,n3_52,n3_118,n3_119,n3_214,n3_378] (by decide +kernel)
def n2_94 := certify 7 [i1,i2,i3,i5,w54,i8,i9,i10,i7] [n3_42,n3_53,n3_120,n3_219,n3_220,n3_379,n3_380] (by decide +kernel)
def n2_95 := certify 7 [i1,i2,i3,i5,w35,w21,i9,i10,i7] [n3_54,n3_121,n3_221,n3_222,n3_381,n3_382] (by decide +kernel)
def n2_96 := certify 7 [i1,i2,i3,i5,i8,i9,i10,w37,w39] [n3_36,n3_56,n3_122,n3_223,n3_226,n3_383,n3_384] (by decide +kernel)
def n2_97 := certify 7 [i1,i2,i3,i5,i8,w19,i10,i7,w39] [n3_35,n3_36,n3_55,n3_123,n3_124,n3_224,n3_225,n3_385] (by decide +kernel)
def n2_98 := certify 7 [i1,i2,i3,i5,w18,w21,i9,i10,i7] [n3_57,n3_125,n3_386,n3_387] (by decide +kernel)
def n2_99 := certify 7 [i1,i2,i3,i5,w18,i9,i10,i7,w39] [n3_37,n3_38,n3_58,n3_126,n3_127,n3_227,n3_388,n3_389] (by decide +kernel)
def n2_100 := certify 7 [i1,i2,i3,i5,w21,w69,i9,i10,i7] [n3_59,n3_128,n3_229,n3_390,n3_391] (by decide +kernel)
def n2_101 := certify 7 [i1,i2,i3,i5,w21,i9,w19,i10,i7] [n3_61,n3_129,n3_394] (by decide +kernel)
def n2_102 := certify 7 [i1,i2,i3,i5,w21,i9,i10,i7,w37] [n3_40,n3_60,n3_63,n3_130,n3_131,n3_228,n3_392,n3_393,n3_395] (by decide +kernel)
def n2_103 := certify 7 [i1,i2,i3,w53,i6,i8,i9,i10,i7] [n3_43,n3_48,n3_132,n3_230,n3_231,n3_401,n3_402] (by decide +kernel)
def n2_104 := certify 7 [i1,i2,i3,w34,i6,i8,w20,i10,i7] [n3_44,n3_133,n3_232,n3_233,n3_403,n3_404] (by decide +kernel)
def n2_105 := certify 7 [i1,i2,i3,i6,w35,i8,w20,i10,i7] [n3_54,n3_134,n3_234,n3_235,n3_249] (by decide +kernel)
def n2_106 := certify 7 [i1,i2,i3,i6,i8,w18,w20,i10,i7] [n3_57,n3_135,n3_243] (by decide +kernel)
def n2_107 := certify 7 [i1,i2,i3,i6,i8,i9,i10,w37,w38] [n3_51,n3_60,n3_136,n3_236,n3_244,n3_405,n3_406] (by decide +kernel)
def n2_108 := certify 7 [i1,i2,i3,i6,i8,w19,w20,i10,i7] [n3_61,n3_137,n3_237,n3_245] (by decide +kernel)
def n2_109 := certify 7 [i1,i2,i3,i6,i8,w19,i10,i7,w38] [n3_45,n3_52,n3_55,n3_138,n3_139,n3_238,n3_239,n3_407] (by decide +kernel)
def n2_110 := certify 7 [i1,i2,i3,i6,i8,w20,w64,i10,i7] [n3_62,n3_140,n3_240,n3_246,n3_409] (by decide +kernel)
def n2_111 := certify 7 [i1,i2,i3,i6,i8,w20,i10,i7,w37] [n3_47,n3_56,n3_63,n3_141,n3_142,n3_241,n3_242,n3_247,n3_408] (by decide +kernel)
def n2_112 := certify 7 [i1,i2,i3,i6,w18,i9,i10,i7,w38] [n3_50,n3_51,n3_58,n3_143,n3_144,n3_248,n3_410,n3_411] (by decide +kernel)
def n2_113 := certify 7 [i1,i2,w36,i5,i6,i8,i9,w17,i7] [n3_64,n3_65,n3_99,n3_101,n3_107,n3_120,n3_132] (by decide +kernel)
def n2_114 := certify 7 [i1,i2,i4,i5,i6,i8,i9,w17,i7] [n3_71,n3_79,n3_102,n3_108] (by decide +kernel)
def n2_115 := certify 7 [i1,i2,i4,i5,i6,i8,i9,i7,w62] [n3_66,n3_67,n3_69,n3_72,n3_78,n3_80,n3_100,n3_103,n3_109] (by decide +kernel)
def n2_116 := certify 7 [i1,i2,i4,i5,i6,i8,w19,w17,i7] [n3_102,n3_110] (by decide +kernel)
def n2_117 := certify 7 [i1,i2,i4,i5,i6,i8,w20,w17,i7] [n3_73,n3_79,n3_104,n3_111,n3_133,n3_440] (by decide +kernel)
def n2_118 := certify 7 [i1,i2,i4,i5,i6,i8,i10,w33,w41] [n3_66,n3_74,n3_81,n3_105,n3_112,n3_260,n3_263,n3_424,n3_425] (by decide +kernel)
def n2_119 := certify 7 [i1,i2,i4,i5,i6,i8,w17,i7,w41] [n3_66,n3_68,n3_70,n3_75,n3_82,n3_106,n3_113,n3_261] (by decide +kernel)
def n2_120 := certify 7 [i1,i2,i4,i5,i6,w18,i9,w17,i7] [n3_108,n3_110] (by decide +kernel)
def n2_121 := certify 7 [i1,i2,i4,i5,i6,w21,i9,w17,i7] [n3_71,n3_83,n3_114,n3_115,n3_121,n3_267] (by decide +kernel)
def n2_122 := certify 7 [i1,i2,i4,i5,i6,i9,i10,w33,w40] [n3_67,n3_76,n3_85,n3_116,n3_118,n3_264,n3_265,n3_426,n3_428] (by decide +kernel)
def n2_123 := certify 7 [i1,i2,i4,i5,i6,i9,w17,i7,w40] [n3_67,n3_68,n3_77,n3_84,n3_86,n3_117,n3_119,n3_427] (by decide +kernel)
def n2_124 := certify 7 [i1,i2,i4,i5,i8,w21,i9,w17,i7] [n3_3,n3_71,n3_87,n3_125,n3_270] (by decide +kernel)
def n2_125 := certify 7 [i1,i2,i4,i5,i8,i9,i10,w33,w39] [n3_69,n3_76,n3_89,n3_123,n3_126,n3_268,n3_271,n3_429,n3_431] (by decide +kernel)
def n2_126 := certify 7 [i1,i2,i4,i5,i8,i9,w17,i7,w39] [n3_69,n3_70,n3_77,n3_88,n3_90,n3_122,n3_124,n3_127,n3_269,n3_430] (by decide +kernel)
def n2_127 := certify 7 [i1,i2,i4,i5,w21,i9,i10,w17,i7] [n3_64,n3_71,n3_94,n3_274,n3_434] (by decide +kernel)
def n2_128 := certify 7 [i1,i2,i4,i5,w21,i9,i10,i7,w33] [n3_72,n3_74,n3_76,n3_92,n3_95,n3_130,n3_273,n3_433,n3_435,n3_438] (by decide +kernel)
def n2_129 := certify 7 [i1,i2,i4,i5,w21,i9,w17,i7] [n3_3,n3_11,n3_64,n3_72,n3_73,n3_75,n3_77,n3_91,n3_93,n3_96,n3_98,n3_128,n3_129,n3_131,n3_272,n3_275,n3_276,n3_420,n3_432,n3_436,n3_437] (by decide +kernel)
def n2_130 := certify 7 [i1,i2,i4,i5,w21,i9,w17,i7,iOnes] [n3_71,n3_97] (by decide +kernel)
def n2_131 := certify 7 [i1,i2,i4,i6,i8,i9,w20,w17,i7] [n3_12,n3_79,n3_91,n3_137,n3_443] (by decide +kernel)
def n2_132 := certify 7 [i1,i2,i4,i6,i8,i9,i10,w33,w38] [n3_78,n3_81,n3_92,n3_138,n3_143,n3_279,n3_286,n3_441,n3_444] (by decide +kernel)
def n2_133 := certify 7 [i1,i2,i4,i6,i8,i9,w17,i7,w38] [n3_78,n3_82,n3_84,n3_88,n3_93,n3_136,n3_139,n3_144,n3_280,n3_442] (by decide +kernel)
def n2_134 := certify 7 [i1,i2,i4,i6,i8,w20,i10,w17,i7] [n3_65,n3_79,n3_94,n3_282,n3_447] (by decide +kernel)
def n2_135 := certify 7 [i1,i2,i4,i6,i8,w20,i10,i7,w33] [n3_80,n3_81,n3_85,n3_89,n3_95,n3_141,n3_281,n3_283,n3_287,n3_446] (by decide +kernel)
def n2_136 := certify 7 [i1,i2,i4,i6,i8,w20,w17,i7] [n3_4,n3_12,n3_65,n3_80,n3_82,n3_83,n3_86,n3_87,n3_90,n3_96,n3_134,n3_135,n3_140,n3_142,n3_277,n3_278,n3_284,n3_285,n3_445,n3_448,n3_449] (by decide +kernel)
def n2_137 := certify 7 [i1,i2,i4,i6,i8,w20,w17,i7,iOnes] [n3_79,n3_97] (by decide +kernel)
def n2_138 := certify 7 [i1,i2,i5,w34,i6,i8,i9,w17,i7] [n3_98,n3_104,n3_133,n3_465] (by decide +kernel)
def n2_139 := certify 7 [i1,i2,i5,i6,w35,i8,i9,w17,i7] [n3_115,n3_121,n3_134,n3_303] (by decide +kernel)
def n2_140 := certify 7 [i1,i2,i5,i6,i8,w18,i9,w17,i7] [n3_6,n3_108,n3_125,n3_135,n3_297] (by decide +kernel)
def n2_141 := certify 7 [i1,i2,i5,i6,i8,i9,w19,w17,i7] [n3_13,n3_102,n3_129,n3_137,n3_454] (by decide +kernel)
def n2_142 := certify 7 [i1,i2,i5,i6,i8,i9,i10,w33,w37] [n3_100,n3_105,n3_116,n3_130,n3_141,n3_290,n3_298,n3_452,n3_455] (by decide +kernel)
def n2_143 := certify 7 [i1,i2,i5,i6,i8,i9,w17,i7,w37] [n3_100,n3_106,n3_117,n3_122,n3_131,n3_136,n3_142,n3_291,n3_453] (by decide +kernel)
def n2_144 := certify 7 [i1,i2,i5,i6,i8,w19,i10,w17,i7] [n3_102,n3_293,n3_457] (by decide +kernel)
def n2_145 := certify 7 [i1,i2,i5,i6,i8,w19,i10,i7,w33] [n3_103,n3_105,n3_118,n3_123,n3_138,n3_292,n3_294,n3_456] (by decide +kernel)
def n2_146 := certify 7 [i1,i2,i5,i6,i8,w19,w17,i7] [n3_5,n3_13,n3_103,n3_104,n3_106,n3_114,n3_119,n3_124,n3_139,n3_288,n3_295,n3_296,n3_450,n3_458,n3_459] (by decide +kernel)
def n2_147 := certify 7 [i1,i2,i5,i6,i8,w19,w17,i7,iOnes] [n3_102] (by decide +kernel)
def n2_148 := certify 7 [i1,i2,i5,i6,w18,i9,i10,w17,i7] [n3_108,n3_300,n3_461] (by decide +kernel)
def n2_149 := certify 7 [i1,i2,i5,i6,w18,i9,i10,i7,w33] [n3_109,n3_112,n3_116,n3_126,n3_143,n3_299,n3_460,n3_462] (by decide +kernel)
def n2_150 := certify 7 [i1,i2,i5,i6,w18,i9,w17,i7] [n3_6,n3_14,n3_109,n3_111,n3_113,n3_115,n3_117,n3_127,n3_144,n3_289,n3_301,n3_302,n3_451,n3_463,n3_464] (by decide +kernel)
def n2_151 := certify 7 [i1,i2,i5,i6,w18,i9,w17,i7,iOnes] [n3_108] (by decide +kernel)
def n2_152 := certify 7 [i1,i3,w29,i4,i5,w21,i9,i10,i7] [n3_145,n3_254,n3_469,n3_470,n3_554] (by decide +kernel)
def n2_153 := certify 7 [i1,i3,w29,i4,i6,i8,w20,i10,i7] [n3_145,n3_164,n3_255,n3_555] (by decide +kernel)
def n2_154 := certify 7 [i1,i3,w29,i5,i6,i8,w19,i10,i7] [n3_199,n3_256,n3_556] (by decide +kernel)
def n2_155 := certify 7 [i1,i3,w29,i5,i6,w18,i9,i10,i7] [n3_257,n3_471,n3_557] (by decide +kernel)
def n2_156 := certify 7 [i1,i3,w36,i5,i6,i8,i9,w16,i7] [n3_146,n3_193,n3_195,n3_219,n3_230] (by decide +kernel)
def n2_157 := certify 7 [i1,i3,w36,i5,i6,w15,i9,i10,i7] [n3_147,n3_205,n3_207,n3_220,n3_231,n3_472] (by decide +kernel)
def n2_158 := certify 7 [i1,i3,i4,i5,i6,i8,i9,i10,w52] [n3_156,n3_161,n3_196,n3_209,n3_258,n3_473,n3_476] (by decide +kernel)
def n2_159 := certify 7 [i1,i3,i4,i5,i6,i8,i9,w51,i7] [n3_157,n3_162,n3_197,n3_210,n3_259] (by decide +kernel)
def n2_160 := certify 7 [i1,i3,i4,i5,i6,i8,i9,w16,i7] [n3_163,n3_198] (by decide +kernel)
def n2_161 := certify 7 [i1,i3,i4,i5,i6,i8,i9,w59,i7] [n3_164,n3_199,n3_558] (by decide +kernel)
def n2_162 := certify 7 [i1,i3,i4,i5,i6,i8,i9,i7,w61] [n3_148,n3_152,n3_160,n3_165,n3_194,n3_200] (by decide +kernel)
def n2_163 := certify 7 [i1,i3,i4,i5,i6,i8,w19,w16,i7] [n3_198,n3_211] (by decide +kernel)
def n2_164 := certify 7 [i1,i3,i4,i5,i6,i8,w20,w16,i7] [n3_163,n3_201,n3_232,n3_514] (by decide +kernel)
def n2_165 := certify 7 [i1,i3,i4,i5,i6,i8,i10,w32,w41] [n3_148,n3_150,n3_158,n3_166,n3_202,n3_212,n3_261,n3_477,n3_478] (by decide +kernel)
def n2_166 := certify 7 [i1,i3,i4,i5,i6,i8,w16,i7,w41] [n3_148,n3_151,n3_153,n3_167,n3_203,n3_260] (by decide +kernel)
def n2_167 := certify 7 [i1,i3,i4,i5,i6,w22,i9,w16,i7] [n3_204] (by decide +kernel)
def n2_168 := certify 7 [i1,i3,i4,i5,i6,w50,i9,i10,i7] [n3_159,n3_168,n3_262,n3_479,n3_480] (by decide +kernel)
def n2_169 := certify 7 [i1,i3,i4,i5,i6,w15,i9,i10,i7] [n3_170,n3_483] (by decide +kernel)
def n2_170 := certify 7 [i1,i3,i4,i5,i6,w15,i9,w24,i7] [n3_484] (by decide +kernel)
def n2_171 := certify 7 [i1,i3,i4,i5,i6,w15,i9,w14,i7] [n3_485] (by decide +kernel)
def n2_172 := certify 7 [i1,i3,i4,i5,i6,w15,i9,w16,i7] [n3_171,n3_208,n3_486] (by decide +kernel)
def n2_173 := certify 7 [i1,i3,i4,i5,i6,w15,i9,w17,i7] [n3_172,n3_487,n3_559] (by decide +kernel)
def n2_174 := certify 7 [i1,i3,i4,i5,i6,w15,i9,i7,w42] [n3_149,n3_154,n3_169,n3_173,n3_206,n3_488] (by decide +kernel)
def n2_175 := certify 7 [i1,i3,i4,i5,i6,w15,w13,i10,i7] [n3_483,n3_485] (by decide +kernel)
def n2_176 := certify 7 [i1,i3,i4,i5,i6,w15,w20,i10,i7] [n3_170,n3_233,n3_489,n3_515] (by decide +kernel)
def n2_177 := certify 7 [i1,i3,i4,i5,i6,w15,i10,i7,w41] [n3_149,n3_150,n3_155,n3_174,n3_263,n3_490] (by decide +kernel)
def n2_178 := certify 7 [i1,i3,i4,i5,i6,w18,i9,w16,i7] [n3_211] (by decide +kernel)
def n2_179 := certify 7 [i1,i3,i4,i5,i6,w21,i9,w16,i7] [n3_175,n3_213,n3_221] (by decide +kernel)
def n2_180 := certify 7 [i1,i3,i4,i5,i6,w68,i9,i10,i7] [n3_176,n3_222,n3_491] (by decide +kernel)
def n2_181 := certify 7 [i1,i3,i4,i5,i6,i9,i10,i7,w70] [n3_150,n3_177,n3_179,n3_264,n3_492,n3_494] (by decide +kernel)
def n2_182 := certify 7 [i1,i3,i4,i5,i6,i9,w16,i7,w40] [n3_151,n3_178,n3_180,n3_214,n3_265,n3_493] (by decide +kernel)
def n2_183 := certify 7 [i1,i3,i4,i5,w49,i8,i9,i10,i7] [n3_159,n3_181,n3_215,n3_216,n3_266,n3_495,n3_496] (by decide +kernel)
def n2_184 := certify 7 [i1,i3,i4,i5,w30,w21,i9,i10,i7] [n3_182,n3_217,n3_218,n3_267,n3_497,n3_498] (by decide +kernel)
def n2_185 := certify 7 [i1,i3,i4,i5,i8,i9,i10,w32,w39] [n3_152,n3_184,n3_224,n3_227,n3_269,n3_499,n3_501] (by decide +kernel)
def n2_186 := certify 7 [i1,i3,i4,i5,i8,i9,w16,i7,w39] [n3_152,n3_153,n3_183,n3_185,n3_223,n3_225,n3_268,n3_500] (by decide +kernel)
def n2_187 := certify 7 [i1,i3,i4,i5,w15,w21,i9,i10,i7] [n3_186,n3_270,n3_502,n3_503] (by decide +kernel)
def n2_188 := certify 7 [i1,i3,i4,i5,w15,i9,i10,i7,w39] [n3_154,n3_155,n3_187,n3_188,n3_226,n3_271,n3_504,n3_505] (by decide +kernel)
def n2_189 := certify 7 [i1,i3,i4,i5,w21,w68,i9,i10,i7] [n3_189,n3_229,n3_272,n3_506,n3_507] (by decide +kernel)
def n2_190 := certify 7 [i1,i3,i4,i5,w21,i9,i10,w16,i7] [n3_191,n3_274,n3_509] (by decide +kernel)
def n2_191 := certify 7 [i1,i3,i4,i5,w21,i9,i10,i7,w32] [n3_158,n3_190,n3_192,n3_228,n3_273,n3_276,n3_508,n3_510,n3_511] (by decide +kernel)
def n2_192 := certify 7 [i1,i3,i4,i6,w30,i8,w20,i10,i7] [n3_176,n3_182,n3_249,n3_277] (by decide +kernel)
def n2_193 := certify 7 [i1,i3,i4,i6,i8,w15,w20,i10,i7] [n3_8,n3_170,n3_186,n3_243,n3_278] (by decide +kernel)
def n2_194 := certify 7 [i1,i3,i4,i6,i8,i9,w20,w16,i7] [n3_163,n3_237,n3_518] (by decide +kernel)
def n2_195 := certify 7 [i1,i3,i4,i6,i8,i9,i10,w32,w38] [n3_160,n3_166,n3_177,n3_190,n3_238,n3_248,n3_280,n3_516,n3_519] (by decide +kernel)
def n2_196 := certify 7 [i1,i3,i4,i6,i8,i9,w16,i7,w38] [n3_160,n3_167,n3_178,n3_183,n3_236,n3_239,n3_279,n3_517] (by decide +kernel)
def n2_197 := certify 7 [i1,i3,i4,i6,i8,w20,i10,w16,i7] [n3_146,n3_163,n3_191,n3_282,n3_522] (by decide +kernel)
def n2_198 := certify 7 [i1,i3,i4,i6,i8,w20,i10,i7,w32] [n3_165,n3_166,n3_179,n3_184,n3_192,n3_241,n3_281,n3_285,n3_521] (by decide +kernel)
def n2_199 := certify 7 [i1,i3,i4,i6,i8,w20,w16,i7] [n3_7,n3_146,n3_164,n3_165,n3_167,n3_175,n3_180,n3_185,n3_234,n3_240,n3_242,n3_283,n3_466,n3_520,n3_523] (by decide +kernel)
def n2_200 := certify 7 [i1,i3,i4,i6,i8,w20,w16,i7,iOnes] [n3_163] (by decide +kernel)
def n2_201 := certify 7 [i1,i3,i4,i6,w15,i9,w20,i10,i7] [n3_170,n3_245,n3_525] (by decide +kernel)
def n2_202 := certify 7 [i1,i3,i4,i6,w15,i9,i10,i7,w38] [n3_169,n3_174,n3_177,n3_187,n3_244,n3_286,n3_524,n3_526] (by decide +kernel)
def n2_203 := certify 7 [i1,i3,i4,i6,w15,w20,i10,i7] [n3_8,n3_147,n3_172,n3_173,n3_174,n3_176,n3_179,n3_188,n3_235,n3_246,n3_247,n3_287,n3_467,n3_527,n3_528] (by decide +kernel)
def n2_204 := certify 7 [i1,i3,i4,i6,w15,w20,i10,i7,iOnes] [n3_170] (by decide +kernel)
def n2_205 := certify 7 [i1,i3,i5,w34,i6,i8,i9,w16,i7] [n3_201,n3_232,n3_550] (by decide +kernel)
def n2_206 := certify 7 [i1,i3,i5,w34,i6,w15,i9,i10,i7] [n3_233,n3_530,n3_551] (by decide +kernel)
def n2_207 := certify 7 [i1,i3,i5,i6,w30,i8,w19,i10,i7] [n3_217,n3_288] (by decide +kernel)
def n2_208 := certify 7 [i1,i3,i5,i6,w30,w18,i9,i10,i7] [n3_218,n3_289,n3_531] (by decide +kernel)
def n2_209 := certify 7 [i1,i3,i5,i6,w35,i8,i9,w16,i7] [n3_221,n3_234] (by decide +kernel)
def n2_210 := certify 7 [i1,i3,i5,i6,w35,w15,i9,i10,i7] [n3_222,n3_235,n3_532] (by decide +kernel)
def n2_211 := certify 7 [i1,i3,i5,i6,i8,i9,w19,w16,i7] [n3_198,n3_237,n3_535] (by decide +kernel)
def n2_212 := certify 7 [i1,i3,i5,i6,i8,i9,i10,w32,w37] [n3_194,n3_202,n3_228,n3_241,n3_291,n3_533,n3_536] (by decide +kernel)
def n2_213 := certify 7 [i1,i3,i5,i6,i8,i9,w16,i7,w37] [n3_194,n3_203,n3_223,n3_236,n3_242,n3_290,n3_534] (by decide +kernel)
def n2_214 := certify 7 [i1,i3,i5,i6,i8,w19,i10,w16,i7] [n3_198,n3_293,n3_538] (by decide +kernel)
def n2_215 := certify 7 [i1,i3,i5,i6,i8,w19,i10,i7,w32] [n3_200,n3_202,n3_224,n3_238,n3_292,n3_296,n3_537] (by decide +kernel)
def n2_216 := certify 7 [i1,i3,i5,i6,i8,w19,w16,i7] [n3_9,n3_199,n3_200,n3_201,n3_203,n3_213,n3_214,n3_225,n3_239,n3_294,n3_468,n3_529,n3_539] (by decide +kernel)
def n2_217 := certify 7 [i1,i3,i5,i6,i8,w19,w16,i7,iOnes] [n3_198] (by decide +kernel)
def n2_218 := certify 7 [i1,i3,i5,i6,w15,w18,i9,i10,i7] [n3_243,n3_297,n3_540,n3_541] (by decide +kernel)
def n2_219 := certify 7 [i1,i3,i5,i6,w15,i9,w19,i10,i7] [n3_245,n3_543] (by decide +kernel)
def n2_220 := certify 7 [i1,i3,i5,i6,w15,i9,i10,i7,w37] [n3_206,n3_226,n3_244,n3_247,n3_298,n3_542,n3_544] (by decide +kernel)
def n2_221 := certify 7 [i1,i3,i5,i6,w18,i9,i10,w16,i7] [n3_300,n3_546] (by decide +kernel)
def n2_222 := certify 7 [i1,i3,i5,i6,w18,i9,i10,i7,w32] [n3_212,n3_227,n3_248,n3_299,n3_302,n3_545,n3_547] (by decide +kernel)
def n2_223 := certify 7 [i1,i3,i5,w30,w35,i8,i9,i10,i7] [n3_218,n3_222,n3_249,n3_303,n3_548,n3_549] (by decide +kernel)
def n2_224 := certify 7 [i1,w48,i4,i5,i6,i8,i9,i10,i7] [n3_250,n3_251,n3_252,n3_253,n3_259,n3_560,n3_561] (by decide +kernel)
def n2_225 := certify 7 [i1,w29,i4,i5,i6,i8,i9,w17,i7] [n3_254,n3_255,n3_256,n3_257,n3_562,n3_563] (by decide +kernel)
def n2_226 := certify 7 [i1,i4,i5,i6,w30,i8,i9,w17,i7] [n3_267,n3_277,n3_288,n3_289,n3_303] (by decide +kernel)
def n2_227 := certify 7 [i1,i4,i5,i6,i8,w15,i9,w17,i7] [n3_270,n3_278,n3_297] (by decide +kernel)
def n2_228 := certify 7 [i1,i4,i5,i6,i8,i9,i10,w32,w33] [n3_264,n3_273,n3_281,n3_292,n3_299,n3_564,n3_568] (by decide +kernel)
def n2_229 := certify 7 [i1,i4,i5,i6,i8,i9,w16,w17,i7] [n3_274,n3_282,n3_293,n3_300] (by decide +kernel)
def n2_230 := certify 7 [i1,i4,i5,i6,i8,i9,w16,i7,w33] [n3_260,n3_265,n3_268,n3_279,n3_283,n3_290,n3_294,n3_565] (by decide +kernel)
def n2_231 := certify 7 [i1,i4,i5,i6,i8,i9,w17,w59,i7] [n3_275,n3_284,n3_295,n3_301,n3_567] (by decide +kernel)
def n2_232 := certify 7 [i1,i4,i5,i6,i8,i9,w17,i7,w32] [n3_261,n3_269,n3_276,n3_280,n3_285,n3_291,n3_296,n3_302,n3_566] (by decide +kernel)
def n2_233 := certify 7 [i1,i4,i5,i6,w15,i9,i10,i7,w33] [n3_263,n3_264,n3_271,n3_286,n3_287,n3_298,n3_569,n3_570] (by decide +kernel)
def n2_234 := certify 7 [w31,i3,i4,i5,i6,i8,i9,w14,i7] [n3_304,n3_306,n3_473,n3_479,n3_495,n3_560] (by decide +kernel)
def n2_235 := certify 7 [w31,i3,i4,i5,i6,i8,w13,i10,i7] [n3_305,n3_476,n3_480,n3_496,n3_561] (by decide +kernel)
def n2_236 := certify 7 [i2,i3,w25,i4,i5,w21,i9,i10,i7] [n3_307,n3_321,n3_416,n3_554] (by decide +kernel)
def n2_237 := certify 7 [i2,i3,w25,i4,i6,i8,w20,i10,i7] [n3_307,n3_417,n3_466,n3_467,n3_555] (by decide +kernel)
def n2_238 := certify 7 [i2,i3,w25,i5,i6,i8,w19,i10,i7] [n3_418,n3_468,n3_556] (by decide +kernel)
def n2_239 := certify 7 [i2,i3,w25,i5,i6,w18,i9,i10,i7] [n3_368,n3_419,n3_557] (by decide +kernel)
def n2_240 := certify 7 [i2,i3,w36,i5,i6,i8,i9,w14,i7] [n3_308,n3_357,n3_363,n3_379,n3_401] (by decide +kernel)
def n2_241 := certify 7 [i2,i3,w36,i5,i6,i8,w13,i10,i7] [n3_309,n3_359,n3_364,n3_380,n3_402,n3_472] (by decide +kernel)
def n2_242 := certify 7 [i2,i3,i4,i5,w26,w21,i9,i10,i7] [n3_329,n3_336,n3_398,n3_420] (by decide +kernel)
def n2_243 := certify 7 [i2,i3,i4,i5,i6,i8,i9,i10,w47] [n3_318,n3_339,n3_361,n3_365,n3_421,n3_474,n3_481] (by decide +kernel)
def n2_244 := certify 7 [i2,i3,i4,i5,i6,i8,i9,w46,i7] [n3_319,n3_340,n3_362,n3_366,n3_422] (by decide +kernel)
def n2_245 := certify 7 [i2,i3,i4,i5,i6,i8,i9,w14,i7] [n3_320,n3_367] (by decide +kernel)
def n2_246 := certify 7 [i2,i3,i4,i5,i6,i8,i9,w58,i7] [n3_321,n3_368,n3_562] (by decide +kernel)
def n2_247 := certify 7 [i2,i3,i4,i5,i6,i8,i9,i7,w60] [n3_310,n3_314,n3_322,n3_337,n3_358,n3_369] (by decide +kernel)
def n2_248 := certify 7 [i2,i3,i4,i5,i6,i8,w23,w14,i7] [n3_370] (by decide +kernel)
def n2_249 := certify 7 [i2,i3,i4,i5,i6,i8,w45,i10,i7] [n3_323,n3_341,n3_423,n3_475,n3_482] (by decide +kernel)
def n2_250 := certify 7 [i2,i3,i4,i5,i6,i8,w13,i10,i7] [n3_324,n3_483] (by decide +kernel)
def n2_251 := certify 7 [i2,i3,i4,i5,i6,i8,w13,w24,i7] [n3_484] (by decide +kernel)
def n2_252 := certify 7 [i2,i3,i4,i5,i6,i8,w13,w14,i7] [n3_325,n3_371,n3_485] (by decide +kernel)
def n2_253 := certify 7 [i2,i3,i4,i5,i6,i8,w13,w16,i7] [n3_486] (by decide +kernel)
def n2_254 := certify 7 [i2,i3,i4,i5,i6,i8,w13,w17,i7] [n3_326,n3_487,n3_563] (by decide +kernel)
def n2_255 := certify 7 [i2,i3,i4,i5,i6,i8,w13,i7,w42] [n3_311,n3_315,n3_327,n3_338,n3_360,n3_488] (by decide +kernel)
def n2_256 := certify 7 [i2,i3,i4,i5,i6,i8,w19,w14,i7] [n3_372] (by decide +kernel)
def n2_257 := certify 7 [i2,i3,i4,i5,i6,i8,w20,w14,i7] [n3_328,n3_373,n3_403] (by decide +kernel)
def n2_258 := certify 7 [i2,i3,i4,i5,i6,i8,w63,i10,i7] [n3_329,n3_404,n3_489] (by decide +kernel)
def n2_259 := certify 7 [i2,i3,i4,i5,i6,i8,i10,i7,w65] [n3_312,n3_316,n3_330,n3_424,n3_477,n3_490] (by decide +kernel)
def n2_260 := certify 7 [i2,i3,i4,i5,i6,i8,w14,i7,w41] [n3_313,n3_317,n3_331,n3_374,n3_425,n3_478] (by decide +kernel)
def n2_261 := certify 7 [i2,i3,i4,i5,i6,w15,w13,i10,i7] [n3_483,n3_486] (by decide +kernel)
def n2_262 := certify 7 [i2,i3,i4,i5,i6,w18,i9,w14,i7] [n3_367,n3_372] (by decide +kernel)
def n2_263 := certify 7 [i2,i3,i4,i5,i6,w21,i9,w14,i7] [n3_320,n3_375,n3_381,n3_497] (by decide +kernel)
def n2_264 := certify 7 [i2,i3,i4,i5,i6,w21,w13,i10,i7] [n3_324,n3_382,n3_491,n3_498] (by decide +kernel)
def n2_265 := certify 7 [i2,i3,i4,i5,i6,i9,i10,w28,w40] [n3_310,n3_312,n3_332,n3_344,n3_376,n3_378,n3_427,n3_492,n3_493] (by decide +kernel)
def n2_266 := certify 7 [i2,i3,i4,i5,i6,i9,w14,i7,w40] [n3_310,n3_313,n3_333,n3_342,n3_377,n3_426] (by decide +kernel)
def n2_267 := certify 7 [i2,i3,i4,i5,i6,w13,i10,i7,w40] [n3_311,n3_312,n3_334,n3_343,n3_428,n3_494] (by decide +kernel)
def n2_268 := certify 7 [i2,i3,i4,i5,i8,w21,i9,w14,i7] [n3_320,n3_386,n3_502] (by decide +kernel)
def n2_269 := certify 7 [i2,i3,i4,i5,i8,w21,w13,i10,i7] [n3_324,n3_387,n3_503] (by decide +kernel)
def n2_270 := certify 7 [i2,i3,i4,i5,i8,i9,i10,w28,w39] [n3_314,n3_316,n3_332,n3_347,n3_385,n3_388,n3_430,n3_500,n3_504] (by decide +kernel)
def n2_271 := certify 7 [i2,i3,i4,i5,i8,i9,w14,i7,w39] [n3_314,n3_317,n3_333,n3_345,n3_383,n3_389,n3_429,n3_499] (by decide +kernel)
def n2_272 := certify 7 [i2,i3,i4,i5,i8,w13,i10,i7,w39] [n3_315,n3_316,n3_334,n3_346,n3_384,n3_431,n3_501,n3_505] (by decide +kernel)
def n2_273 := certify 7 [i2,i3,i4,i5,w21,i9,w13,i10,i7] [n3_305,n3_324,n3_350,n3_394,n3_432] (by decide +kernel)
def n2_274 := certify 7 [i2,i3,i4,i5,w21,i9,i10,w14,i7] [n3_308,n3_320,n3_353,n3_434,n3_509] (by decide +kernel)
def n2_275 := certify 7 [i2,i3,i4,i5,w21,i9,i10,i7,w28] [n3_322,n3_330,n3_332,n3_348,n3_354,n3_392,n3_433,n3_437,n3_508] (by decide +kernel)
def n2_276 := certify 7 [i2,i3,i4,i5,w21,i9,w14,i7] [n3_304,n3_308,n3_321,n3_322,n3_328,n3_331,n3_333,n3_349,n3_355,n3_390,n3_393,n3_435,n3_469,n3_506,n3_510] (by decide +kernel)
def n2_277 := certify 7 [i2,i3,i4,i5,w21,i9,w14,i7,iOnes] [n3_320] (by decide +kernel)
def n2_278 := certify 7 [i2,i3,i4,i5,w21,w13,i10,i7] [n3_305,n3_309,n3_326,n3_327,n3_329,n3_330,n3_334,n3_351,n3_356,n3_391,n3_395,n3_438,n3_470,n3_507,n3_511] (by decide +kernel)
def n2_279 := certify 7 [i2,i3,i4,i5,w21,w13,i10,i7,iOnes] [n3_324] (by decide +kernel)
def n2_280 := certify 7 [i2,i3,i4,w44,i6,i8,i9,i10,i7] [n3_335,n3_341,n3_396,n3_397,n3_439,n3_512,n3_513] (by decide +kernel)
def n2_281 := certify 7 [i2,i3,i4,w26,i6,i8,w20,i10,i7] [n3_336,n3_399,n3_400,n3_440,n3_514,n3_515] (by decide +kernel)
def n2_282 := certify 7 [i2,i3,i4,i6,i8,i9,i10,w28,w38] [n3_337,n3_348,n3_407,n3_410,n3_442,n3_517,n3_524] (by decide +kernel)
def n2_283 := certify 7 [i2,i3,i4,i6,i8,i9,w14,i7,w38] [n3_337,n3_342,n3_345,n3_349,n3_405,n3_411,n3_441,n3_516] (by decide +kernel)
def n2_284 := certify 7 [i2,i3,i4,i6,i8,w13,w20,i10,i7] [n3_350,n3_443,n3_518,n3_525] (by decide +kernel)
def n2_285 := certify 7 [i2,i3,i4,i6,i8,w13,i10,i7,w38] [n3_338,n3_343,n3_346,n3_351,n3_406,n3_444,n3_519,n3_526] (by decide +kernel)
def n2_286 := certify 7 [i2,i3,i4,i6,i8,w20,w63,i10,i7] [n3_352,n3_409,n3_445,n3_520,n3_527] (by decide +kernel)
def n2_287 := certify 7 [i2,i3,i4,i6,i8,w20,i10,w14,i7] [n3_353,n3_447,n3_522] (by decide +kernel)
def n2_288 := certify 7 [i2,i3,i4,i6,i8,w20,i10,i7,w28] [n3_344,n3_347,n3_354,n3_408,n3_446,n3_449,n3_521,n3_523,n3_528] (by decide +kernel)
def n2_289 := certify 7 [i2,i3,i5,w26,i6,i8,w19,i10,i7] [n3_399,n3_450,n3_529] (by decide +kernel)
def n2_290 := certify 7 [i2,i3,i5,w26,i6,w18,i9,i10,i7] [n3_400,n3_451] (by decide +kernel)
def n2_291 := certify 7 [i2,i3,i5,w34,i6,i8,i9,w14,i7] [n3_355,n3_403] (by decide +kernel)
def n2_292 := certify 7 [i2,i3,i5,w34,i6,i8,w13,i10,i7] [n3_356,n3_404,n3_530] (by decide +kernel)
def n2_293 := certify 7 [i2,i3,i5,i6,w35,i8,i9,w14,i7] [n3_375,n3_381,n3_548] (by decide +kernel)
def n2_294 := certify 7 [i2,i3,i5,i6,w35,i8,w13,i10,i7] [n3_382,n3_532,n3_549] (by decide +kernel)
def n2_295 := certify 7 [i2,i3,i5,i6,i8,w18,i9,w14,i7] [n3_367,n3_386,n3_540] (by decide +kernel)
def n2_296 := certify 7 [i2,i3,i5,i6,i8,w18,w13,i10,i7] [n3_387,n3_541] (by decide +kernel)
def n2_297 := certify 7 [i2,i3,i5,i6,i8,i9,i10,w28,w37] [n3_358,n3_376,n3_392,n3_408,n3_453,n3_534,n3_542] (by decide +kernel)
def n2_298 := certify 7 [i2,i3,i5,i6,i8,i9,w14,i7,w37] [n3_358,n3_377,n3_383,n3_393,n3_405,n3_452,n3_533] (by decide +kernel)
def n2_299 := certify 7 [i2,i3,i5,i6,i8,w13,w19,i10,i7] [n3_394,n3_454,n3_535,n3_543] (by decide +kernel)
def n2_300 := certify 7 [i2,i3,i5,i6,i8,w13,i10,i7,w37] [n3_360,n3_384,n3_395,n3_406,n3_455,n3_536,n3_544] (by decide +kernel)
def n2_301 := certify 7 [i2,i3,i5,i6,i8,w19,i10,w14,i7] [n3_457,n3_538] (by decide +kernel)
def n2_302 := certify 7 [i2,i3,i5,i6,i8,w19,i10,i7,w28] [n3_378,n3_385,n3_407,n3_456,n3_459,n3_537,n3_539] (by decide +kernel)
def n2_303 := certify 7 [i2,i3,i5,i6,w18,i9,i10,w14,i7] [n3_367,n3_461,n3_546] (by decide +kernel)
def n2_304 := certify 7 [i2,i3,i5,i6,w18,i9,i10,i7,w28] [n3_369,n3_376,n3_388,n3_410,n3_460,n3_464,n3_545] (by decide +kernel)
def n2_305 := certify 7 [i2,i3,i5,i6,w18,i9,w14,i7] [n3_306,n3_368,n3_369,n3_373,n3_374,n3_375,n3_377,n3_389,n3_411,n3_462,n3_471,n3_531,n3_547] (by decide +kernel)
def n2_306 := certify 7 [i2,i3,i5,i6,w18,i9,w14,i7,iOnes] [n3_367] (by decide +kernel)
def n2_307 := certify 7 [i2,i3,w26,w34,i6,i8,i9,i10,i7] [n3_398,n3_399,n3_404,n3_465,n3_550,n3_551] (by decide +kernel)
def n2_308 := certify 7 [i2,w43,i4,i5,i6,i8,i9,i10,i7] [n3_412,n3_413,n3_414,n3_415,n3_422,n3_552,n3_553] (by decide +kernel)
def n2_309 := certify 7 [i2,w25,i4,i5,i6,i8,i9,w17,i7] [n3_416,n3_417,n3_418,n3_419,n3_558,n3_559] (by decide +kernel)
def n2_310 := certify 7 [i2,i4,i5,w26,i6,i8,i9,w17,i7] [n3_420,n3_440,n3_450,n3_451,n3_465] (by decide +kernel)
def n2_311 := certify 7 [i2,i4,i5,i6,i8,i9,w13,w17,i7] [n3_432,n3_443,n3_454] (by decide +kernel)
def n2_312 := certify 7 [i2,i4,i5,i6,i8,i9,i10,w28,w33] [n3_424,n3_433,n3_446,n3_456,n3_460,n3_565,n3_569] (by decide +kernel)
def n2_313 := certify 7 [i2,i4,i5,i6,i8,i9,w14,w17,i7] [n3_434,n3_447,n3_457,n3_461] (by decide +kernel)
def n2_314 := certify 7 [i2,i4,i5,i6,i8,i9,w14,i7,w33] [n3_425,n3_426,n3_429,n3_435,n3_441,n3_452,n3_462,n3_564] (by decide +kernel)
def n2_315 := certify 7 [i2,i4,i5,i6,i8,i9,w17,w58,i7] [n3_436,n3_448,n3_458,n3_463,n3_567] (by decide +kernel)
def n2_316 := certify 7 [i2,i4,i5,i6,i8,i9,w17,i7,w28] [n3_427,n3_430,n3_437,n3_442,n3_449,n3_453,n3_459,n3_464,n3_566] (by decide +kernel)
def n2_317 := certify 7 [i2,i4,i5,i6,i8,w13,i10,i7,w33] [n3_424,n3_428,n3_431,n3_438,n3_444,n3_455,n3_568,n3_570] (by decide +kernel)
def n2_318 := certify 7 [i3,w25,i4,i5,i6,i8,i9,w16,i7] [n3_466,n3_468,n3_558] (by decide +kernel)
def n2_319 := certify 7 [i3,w25,i4,i5,i6,w15,i9,i10,i7] [n3_467,n3_559] (by decide +kernel)
def n2_320 := certify 7 [i3,w29,i4,i5,i6,i8,i9,w14,i7] [n3_469,n3_471,n3_562] (by decide +kernel)
def n2_321 := certify 7 [i3,w29,i4,i5,i6,i8,w13,i10,i7] [n3_470,n3_563] (by decide +kernel)
def n2_322 := certify 7 [i3,i4,i5,w26,i6,i8,i9,w16,i7] [n3_514,n3_529,n3_550] (by decide +kernel)
def n2_323 := certify 7 [i3,i4,i5,w26,i6,w15,i9,i10,i7] [n3_489,n3_515,n3_551] (by decide +kernel)
def n2_324 := certify 7 [i3,i4,i5,i6,w30,i8,i9,w14,i7] [n3_497,n3_531,n3_548] (by decide +kernel)
def n2_325 := certify 7 [i3,i4,i5,i6,w30,i8,w13,i10,i7] [n3_491,n3_498,n3_549] (by decide +kernel)
def n2_326 := certify 7 [i3,i4,i5,i6,i8,w15,i9,w14,i7] [n3_502,n3_540] (by decide +kernel)
def n2_327 := certify 7 [i3,i4,i5,i6,i8,w15,w13,i10,i7] [n3_483,n3_503,n3_541] (by decide +kernel)
def n2_328 := certify 7 [i3,i4,i5,i6,i8,i9,w13,w16,i7] [n3_518,n3_535] (by decide +kernel)
def n2_329 := certify 7 [i3,i4,i5,i6,i8,i9,i10,w28,w32] [n3_477,n3_492,n3_508,n3_521,n3_537,n3_545,n3_566] (by decide +kernel)
def n2_330 := certify 7 [i3,i4,i5,i6,i8,i9,w14,w16,i7] [n3_509,n3_522,n3_538,n3_546] (by decide +kernel)
def n2_331 := certify 7 [i3,i4,i5,i6,i8,i9,w14,i7,w32] [n3_478,n3_499,n3_510,n3_516,n3_533,n3_547,n3_564] (by decide +kernel)
def n2_332 := certify 7 [i3,i4,i5,i6,i8,i9,w16,i7,w28] [n3_493,n3_500,n3_517,n3_523,n3_534,n3_539,n3_565] (by decide +kernel)
def n2_333 := certify 7 [i3,i4,i5,i6,i8,w13,i10,i7,w32] [n3_477,n3_494,n3_501,n3_511,n3_519,n3_536,n3_568] (by decide +kernel)
def n2_334 := certify 7 [i3,i4,i5,i6,w15,i9,w13,i10,i7] [n3_483,n3_525,n3_543] (by decide +kernel)
def n2_335 := certify 7 [i3,i4,i5,i6,w15,i9,i10,i7,w28] [n3_490,n3_492,n3_504,n3_524,n3_528,n3_542,n3_569] (by decide +kernel)
def n2_336 := certify 7 [i3,i4,i5,i6,w15,w13,i10,i7] [n3_472,n3_487,n3_488,n3_489,n3_490,n3_491,n3_494,n3_505,n3_526,n3_530,n3_532,n3_544,n3_570] (by decide +kernel)
def n2_337 := certify 7 [i3,i4,i5,i6,w15,w13,i10,i7,iOnes] [n3_483] (by decide +kernel)
def n2_338 := certify 7 [w25,w29,i4,i5,i6,i8,i9,i10,i7] [n3_554,n3_555,n3_556,n3_557,n3_558,n3_562] (by decide +kernel)
def n1_0 := certify 8 [iZero,i1,i2,i3,i4,i5,w21,i9,i10,i7] [n2_0,n2_1,n2_8,n2_9,n2_43] (by decide +kernel)
def n1_1 := certify 8 [iZero,i1,i2,i3,i4,i6,i8,w20,i10,i7] [n2_0,n2_2,n2_5,n2_6,n2_52] (by decide +kernel)
def n1_2 := certify 8 [iZero,i1,i2,i3,i5,i6,i8,w19,i10,i7] [n2_3,n2_7,n2_72] (by decide +kernel)
def n1_3 := certify 8 [iZero,i1,i2,i3,i5,i6,w18,i9,i10,i7] [n2_4,n2_10,n2_81] (by decide +kernel)
def n1_4 := certify 8 [iZero,i1,i2,i4,i5,i6,i8,i9,w17,i7] [n2_1,n2_2,n2_3,n2_4,n2_114] (by decide +kernel)
def n1_5 := certify 8 [iZero,i1,i3,i4,i5,i6,i8,i9,w16,i7] [n2_5,n2_7,n2_160] (by decide +kernel)
def n1_6 := certify 8 [iZero,i1,i3,i4,i5,i6,w15,i9,i10,i7] [n2_6,n2_11,n2_169] (by decide +kernel)
def n1_7 := certify 8 [iZero,i2,i3,i4,i5,i6,i8,i9,w14,i7] [n2_8,n2_10,n2_245] (by decide +kernel)
def n1_8 := certify 8 [iZero,i2,i3,i4,i5,i6,i8,w13,i10,i7] [n2_9,n2_11,n2_250] (by decide +kernel)
def n1_9 := certify 8 [i0,i1,i2,i3,i4,i5,w21,i9,i10,i7] [n2_12,n2_13,n2_20,n2_21] (by decide +kernel)
def n1_10 := certify 8 [i0,i1,i2,i3,i4,i6,i8,w20,i10,i7] [n2_12,n2_14,n2_17,n2_18] (by decide +kernel)
def n1_11 := certify 8 [i0,i1,i2,i3,i5,i6,i8,w19,i10,i7] [n2_15,n2_19,n2_78] (by decide +kernel)
def n1_12 := certify 8 [i0,i1,i2,i3,i5,i6,w18,i9,i10,i7] [n2_16,n2_22,n2_85] (by decide +kernel)
def n1_13 := certify 8 [i0,i1,i2,i4,i5,i6,i8,i9,w17,i7] [n2_13,n2_14,n2_15,n2_16] (by decide +kernel)
def n1_14 := certify 8 [i0,i1,i3,i4,i5,i6,i8,i9,w16,i7] [n2_17,n2_19,n2_167] (by decide +kernel)
def n1_15 := certify 8 [i0,i1,i3,i4,i5,i6,w15,i9,i10,i7] [n2_18,n2_23,n2_170] (by decide +kernel)
def n1_16 := certify 8 [i0,i2,i3,i4,i5,i6,i8,i9,w14,i7] [n2_20,n2_22,n2_248] (by decide +kernel)
def n1_17 := certify 8 [i0,i2,i3,i4,i5,i6,i8,w13,i10,i7] [n2_21,n2_23,n2_251] (by decide +kernel)
def n1_18 := certify 8 [w27,i2,i3,i4,i5,i6,i8,i9,i10,i7] [n2_24,n2_25,n2_26,n2_27,n2_28,n2_29,n2_30,n2_243,n2_244,n2_249,n2_280,n2_308] (by decide +kernel)
def n1_19 := certify 8 [i1,w31,i3,i4,i5,i6,i8,i9,i10,i7] [n2_31,n2_32,n2_33,n2_34,n2_35,n2_158,n2_159,n2_168,n2_183,n2_224,n2_234,n2_235] (by decide +kernel)
def n1_20 := certify 8 [i1,i2,i3,w36,i5,i6,i8,i9,i10,i7] [n2_36,n2_37,n2_69,n2_71,n2_80,n2_94,n2_103,n2_113,n2_156,n2_157,n2_240,n2_241] (by decide +kernel)
def n1_21 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,i10,i7] [n2_43,n2_52,n2_72,n2_81,n2_114,n2_160,n2_169,n2_245,n2_250] (by decide +kernel)
def n1_22 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,w24,i7] [n2_170,n2_251] (by decide +kernel)
def n1_23 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,w14,i7] [n2_44,n2_82,n2_171,n2_245,n2_252] (by decide +kernel)
def n1_24 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,w16,i7] [n2_53,n2_73,n2_160,n2_172,n2_253] (by decide +kernel)
def n1_25 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,w17,i7] [n2_45,n2_54,n2_74,n2_83,n2_114,n2_161,n2_173,n2_225,n2_246,n2_254,n2_309] (by decide +kernel)
def n1_26 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i9,i7,w42] [n2_38,n2_39,n2_41,n2_46,n2_51,n2_55,n2_70,n2_75,n2_84,n2_115,n2_162,n2_174,n2_247,n2_255] (by decide +kernel)
def n1_27 := certify 8 [i1,i2,i3,i4,i5,i6,i8,w23,i10,i7] [n2_85,n2_248] (by decide +kernel)
def n1_28 := certify 8 [i1,i2,i3,i4,i5,i6,i8,w13,i10,i7] [n2_47,n2_86,n2_175,n2_250,n2_252] (by decide +kernel)
def n1_29 := certify 8 [i1,i2,i3,i4,i5,i6,i8,w19,i10,i7] [n2_72,n2_87,n2_116,n2_163,n2_256] (by decide +kernel)
def n1_30 := certify 8 [i1,i2,i3,i4,i5,i6,i8,w20,i10,i7] [n2_48,n2_52,n2_76,n2_88,n2_104,n2_117,n2_164,n2_176,n2_257,n2_258,n2_281] (by decide +kernel)
def n1_31 := certify 8 [i1,i2,i3,i4,i5,i6,i8,i10,i7,w41] [n2_38,n2_40,n2_42,n2_49,n2_56,n2_77,n2_89,n2_118,n2_119,n2_165,n2_166,n2_177,n2_259,n2_260] (by decide +kernel)
def n1_32 := certify 8 [i1,i2,i3,i4,i5,i6,w22,i9,i10,i7] [n2_78,n2_167] (by decide +kernel)
def n1_33 := certify 8 [i1,i2,i3,i4,i5,i6,w15,i9,i10,i7] [n2_57,n2_79,n2_169,n2_172,n2_261] (by decide +kernel)
def n1_34 := certify 8 [i1,i2,i3,i4,i5,i6,w18,i9,i10,i7] [n2_81,n2_87,n2_120,n2_178,n2_262] (by decide +kernel)
def n1_35 := certify 8 [i1,i2,i3,i4,i5,i6,w21,i9,i10,i7] [n2_43,n2_58,n2_90,n2_91,n2_95,n2_121,n2_179,n2_180,n2_184,n2_263,n2_264] (by decide +kernel)
def n1_36 := certify 8 [i1,i2,i3,i4,i5,i6,i9,i10,i7,w40] [n2_39,n2_40,n2_50,n2_59,n2_60,n2_92,n2_93,n2_122,n2_123,n2_181,n2_182,n2_265,n2_266,n2_267] (by decide +kernel)
def n1_37 := certify 8 [i1,i2,i3,i4,i5,i8,w21,i9,i10,i7] [n2_24,n2_43,n2_61,n2_98,n2_124,n2_187,n2_268,n2_269] (by decide +kernel)
def n1_38 := certify 8 [i1,i2,i3,i4,i5,i8,i9,i10,i7,w39] [n2_41,n2_42,n2_50,n2_62,n2_63,n2_96,n2_97,n2_99,n2_125,n2_126,n2_185,n2_186,n2_188,n2_270,n2_271,n2_272] (by decide +kernel)
def n1_39 := certify 8 [i1,i2,i3,i4,i5,w21,i9,i10,i7] [n2_24,n2_31,n2_36,n2_44,n2_45,n2_46,n2_47,n2_48,n2_49,n2_50,n2_64,n2_65,n2_66,n2_68,n2_100,n2_101,n2_102,n2_127,n2_128,n2_129,n2_152,n2_189,n2_190,n2_191,n2_236,n2_242,n2_273,n2_274,n2_275,n2_276,n2_278] (by decide +kernel)
def n1_40 := certify 8 [i1,i2,i3,i4,i5,w21,i9,i10,i7,iOnes] [n2_43,n2_67,n2_130,n2_277,n2_279] (by decide +kernel)
def n1_41 := certify 8 [i1,i2,i3,i4,i6,i8,i9,w20,i10,i7] [n2_32,n2_52,n2_64,n2_108,n2_131,n2_194,n2_201,n2_284] (by decide +kernel)
def n1_42 := certify 8 [i1,i2,i3,i4,i6,i8,i9,i10,i7,w38] [n2_51,n2_56,n2_59,n2_62,n2_65,n2_107,n2_109,n2_112,n2_132,n2_133,n2_195,n2_196,n2_202,n2_282,n2_283,n2_285] (by decide +kernel)
def n1_43 := certify 8 [i1,i2,i3,i4,i6,i8,w20,i10,i7] [n2_25,n2_32,n2_37,n2_53,n2_54,n2_55,n2_56,n2_57,n2_58,n2_60,n2_61,n2_63,n2_66,n2_105,n2_106,n2_110,n2_111,n2_134,n2_135,n2_136,n2_153,n2_192,n2_193,n2_197,n2_198,n2_199,n2_203,n2_237,n2_286,n2_287,n2_288] (by decide +kernel)
def n1_44 := certify 8 [i1,i2,i3,i4,i6,i8,w20,i10,i7,iOnes] [n2_52,n2_67,n2_137,n2_200,n2_204] (by decide +kernel)
def n1_45 := certify 8 [i1,i2,i3,i5,w34,i6,i8,i9,i10,i7] [n2_68,n2_76,n2_104,n2_138,n2_205,n2_206,n2_291,n2_292,n2_307] (by decide +kernel)
def n1_46 := certify 8 [i1,i2,i3,i5,i6,w35,i8,i9,i10,i7] [n2_91,n2_95,n2_105,n2_139,n2_209,n2_210,n2_223,n2_293,n2_294] (by decide +kernel)
def n1_47 := certify 8 [i1,i2,i3,i5,i6,i8,w18,i9,i10,i7] [n2_27,n2_81,n2_98,n2_106,n2_140,n2_218,n2_295,n2_296] (by decide +kernel)
def n1_48 := certify 8 [i1,i2,i3,i5,i6,i8,i9,w19,i10,i7] [n2_33,n2_72,n2_101,n2_108,n2_141,n2_211,n2_219,n2_299] (by decide +kernel)
def n1_49 := certify 8 [i1,i2,i3,i5,i6,i8,i9,i10,i7,w37] [n2_70,n2_77,n2_92,n2_96,n2_102,n2_107,n2_111,n2_142,n2_143,n2_212,n2_213,n2_220,n2_297,n2_298,n2_300] (by decide +kernel)
def n1_50 := certify 8 [i1,i2,i3,i5,i6,i8,w19,i10,i7] [n2_26,n2_33,n2_73,n2_74,n2_75,n2_76,n2_77,n2_79,n2_90,n2_93,n2_97,n2_109,n2_144,n2_145,n2_146,n2_154,n2_207,n2_214,n2_215,n2_216,n2_238,n2_289,n2_301,n2_302] (by decide +kernel)
def n1_51 := certify 8 [i1,i2,i3,i5,i6,i8,w19,i10,i7,iOnes] [n2_72,n2_147,n2_217] (by decide +kernel)
def n1_52 := certify 8 [i1,i2,i3,i5,i6,w18,i9,i10,i7] [n2_27,n2_34,n2_82,n2_83,n2_84,n2_86,n2_88,n2_89,n2_91,n2_92,n2_99,n2_112,n2_148,n2_149,n2_150,n2_155,n2_208,n2_221,n2_222,n2_239,n2_290,n2_303,n2_304,n2_305] (by decide +kernel)
def n1_53 := certify 8 [i1,i2,i3,i5,i6,w18,i9,i10,i7,iOnes] [n2_81,n2_151,n2_306] (by decide +kernel)
def n1_54 := certify 8 [i1,i2,i4,i5,i6,i8,i9,i10,w17,i7] [n2_113,n2_114,n2_127,n2_134,n2_144,n2_148,n2_229,n2_313] (by decide +kernel)
def n1_55 := certify 8 [i1,i2,i4,i5,i6,i8,i9,i10,i7,w33] [n2_115,n2_118,n2_122,n2_125,n2_128,n2_132,n2_135,n2_142,n2_145,n2_149,n2_228,n2_230,n2_233,n2_312,n2_314,n2_317] (by decide +kernel)
def n1_56 := certify 8 [i1,i2,i4,i5,i6,i8,i9,w17,i7] [n2_28,n2_35,n2_113,n2_115,n2_116,n2_117,n2_119,n2_120,n2_121,n2_123,n2_124,n2_126,n2_129,n2_131,n2_133,n2_136,n2_138,n2_139,n2_140,n2_141,n2_143,n2_146,n2_150,n2_226,n2_227,n2_231,n2_232,n2_310,n2_311,n2_315,n2_316] (by decide +kernel)
def n1_57 := certify 8 [i1,i2,i4,i5,i6,i8,i9,w17,i7,iOnes] [n2_114,n2_130,n2_137,n2_147,n2_151] (by decide +kernel)
def n1_58 := certify 8 [i1,i3,w29,i4,i5,i6,i8,i9,i10,i7] [n2_152,n2_153,n2_154,n2_155,n2_161,n2_225,n2_320,n2_321,n2_338] (by decide +kernel)
def n1_59 := certify 8 [i1,i3,i4,i5,i6,w30,i8,i9,i10,i7] [n2_180,n2_184,n2_192,n2_207,n2_208,n2_223,n2_226,n2_324,n2_325] (by decide +kernel)
def n1_60 := certify 8 [i1,i3,i4,i5,i6,i8,w15,i9,i10,i7] [n2_30,n2_169,n2_187,n2_193,n2_218,n2_227,n2_326,n2_327] (by decide +kernel)
def n1_61 := certify 8 [i1,i3,i4,i5,i6,i8,i9,i10,w16,i7] [n2_156,n2_160,n2_190,n2_197,n2_214,n2_221,n2_229,n2_330] (by decide +kernel)
def n1_62 := certify 8 [i1,i3,i4,i5,i6,i8,i9,i10,i7,w32] [n2_162,n2_165,n2_181,n2_185,n2_191,n2_195,n2_198,n2_212,n2_215,n2_222,n2_228,n2_232,n2_329,n2_331,n2_333] (by decide +kernel)
def n1_63 := certify 8 [i1,i3,i4,i5,i6,i8,i9,w16,i7] [n2_29,n2_156,n2_161,n2_162,n2_163,n2_164,n2_166,n2_178,n2_179,n2_182,n2_186,n2_194,n2_196,n2_199,n2_205,n2_209,n2_211,n2_213,n2_216,n2_230,n2_318,n2_322,n2_328,n2_332] (by decide +kernel)
def n1_64 := certify 8 [i1,i3,i4,i5,i6,i8,i9,w16,i7,iOnes] [n2_160,n2_200,n2_217] (by decide +kernel)
def n1_65 := certify 8 [i1,i3,i4,i5,i6,w15,i9,i10,i7] [n2_30,n2_157,n2_171,n2_173,n2_174,n2_175,n2_176,n2_177,n2_180,n2_181,n2_188,n2_201,n2_202,n2_203,n2_206,n2_210,n2_219,n2_220,n2_233,n2_319,n2_323,n2_334,n2_335,n2_336] (by decide +kernel)
def n1_66 := certify 8 [i1,i3,i4,i5,i6,w15,i9,i10,i7,iOnes] [n2_169,n2_204,n2_337] (by decide +kernel)
def n1_67 := certify 8 [i2,i3,w25,i4,i5,i6,i8,i9,i10,i7] [n2_236,n2_237,n2_238,n2_239,n2_246,n2_309,n2_318,n2_319,n2_338] (by decide +kernel)
def n1_68 := certify 8 [i2,i3,i4,i5,w26,i6,i8,i9,i10,i7] [n2_242,n2_258,n2_281,n2_289,n2_290,n2_307,n2_310,n2_322,n2_323] (by decide +kernel)
def n1_69 := certify 8 [i2,i3,i4,i5,i6,i8,i9,w13,i10,i7] [n2_235,n2_250,n2_273,n2_284,n2_299,n2_311,n2_328,n2_334] (by decide +kernel)
def n1_70 := certify 8 [i2,i3,i4,i5,i6,i8,i9,i10,w14,i7] [n2_240,n2_245,n2_274,n2_287,n2_301,n2_303,n2_313,n2_330] (by decide +kernel)
def n1_71 := certify 8 [i2,i3,i4,i5,i6,i8,i9,i10,i7,w28] [n2_247,n2_259,n2_265,n2_270,n2_275,n2_282,n2_288,n2_297,n2_302,n2_304,n2_312,n2_316,n2_329,n2_332,n2_335] (by decide +kernel)
def n1_72 := certify 8 [i2,i3,i4,i5,i6,i8,i9,w14,i7] [n2_234,n2_240,n2_246,n2_247,n2_256,n2_257,n2_260,n2_262,n2_263,n2_266,n2_268,n2_271,n2_276,n2_283,n2_291,n2_293,n2_295,n2_298,n2_305,n2_314,n2_320,n2_324,n2_326,n2_331] (by decide +kernel)
def n1_73 := certify 8 [i2,i3,i4,i5,i6,i8,i9,w14,i7,iOnes] [n2_245,n2_277,n2_306] (by decide +kernel)
def n1_74 := certify 8 [i2,i3,i4,i5,i6,i8,w13,i10,i7] [n2_235,n2_241,n2_253,n2_254,n2_255,n2_258,n2_259,n2_261,n2_264,n2_267,n2_269,n2_272,n2_278,n2_285,n2_292,n2_294,n2_296,n2_300,n2_317,n2_321,n2_325,n2_327,n2_333,n2_336] (by decide +kernel)
def n1_75 := certify 8 [i2,i3,i4,i5,i6,i8,w13,i10,i7,iOnes] [n2_250,n2_279,n2_337] (by decide +kernel)
def n0_0 := certify 9 [iZero,i1,i2,i3,i4,i5,i6,i8,i9,i10,i7] [n1_0,n1_1,n1_2,n1_3,n1_4,n1_5,n1_6,n1_7,n1_8,n1_21] (by decide +kernel)
def n0_1 := certify 9 [i0,i1,i2,i3,i4,i5,i6,i8,i9,i10,i7] [n1_9,n1_10,n1_11,n1_12,n1_13,n1_14,n1_15,n1_16,n1_17,n1_22,n1_27,n1_32] (by decide +kernel)
def n0_2 := certify 9 [i1,i2,i3,i4,i5,i6,i8,i9,i10,i7] [n1_18,n1_19,n1_20,n1_23,n1_24,n1_25,n1_26,n1_28,n1_29,n1_30,n1_31,n1_33,n1_34,n1_35,n1_36,n1_37,n1_38,n1_39,n1_41,n1_42,n1_43,n1_45,n1_46,n1_47,n1_48,n1_49,n1_50,n1_52,n1_54,n1_55,n1_56,n1_58,n1_59,n1_60,n1_61,n1_62,n1_63,n1_65,n1_67,n1_68,n1_69,n1_70,n1_71,n1_72,n1_74] (by decide +kernel)
def n0_3 := certify 9 [i1,i2,i3,i4,i5,i6,i8,i9,i10,i7,iOnes] [n1_21,n1_40,n1_44,n1_51,n1_53,n1_57,n1_64,n1_66,n1_73,n1_75] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem ten_impossible : ¬ RepSizeAtMost graph 10 := from_nodes [n0_0,n0_1,n0_2,n0_3] (by decide +kernel)

end PEqualNP.Outside.ThreeStopExclusion_aux

theorem PEqualNP.Outside.ThreeStopExclusion :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 8) (v : Fin 3) =>
      (16434824 : Nat).testBit (3 * u.val + v.val)) 10 :=
  PEqualNP.Outside.ThreeStopExclusion_aux.ten_impossible
