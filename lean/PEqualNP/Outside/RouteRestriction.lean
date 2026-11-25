import PEqualNP.Outside.RouteLower

namespace PEqualNP.Outside.RouteRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical
open PEqualNP.Outside.RouteLower_aux
namespace Lifting
variable {X : Type}
abbrev Wire (X : Type) := Word × (X → Bool)
abbrev Bank (X : Type) := Finset (Wire X)
def zero : Wire X := (0,fun _ => false)
def one : Wire X := (BitVec.allOnes 288,fun _ => true)
def mix (op : Bool) (a b : Wire X) : Wire X :=
  (combine op a.1 b.1,fun x => if op then a.2 x && b.2 x else a.2 x || b.2 x)
def view : Sum (Fin 288) X → Wire X → Bool
  | .inl p, w => bit p w.1
  | .inr x, w => w.2 x

theorem view_mix (op : Bool) (p : Sum (Fin 288) X) (a b : Wire X) :
    view p (mix op a b) = (if op then view p a && view p b else view p a || view p b) := by
  cases op <;> cases p <;> simp [view,mix,combine,bit]

theorem view_zero (p : Sum (Fin 288) X) : view p zero = false := by
  cases p <;> simp [view,zero,bit]

set_option maxRecDepth 2000 in
theorem view_one (p : Sum (Fin 288) X) : view p one = true := by
  cases p with
  | inl p => exact (by decide +kernel : ∀ i : Fin 288, bit i (BitVec.allOnes 288) = true) p
  | inr => rfl

theorem wire_ext {a b : Wire X} (h : ∀ p, view p a = view p b) : a = b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact h (.inl ⟨i,hi⟩)
  · exact funext fun x => h (.inr x)
inductive Program (t : Wire X) : Nat → (Bank X) → Prop where
  | done {s} (h : t ∈ s) : Program t 0 s
  | gate {n s a b} (op : Bool) (ha : a ∈ s) (hb : b ∈ s)
      (tail : Program t n (insert (mix op a b) s)) : Program t (n+1) s

-- Trace back only the operands actually needed by the output.
inductive Cone (t : Wire X) : Nat → (Bank X) → Prop where
  | done : Cone t 0 {t}
  | gate {n u} (op : Bool) (a b : Wire X) (freshA : mix op a b ≠ a) (freshB : mix op a b ≠ b) (tail : Cone t n u)
      (used : mix op a b ∈ u) :
      Cone t (n+1) (insert a (insert b (u.erase (mix op a b))))

theorem extractCone {t : Wire X} {n s} (h : Program t n s) :
    ∃ k ≤ n, ∃ u ⊆ s, Cone t k u := by
  induction h with
  | done h => exact ⟨0, le_rfl, {t}, Finset.singleton_subset_iff.mpr h, Cone.done⟩
  | @gate n s a b op ha hb tail ih =>
    obtain ⟨k,hk,u,hu,hn⟩ := ih
    by_cases old : mix op a b ∈ s
    · exact ⟨k, by omega, u, (by simpa [Finset.insert_eq_of_mem old] using hu), hn⟩
    by_cases hc : mix op a b ∈ u
    · refine ⟨k+1, by omega, _, ?_, Cone.gate op a b (fun e => old (e.symm ▸ ha)) (fun e => old (e.symm ▸ hb)) hn hc⟩
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

theorem distinguishes {t : Wire X} {n s} (h : Cone t n s) :
    ∀ p q, t.2 p = true → t.2 q = false → ∃ w ∈ s, w.2 p = true ∧ w.2 q = false := by
  induction h with
  | done => exact fun p q hp hq => ⟨t, by simp, hp, hq⟩
  | @gate n u op a b freshA freshB tail used ih =>
    intro p q hp hq
    obtain ⟨w,hw,wp,wq⟩ := ih p q hp hq
    by_cases he : w = mix op a b
    · subst w
      have h : (a.2 p = true ∧ a.2 q = false) ∨
          (b.2 p = true ∧ b.2 q = false) := by
        cases op <;> simp [mix] at wp wq <;> grind
      rcases h with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · exact ⟨w, by simp [Finset.mem_erase.mpr ⟨he,hw⟩], wp,wq⟩

set_option maxRecDepth 10000 in
theorem operandsX (g : Gate) (ws : List (Wire X)) (s : Bank X)
    (hs : ∀ w ∈ ws, w ∈ s) (hz : zero ∈ s) (ho : one ∈ s)
    (allowed : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ op a b, a ∈ s ∧ b ∈ s ∧ ∀ p : Sum (Fin 288) X,
      view p (mix op a b) =
        g.op.eval (g.inputs.map fun i => (ws.map (view p)).getD i false) := by
  have mem (i : Nat) : ws.getD i zero ∈ s := by
    by_cases h : i < ws.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs ws[i] (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega : ws.length ≤ i)]; exact hz
  have readBit (p : Sum (Fin 288) X) (i : Nat) :
      (ws.map (view p)).getD i false = view p (ws.getD i zero) := by
    simpa [view_zero] using (List.getD_map (l := ws) (d := (zero : Wire X)) (n := i) (view p))
  obtain ⟨o,ins⟩ := g
  obtain ⟨hop,hlen⟩ := allowed
  change o = GateOp.and ∨ o = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · have all : ∀ q : Sum (Fin 288) X, view q (mix true one one) = true := by intro q; simp [view_mix,view_one]
      exact ⟨true,_,_,ho,ho,all⟩
    · exact ⟨false,zero,zero,hz,hz,fun p => by simp [view_mix,view_zero,GateOp.eval]⟩
  | cons i rest =>
    cases rest with
    | nil =>
      refine ⟨false,_,_,mem i,mem i,fun p => ?_⟩
      rcases hop with rfl | rfl <;> simp [ -List.getD_eq_getElem?_getD, view_mix,GateOp.eval,readBit]
    | cons j rest =>
      cases rest with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨true,_,_,mem i,mem j,fun p => by simp [ -List.getD_eq_getElem?_getD, view_mix,GateOp.eval,readBit]⟩
        · exact ⟨false,_,_,mem i,mem j,fun p => by simp [ -List.getD_eq_getElem?_getD, view_mix,GateOp.eval,readBit]⟩

theorem simulateX {target : Wire X} (gs : List Gate) (ws : List (Wire X)) (s : Bank X) (out : Nat)
    (hs : ∀ w ∈ ws, w ∈ s) (hz : zero ∈ s) (ho : one ∈ s)
    (allowed : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (correct : ∀ p, (run gs (ws.map (view p))).getD out false = view p target) :
    Program target gs.length s := by
  induction gs generalizing ws s with
  | nil =>
    have hw : ws.getD out zero = target := by
      apply wire_ext
      intro p
      have h := correct p
      change (ws.map (view p)).getD out false = _ at h
      simpa [List.getD_map,view_zero] using
        (List.getD_map (l := ws) (d := (zero : Wire X)) (n := out) (view p)).symm.trans (by simpa [view_zero] using h)
    apply Program.done
    rw [← hw]
    by_cases h : out < ws.length
    · rw [List.getD_eq_getElem _ _ h]; exact hs ws[out] (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega : ws.length ≤ out)]; exact hz
  | cons g gs ih =>
    obtain ⟨op,a,b,ha,hb,hbit⟩ := operandsX g ws s hs hz ho (allowed g (by simp))
    apply Program.gate op ha hb
    apply ih (ws ++ [mix op a b])
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


noncomputable def vanishing (s : Bank X) := (s.filter fun w => w.1 = 0).card

theorem insert_bound (s : Bank X) (a : Wire X) :
    vanishing (insert a s) ≤ vanishing s + (if a.1 = 0 then 1 else 0) := by
  classical
  by_cases ha : a.1 = 0
  · simpa [vanishing,Finset.filter_insert,ha] using
      Finset.card_insert_le a (s.filter fun w => w.1 = 0)
  · simp only [vanishing,Finset.filter_insert,ha,ite_false,Nat.add_zero,le_refl]

theorem erase_count (s : Bank X) (a : Wire X) (ha : a ∈ s) :
    vanishing (s.erase a) + (if a.1 = 0 then 1 else 0) = vanishing s := by
  classical
  have eq : (s.erase a).filter (fun w => w.1 = 0) = (s.filter (fun w => w.1 = 0)).erase a := by
    ext w; simp; tauto
  unfold vanishing
  rw [eq]
  by_cases h : a.1 = 0
  · simpa [h] using Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨ha,h⟩)
  · have no : a ∉ s.filter (fun w => w.1 = 0) := fun hm => h (Finset.mem_filter.mp hm).2
    simp only [h,ite_false,Nat.add_zero,Finset.erase_eq_of_notMem no]

-- A gate touching a zero operand needs no gate on the retained submatrix.
-- Two zero operands yield a zero result, so merging them pays for only one input.
theorem zero_left (op : Bool) (w : Word) : combine op 0 w = (if op then 0 else w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; cases op <;> simp [combine]
theorem zero_right (op : Bool) (w : Word) : combine op w 0 = (if op then 0 else w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; cases op <;> simp [combine]

theorem lowerCone {t : Wire X} (ht : t.1 = target) {n s} (h : Cone t n s) :
    ∀ bank : Pool, 0 ∈ bank → (∀ w ∈ s, w.1 ∈ bank) →
      ∃ k, k + vanishing s ≤ n ∧ Builds k bank := by
  induction h with
  | done =>
    intro bank hz hs
    have nz : t.1 ≠ 0 := ht ▸ (by decide : target ≠ 0)
    exact ⟨0,by simp only [vanishing,Finset.filter_singleton,nz,ite_false,Finset.card_empty,Nat.zero_add,le_refl],Builds.done (ht ▸ hs t (by simp))⟩
  | @gate n u op a b fa fb tail used ih =>
    intro bank hz hs
    let z := mix op a b
    let rest := u.erase z
    have ca := insert_bound (insert b rest) a
    have cb := insert_bound rest b
    have cz := erase_count u z used
    have hr (w : Wire X) (hw : w ∈ u) (ne : w ≠ z) : w.1 ∈ bank :=
      hs w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ne,hw⟩)))
    have ma : a.1 ∈ bank := hs a (by simp)
    have mb : b.1 ∈ bank := hs b (by simp)
    by_cases trivialGate : a.1 = 0 ∨ b.1 = 0
    · have mz : z.1 ∈ bank := by
        change combine op a.1 b.1 ∈ bank
        rcases trivialGate with ha | hb
        · rw [ha,zero_left]; cases op <;> assumption
        · rw [hb,zero_right]; cases op <;> assumption
      obtain ⟨k,hk,prog⟩ := ih bank hz (fun w hw => by
        by_cases eq : w = z
        · simpa [eq] using mz
        · exact hr w hw eq)
      refine ⟨k,?_,prog⟩
      change k + vanishing (insert a (insert b rest)) ≤ n+1
      change vanishing rest + _ = _ at cz
      by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0
      · have hzero : z.1 = 0 := by cases op <;> simp [z,mix,combine,ha,hb]
        simp only [ha,hb,hzero,ite_true,ite_false] at ca cb cz; omega
      · simp only [ha,hb,ite_true,ite_false] at ca cb; omega
      · simp only [ha,hb,ite_true,ite_false] at ca cb; omega
      · tauto
    · have ha : a.1 ≠ 0 := fun eq => trivialGate (Or.inl eq)
      have hb : b.1 ≠ 0 := fun eq => trivialGate (Or.inr eq)
      obtain ⟨k,hk,prog⟩ := ih (insert z.1 bank) (Finset.mem_insert_of_mem hz) (fun w hw => by
        by_cases eq : w = z
        · simp [eq]
        · exact Finset.mem_insert_of_mem (hr w hw eq))
      refine ⟨k+1,?_,Builds.gate op ma mb prog⟩
      change k+1 + vanishing (insert a (insert b rest)) ≤ n+1
      change vanishing rest + _ = _ at cz
      simp only [ha,hb,ite_true,ite_false] at ca cb; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem base_cost {d : Nat} (p : Builds d initial) : 11 ≤ d := by
  by_contra! hd
  obtain ⟨n,hnd,s,hs,h⟩ := extract p
  have hn : n ≤ 10 := by omega
  let cs : List (Certified 10) := [n0_0,n0_1,n0_2,n0_3]
  have ok : ∀ xs ∈ roots, ∃ zs ∈ cs.map Subtype.val, xs.toFinset = zs.toFinset := by decide +kernel
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

abbrev Cell (n m : Nat) := Fin n × Fin m

def row {n m : Nat} (i : Fin n) : Wire (Cell n m) :=
  (if i.val < 8 then pins.getD i.val 0 else 0,fun p => decide (i = p.1))
def col {n m : Nat} (j : Fin m) : Wire (Cell n m) :=
  (if j.val < 3 then pins.getD (8+j.val) 0 else 0,fun p => decide (j = p.2))
def inputs (n m : Nat) : List (Wire (Cell n m)) := List.ofFn row ++ List.ofFn col

noncomputable def sources (n m : Nat) : Bank (Cell n m) :=
  insert zero (insert one (inputs n m).toFinset)

theorem sources_cases {n m} {w : Wire (Cell n m)} (hw : w ∈ sources n m) :
    w = zero ∨ w = one ∨ (∃ i, w = row i) ∨ ∃ j, w = col j := by
  simpa [sources,inputs,List.mem_ofFn,eq_comm] using hw

def coreU (p : Fin 288) := Fin.ofNat 8 (rowIndex p / 3)
def coreV (p : Fin 288) := Fin.ofNat 3 (rowIndex p % 3)

theorem pin_rows : ∀ (i : Fin 8) (p : Fin 288),
    bit p (pins.getD i.val 0) = decide (i = coreU p) := by decide +kernel
theorem pin_cols : ∀ (j : Fin 3) (p : Fin 288),
    bit p (pins.getD (8+j.val) 0) = decide (j = coreV p) := by decide +kernel
theorem core_graph : ∀ p : Fin 288, graph (coreU p) (coreV p) = bit p target := by decide +kernel

theorem match_pin {a b : Nat} (le : a ≤ b) (i : Fin b) (v : Fin a) :
    (if h : i.val < a then decide ((⟨i.val,h⟩ : Fin a) = v) else false) =
      decide (i = v.castLE le) := by
  by_cases h : i.val < a
  · simp only [h,dite_true,Fin.ext_iff]
    rfl
  · have ne : i ≠ v.castLE le := fun e => h (e ▸ v.isLt)
    simp only [h,dite_false,ne,decide_false]

theorem sample_inputs {n m} (hn : 8 ≤ n) (hm : 3 ≤ m) (p : Fin 288) :
    (inputs n m).map (view (.inl p)) = oneEach ((coreU p).castLE hn) ((coreV p).castLE hm) := by
  simp only [inputs,List.map_append,List.map_ofFn,oneEach]
  congr 1 <;> apply congrArg List.ofFn <;> funext i
  · change bit p (if i.val < 8 then pins.getD i.val 0 else 0) = _
    rw [← match_pin hn i (coreU p)]
    by_cases h : i.val < 8
    · simpa only [h,ite_true,dite_true] using pin_rows ⟨i,h⟩ p
    · simp [h,bit]
  · change bit p (if i.val < 3 then pins.getD (8+i.val) 0 else 0) = _
    rw [← match_pin hm i (coreV p)]
    by_cases h : i.val < 3
    · simpa only [h,ite_true,dite_true] using pin_cols ⟨i,h⟩ p
    · simp [h,bit]

theorem projected_input {n m} {w : Wire (Cell n m)} (hw : w ∈ sources n m) : w.1 ∈ initial := by
  have mem (k : Nat) : pins.getD k 0 ∈ initial := by
    by_cases h : k < pins.length
    · rw [List.getD_eq_getElem _ _ h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.getElem_mem h)))
    · rw [List.getD_eq_default _ _ (by omega : pins.length ≤ k)]; simp [initial]
  rcases sources_cases hw with rfl|rfl|⟨i,rfl⟩|⟨j,rfl⟩
  · simp [zero,initial]
  · simp [one,initial]
  · change (if i.val < 8 then _ else _) ∈ initial
    split <;> first | apply mem | simp [initial]
  · change (if j.val < 3 then _ else _) ∈ initial
    split <;> first | apply mem | simp [initial]

theorem graph_cone {n m d} (hn : 8 ≤ n) (hm : 3 ≤ m) (A : Fin n → Fin m → Bool)
    (core : ∀ i j, A (Fin.castLE hn i) (Fin.castLE hm j) = graph i j)
    (ex : RepSizeAtMost A d) :
    ∃ k ≤ d, ∃ s ⊆ sources n m, Cone (target,fun x : Cell n m => A x.1 x.2) k s := by
  obtain ⟨c,mono,sz,rep⟩ := ex
  have prog := simulateX (target := (target,fun x : Cell n m => A x.1 x.2))
    c.gates (inputs n m) (sources n m) c.output
    (fun w hw => by simp [sources,hw]) (by simp [sources]) (by simp [sources]) mono (fun p => by
      cases p with
      | inl p =>
        rw [sample_inputs hn hm]
        exact (rep _ _).trans ((core _ _).trans (core_graph p))
      | inr x =>
        have eq : (inputs n m).map (view (.inr x)) = oneEach x.1 x.2 := by
          simp only [inputs,List.map_append,List.map_ofFn,oneEach]
          rfl
        rw [eq]
        exact rep _ _)
  obtain ⟨k,hk,s,hs,con⟩ := extractCone prog
  exact ⟨k,le_trans hk sz,s,hs,con⟩

theorem row_needed {n m k} {A : Fin n → Fin m → Bool} {s : Bank (Cell n m)}
    (hs : s ⊆ sources n m) (cone : Cone (target,fun x : Cell n m => A x.1 x.2) k s)
    (i i' : Fin n) (j : Fin m) (hy : A i j = true) (hn : A i' j = false) :
    row i ∈ s := by
  obtain ⟨w,hw,pos,neg⟩ := distinguishes cone (i,j) (i',j) hy hn
  rcases sources_cases (hs hw) with rfl | rfl | ⟨a,rfl⟩ | ⟨b,rfl⟩
  · contradiction
  · contradiction
  · have eq : a = i := of_decide_eq_true pos
    exact eq ▸ hw
  · exact False.elim (Bool.noConfusion (pos.symm.trans neg) : False)

theorem col_needed {n m k} {A : Fin n → Fin m → Bool} {s : Bank (Cell n m)}
    (hs : s ⊆ sources n m) (cone : Cone (target,fun x : Cell n m => A x.1 x.2) k s)
    (j j' : Fin m) (i : Fin n) (hy : A i j = true) (hn : A i j' = false) :
    col j ∈ s := by
  obtain ⟨w,hw,pos,neg⟩ := distinguishes cone (i,j) (i,j') hy hn
  rcases sources_cases (hs hw) with rfl | rfl | ⟨a,rfl⟩ | ⟨b,rfl⟩
  · contradiction
  · contradiction
  · exact False.elim (Bool.noConfusion (pos.symm.trans neg) : False)
  · have eq : b = j := of_decide_eq_true pos
    exact eq ▸ hw

def extra {n m : Nat} : Fin (n-8) ⊕ Fin (m-3) → Wire (Cell n m)
  | .inl a => row ⟨8 + a.val,by have := a.isLt; omega⟩
  | .inr b => col ⟨3 + b.val,by have := b.isLt; omega⟩

theorem extra_inj {n m : Nat} (hn : 8 ≤ n) (hm : 3 ≤ m) : Function.Injective (@extra n m) := by
  let u : Fin n := ⟨0,by omega⟩
  let v : Fin m := ⟨0,by omega⟩
  intro a b eq
  cases a with
  | inl a =>
    let ua : Fin n := ⟨8+a.val,by have := a.isLt; omega⟩
    have val := congrArg (fun w : Wire (Cell n m) => w.2 (ua,v)) eq
    cases b with
    | inl b =>
      have h : (8+b.val) = 8+a.val := by simpa [extra,row,ua,Fin.ext_iff] using val.symm
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr b => simp [extra,row,col,ua,v,Fin.ext_iff] at val
  | inr a =>
    let va : Fin m := ⟨3+a.val,by have := a.isLt; omega⟩
    have val := congrArg (fun w : Wire (Cell n m) => w.2 (u,va)) eq
    cases b with
    | inl b => simp [extra,row,col,va,u,Fin.ext_iff] at val
    | inr b =>
      have h : (3+b.val) = 3+a.val := by simpa [extra,col,va,Fin.ext_iff] using val.symm
      exact congrArg Sum.inr (Fin.ext (by omega))

-- The extra rows and columns need a positive cell distinguishable by that pin alone.
theorem extension_bound {n m d} (hn : 8 ≤ n) (hm : 3 ≤ m) (A : Fin n → Fin m → Bool)
    (core : ∀ i j, A (Fin.castLE hn i) (Fin.castLE hm j) = graph i j)
    (rows : ∀ i : Fin n, 8 ≤ i.val → ∃ j i', A i j = true ∧ A i' j = false)
    (cols : ∀ j : Fin m, 3 ≤ j.val → ∃ i j', A i j = true ∧ A i j' = false)
    (ex : RepSizeAtMost A d) : n + m ≤ d := by
  classical
  obtain ⟨k,hk,s,hs,c⟩ := graph_cone hn hm A core ex
  obtain ⟨q,hq,prog⟩ := lowerCone rfl c initial (by simp [initial]) (fun w hw => projected_input (hs hw))
  have cost := base_cost prog
  let vanished := s.filter fun w => w.1 = 0
  have mem (a : Fin (n-8) ⊕ Fin (m-3)) : extra a ∈ vanished := by
    apply Finset.mem_filter.mpr
    cases a with
    | inl a =>
      let i : Fin n := ⟨8+a.val,by have := a.isLt; omega⟩
      obtain ⟨j,i',hy,hno⟩ := rows i (by dsimp [i]; omega)
      exact ⟨row_needed hs c i i' j hy hno,by simp [extra,row]⟩
    | inr b =>
      let j : Fin m := ⟨3+b.val,by have := b.isLt; omega⟩
      obtain ⟨i,j',hy,hno⟩ := cols j (by dsimp [j]; omega)
      exact ⟨col_needed hs c j j' i hy hno,by simp [extra,col]⟩
  let f (a : Fin (n-8) ⊕ Fin (m-3)) : vanished := ⟨extra a,mem a⟩
  have hf : Function.Injective f := fun _ _ e => extra_inj hn hm (congrArg Subtype.val e)
  have count := Fintype.card_le_of_injective f hf
  change q + vanished.card ≤ k at hq
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_coe] at count
  omega

theorem membership_bound (k : Nat) (hk : 3 ≤ k) {d : Nat}
    (h : RepSizeAtMost (fun (i : Fin (2^k)) (j : Fin k) => i.val.testBit j.val) d) :
    2^k + k ≤ d := by
  have hn : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  apply extension_bound hn hk _ _ _ _ h
  · exact (by decide : ∀ (i : Fin 8) (j : Fin 3), i.val.testBit j.val = graph i j)
  · intro i hi
    obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero (by omega : i.val ≠ 0)
    have lt : j < k := by
      by_contra! bad
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) bad
      have hz := Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt hp)
      simp_all
    exact ⟨⟨j,lt⟩,⟨0,by omega⟩,hj,by simp⟩
  · intro j hj
    refine ⟨⟨2^j.val,Nat.pow_lt_pow_right (by decide : 1 < 2) j.isLt⟩,⟨0,by omega⟩,
      Nat.testBit_two_pow_self,?_⟩
    exact Nat.testBit_two_pow_of_ne (show j.val ≠ 0 by omega)

end Lifting
end PEqualNP.Outside.RouteRestriction
