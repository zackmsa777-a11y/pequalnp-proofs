import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire semantics and constant propagation are adapted from L_meta_193.
-- We also track when an individual gate disappears during the pass.
-- Run gates on a wire list: the fold inside `Circuit.wires`.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

-- The allowed gates: AND, OR, NOT reading at most two wires.
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

-- A NOT gate reads only its first wire: drop the others.
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

-- An allowed gate whose NOT gates read at most one wire.
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

-- The status of an old wire: a constant, or the wire `j` of the new circuit.
abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
-- next new wire. The result is the gate to emit, if any, and the status of the gate's wire.
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates.
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)


theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
-- and every old wire has a valid status whose value on the new wires is the old value.
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2




def seed (m h : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => if i.val = h then .inl false else .inr i.val

theorem seed_inv (w : List Bool) (m h : ℕ) (hw : w.length = m)
    (hz : w.getD h false = false) : Inv m w w (seed m h, []) := by
  refine ⟨by simp [seed, hw], fun i => ?_⟩
  by_cases hi : i < m
  · by_cases e : i = h
    · subst i; simpa [seed, hi, Stat.Valid, Stat.val] using hz
    · simp [seed, hi, e, Stat.Valid, Stat.val, wiresFrom]
  · have : m ≤ i := by omega
    simpa [seed, hi, Stat.Valid, Stat.val] using (List.getD_eq_default w false (by omega : w.length ≤ i))

-- Reattach h to the residual output using a single final gate.
def finish (h : ℕ) : Stat → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [h]⟩
  | .inr j => ⟨.or, [h,j]⟩

theorem finish_ok (h : ℕ) (s : Stat) : Ok (finish h s) := by
  cases s with
  | inl b => cases b <;> simp [finish, Ok]
  | inr j => simp [finish, Ok]

theorem finish_eval (w : List Bool) (h : ℕ) (s : Stat) :
    (wiresFrom [finish h s] w).getD w.length false = (w.getD h false || s.val w) := by
  cases s with
  | inl b => cases b <;> simp [finish, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finish, wiresFrom, GateOp.eval, Stat.val]

-- Record the state after each gate so savings at distinct gates can be counted.
def st (m h : ℕ) (gs : List Gate) (i : ℕ) :=
  elim m ((gs.take i).map normGate) (seed m h, [])

def action (m h : ℕ) (gs : List Gate) (j : Fin gs.length) :=
  let g := normGate (gs.get j)
  let a := st m h gs j
  simplify g.op (m + a.2.length) (g.inputs.map fun v => a.1.getD v (.inl false))

def skipped (m h : ℕ) (gs : List Gate) (j : Fin gs.length) : Prop :=
  (action m h gs j).1 = none

theorem st_zero (m h : ℕ) (gs : List Gate) : st m h gs 0 = (seed m h, []) := by
  simp [st, elim]

theorem st_succ (m h : ℕ) (gs : List Gate) (j : Fin gs.length) :
    st m h gs (j.val + 1) =
      ((st m h gs j).1 ++ [(action m h gs j).2],
       (st m h gs j).2 ++ (action m h gs j).1.toList) := by
  simp only [st, List.take_succ_eq_append_getElem j.isLt, List.map_append, List.map_cons,
    List.map_nil, elim, List.foldl_append]
  rfl

theorem st_sizes (m h : ℕ) (gs : List Gate) (i : ℕ) (hi : i ≤ gs.length) :
    (st m h gs i).1.length = m + i ∧ (st m h gs i).2.length ≤ i := by
  induction i with
  | zero => simp [st_zero, seed]
  | succ i ih =>
    have lt : i < gs.length := hi
    have a := ih (by omega)
    rw [st_succ m h gs ⟨i,lt⟩]
    simp only [List.length_append, List.length_singleton]
    have := toList_length_le (action m h gs ⟨i,lt⟩).1
    omega

theorem st_growth (m h : ℕ) (gs : List Gate) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ gs.length) :
    (st m h gs k).2.length ≤ (st m h gs i).2.length + (k-i) := by
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have b := ih (by omega)
    have lt : k < gs.length := hk
    rw [st_succ m h gs ⟨k,lt⟩, List.length_append]
    dsimp only
    have := toList_length_le (action m h gs ⟨k,lt⟩).1
    omega

theorem st_keeps (m h : ℕ) (gs : List Gate) {i k v : ℕ} (hi : i ≤ k) (hk : k ≤ gs.length)
    (hv : v < m+i) :
    (st m h gs k).1.getD v (.inl false) = (st m h gs i).1.getD v (.inl false) := by
  induction k, hi using Nat.le_induction with
  | base => rfl
  | succ k hik ih =>
    have lt : k < gs.length := hk
    rw [st_succ m h gs ⟨k,lt⟩, List.getD_append _ _ _ _ (by
      rw [(st_sizes m h gs k (by omega)).1]; omega)]
    exact ih (by omega)

theorem st_result (m h : ℕ) (gs : List Gate) (i : Fin gs.length) {k : ℕ}
    (hl : i.val < k) (hk : k ≤ gs.length) :
    (st m h gs k).1.getD (m+i.val) (.inl false) = (action m h gs i).2 := by
  rw [st_keeps m h gs (i := i.val+1) (by omega) hk (by omega), st_succ,
    ← (st_sizes m h gs i (by omega)).1, getD_snoc_eq]

theorem st_fixed (m h : ℕ) (gs : List Gate) {i : ℕ} (hi : i ≤ gs.length) (hh : h < m) :
    (st m h gs i).1.getD h (.inl false) = .inl false := by
  rw [st_keeps m h gs (i := 0) (by omega) hi (by omega), st_zero]
  simp [seed, hh]

theorem skip_length (m h : ℕ) (gs : List Gate) (i : Fin gs.length) (e : skipped m h gs i) :
    (st m h gs (i.val+1)).2.length = (st m h gs i).2.length := by
  rw [st_succ, show (action m h gs i).1 = none from e]
  simp

theorem one_skip (m h : ℕ) (gs : List Gate) (i : Fin gs.length) (e : skipped m h gs i) :
    (st m h gs gs.length).2.length + 1 ≤ gs.length := by
  have a := (st_sizes m h gs i (by omega)).2
  have b := skip_length m h gs i e
  have c := st_growth m h gs (i := i.val+1) (k := gs.length) (by omega) (by omega)
  omega

theorem two_skips (m h : ℕ) (gs : List Gate) (i j : Fin gs.length) (hne : i ≠ j)
    (ei : skipped m h gs i) (ej : skipped m h gs j) :
    (st m h gs gs.length).2.length + 2 ≤ gs.length := by
  wlog hij : i.val < j.val generalizing i j
  · exact this j i hne.symm ej ei (by have : i.val ≠ j.val := fun e => hne (Fin.ext e); omega)
  have a := (st_sizes m h gs i (by omega)).2
  have b := skip_length m h gs i ei
  have c := st_growth m h gs (i := i.val+1) (k := j.val) (by omega) (by omega)
  have d := skip_length m h gs j ej
  have e := st_growth m h gs (i := j.val+1) (k := gs.length) (by omega) (by omega)
  omega

def Reads (g : Gate) (v : ℕ) : Prop := v ∈ (normGate g).inputs

theorem reads_iff (g : Gate) (v : ℕ) : Reads g v ↔
    g.op = .not ∧ g.inputs.head? = some v ∨ g.op ≠ .not ∧ v ∈ g.inputs := by
  obtain ⟨op,l⟩ := g
  cases op <;> cases l <;> simp [Reads,normGate, eq_comm]

theorem read_const_skip (m h : ℕ) (gs : List Gate) (j : Fin gs.length) {v : ℕ} {b : Bool}
    (ok : Ok (gs.get j)) (read : Reads (gs.get j) v)
    (constant : (st m h gs j).1.getD v (.inl false) = .inl b) :
    skipped m h gs j := by
  have ng := normGate_nok _ ok
  apply simplify_count _ _ _ ng.1.1 (by simpa using ng.1.2) (fun e => by simpa using ng.2 e)
  exact ⟨b, List.mem_map.mpr ⟨v,read,constant⟩⟩

theorem pass_ok (m h : ℕ) (gs : List Gate) :
    ∀ g ∈ (st m h gs gs.length).2, Ok g :=
  elim_ok m _ _ (by simp)

theorem pass_inv (m h : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, Ok g)
    (w : List Bool) (hw : w.length = m) (hv : w.getD h false = false) :
    Inv m w (wiresFrom gs w) (st m h gs gs.length) := by
  have e := inv_elim m w hw (gs.map normGate) w (seed m h, [])
    (by intro g hg; obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
        exact (normGate_nok _ (ok _ hg0)).1) (seed_inv w m h hw hv)
  simpa [st,wiresFrom_norm] using e


def V (n : ℕ) (C : Circuit) (x : Fin n → Bool) (v : ℕ) :=
  (C.wires (List.ofFn x)).getD v false

def Varies (n : ℕ) (C : Circuit) := ∃ x y, circuitFun n C x ≠ circuitFun n C y

def Edge (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = n + j.val ∧ Reads (C.gates.get j) a

theorem out_valid {n : ℕ} {C : Circuit} (nc : Varies n C) : C.output < n+C.gates.length := by
  obtain ⟨x,y,h⟩ := nc
  by_contra! bad
  have val (z : Fin n → Bool) : circuitFun n C z = false := by
    apply List.getD_eq_default
    simpa [wires_eq,length_wiresFrom] using bad
  exact h ((val x).trans (val y).symm)

theorem in_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    V n C x i = x i := by
  rw [V,wires_eq,getD_wiresFrom _ _ _ (by simpa using i.isLt)]
  simp

theorem val_prefix {n : ℕ} {C : Circuit} (x : Fin n → Bool) {v k : ℕ}
    (hk : k ≤ C.gates.length) (hv : v < n+k) :
    V n C x v = (wiresFrom (C.gates.take k) (List.ofFn x)).getD v false := by
  unfold V
  rw [wires_eq]
  conv_lhs => rw [← List.take_append_drop k C.gates, wiresFrom_append]
  apply getD_wiresFrom
  simpa [length_wiresFrom, Nat.min_eq_left hk] using hv

theorem trunc_size {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) {v k : ℕ}
    (hk : k ≤ C.gates.length) (hv : v < n+k) (e : ∀ x, circuitFun n C x = V n C x v) :
    C.gates.length ≤ k := by
  let D : Circuit := ⟨C.gates.take k, v⟩
  have ok : FanInTwo D := fun g hg => hm.1 g (List.mem_of_mem_take hg)
  have same : circuitFun n D = circuitFun n C := by
    funext x
    exact (val_prefix x hk hv).symm.trans (e x).symm
  simpa [D,Circuit.size, Nat.min_eq_left hk] using hm.2 D ok same

theorem output_last {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C)
    (j : Fin C.gates.length) (e : C.output = n + j.val) : j.val+1 = C.gates.length := by
  have le := trunc_size hm (v := C.output) (k := j.val+1) (by omega) (by omega) (fun _ => rfl)
  omega

-- An effective forward reference reads false. Constant propagation would remove its gate.
theorem reads_lt {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) (nc : Varies n C)
    (j : Fin C.gates.length) {a : ℕ} (r : Reads (C.gates.get j) a) : a < n+j.val := by
  let last := st n n C.gates C.gates.length
  have inv (x : Fin n → Bool) :=
    pass_inv n n C.gates hm.1 (List.ofFn x) (by simp) (by simp)
  have eqv (x : Fin n → Bool) :
      (last.1.getD C.output (.inl false)).val (wiresFrom last.2 (List.ofFn x)) = circuitFun n C x :=
    ((inv x).2 C.output).2
  have keep : C.gates.length ≤ last.2.length := by
    cases e : last.1.getD C.output (.inl false) with
    | inl b =>
      obtain ⟨x,y,xy⟩ := nc
      have vx := eqv x
      have vy := eqv y
      rw [e] at vx vy
      exact False.elim (xy (vx.symm.trans vy))
    | inr v =>
      let D : Circuit := ⟨last.2,v⟩
      apply hm.2 D (pass_ok n n _)
      funext x
      have ex := eqv x
      rw [e] at ex
      exact ex
  by_contra! bad
  have hval : (st n n C.gates j).1.getD a (.inl false) = .inl false :=
    List.getD_eq_default _ _ (by rw [(st_sizes _ _ _ _ j.isLt.le).1]; omega)
  have s := one_skip _ _ _ j (read_const_skip _ _ _ j (hm.1 _ (C.gates.get_mem j)) r hval)
  change C.gates.length ≤ (st n n C.gates C.gates.length).2.length at keep
  omega

theorem edge_lt {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) (nc : Varies n C)
    {a b} (e : Edge n C a b) : a < b := by
  obtain ⟨j,rfl,r⟩ := e
  exact reads_lt hm nc j r

theorem gate_val {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) (nc : Varies n C)
    (x : Fin n → Bool) (j : Fin C.gates.length) :
    V n C x (n+j.val) = (normGate (C.gates.get j)).op.eval
      ((normGate (C.gates.get j)).inputs.map (V n C x)) := by
  let w := wiresFrom (C.gates.take j.val) (List.ofFn x)
  have lw : w.length = n+j.val := by simp [w,length_wiresFrom,Nat.min_eq_left j.isLt.le]
  rw [val_prefix (k := j.val+1) x (by omega) (by omega),
    List.take_succ_eq_append_getElem j.isLt, wiresFrom_append]
  change (w ++ [(C.gates.get j).op.eval ((C.gates.get j).inputs.map fun i => w.getD i false)]).getD
    (n+j.val) false = _
  rw [← lw, getD_snoc_eq, ← normGate_eval]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (val_prefix x j.isLt.le (reads_lt hm nc j ha)).symm

-- Keep the gates through h, process the remaining gates with h fixed to false, then append an OR.
-- Minimality permits at most one saved gate. A constant residual would make the
-- output constant or equal to h, which the gates through h already compute.
theorem cut_bound {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) (nc : Varies n C)
    (pre rest : List Gate) (split : pre ++ rest = C.gates) {h : ℕ}
    (hh : h < n+pre.length) (short : pre.length < C.gates.length)
    (dominates : ∀ x, V n C x h = true → circuitFun n C x = true) :
    let a := st (n+pre.length) h rest rest.length
    rest.length ≤ a.2.length+1 ∧ ∀ b, a.1.getD C.output (.inl false) ≠ .inl b := by
  let m := n+pre.length
  let a := st m h rest rest.length
  let s := a.1.getD C.output (.inl false)
  have hp (g) (hg : g ∈ pre) : Ok g := hm.1 g (split ▸ List.mem_append_left _ hg)
  have hr (g) (hg : g ∈ rest) : Ok g := hm.1 g (split ▸ List.mem_append_right _ hg)
  let w (x : Fin n → Bool) := wiresFrom pre (List.ofFn x)
  have lw (x) : (w x).length = m := by simp [w,m,length_wiresFrom]
  have old (x) : C.wires (List.ofFn x) = wiresFrom rest (w x) := by
    rw [wires_eq, ← split, wiresFrom_append]
  have kept (x) : V n C x h = (w x).getD h false := by
    rw [V,old,getD_wiresFrom _ _ _ (by rw [lw]; exact hh)]
  have eval (x) : circuitFun n C x = ((w x).getD h false || s.val (wiresFrom a.2 (w x))) := by
    cases e : (w x).getD h false with
    | true => simpa using dominates x ((kept x).trans e)
    | false =>
      have v := ((pass_inv m h rest hr (w x) (lw x) e).2 C.output).2
      rw [← old] at v
      simpa [s,a,circuitFun,Circuit.eval] using v.symm
  let D : Circuit := ⟨(pre ++ a.2) ++ [finish h s], m + a.2.length⟩
  have Dok : FanInTwo D := by
    intro g hg
    change g ∈ (pre ++ a.2) ++ [finish h s] at hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with ((e | e) | rfl)
    · exact hp _ e
    · exact pass_ok m h rest _ e
    · exact finish_ok _ _
  have Dsame : circuitFun n D = circuitFun n C := by
    funext x
    rw [eval x]
    change (wiresFrom ((pre ++ a.2) ++ [finish h s]) (List.ofFn x)).getD _ false = _
    rw [wiresFrom_append,wiresFrom_append]
    have len : (wiresFrom a.2 (w x)).length = m + a.2.length := by rw [length_wiresFrom,lw]
    change (wiresFrom [finish h s] (wiresFrom a.2 (w x))).getD (m+a.2.length) false = _
    rw [← len, finish_eval, getD_wiresFrom _ _ _ (by rw [lw]; exact hh)]
  change rest.length ≤ a.2.length+1 ∧ ∀ b, s ≠ .inl b
  constructor
  · have le := hm.2 D Dok Dsame
    simpa [D,Circuit.size,← split,Nat.add_assoc] using le
  intro b e
  cases b with
  | true =>
    obtain ⟨x,y,ne⟩ := nc
    exact ne (by simp [eval,e,Stat.val])
  | false =>
    let P : Circuit := ⟨pre,h⟩
    have eqv : circuitFun n P = circuitFun n C := by
      funext x
      simpa [eval,e,Stat.val] using (show circuitFun n P x = (w x).getD h false from rfl)
    have le := hm.2 P hp eqv
    change C.gates.length ≤ pre.length at le
    omega


-- The side input can occur on either side of the OR gate.
def OrReader (g : Gate) (h : ℕ) : Prop :=
  g.op = .or ∧ ∃ w, w ≠ h ∧ (g.inputs = [h,w] ∨ g.inputs = [w,h])

theorem shape_of_status (g : Gate) (m h : ℕ) (rho : ℕ → Stat) (ok : Ok g)
    (read : Reads g h) (fixed : rho h = .inl false)
    (live : ∀ b, (simplify (normGate g).op m ((normGate g).inputs.map rho)).2 ≠ .inl b) :
    OrReader g h := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,len⟩ := ok
  change op = .and ∨ op = .or ∨ op = .not at hop
  change l.length ≤ 2 at len
  cases l with
  | nil => rcases hop with rfl | rfl | rfl <;> simp [Reads,normGate] at read
  | cons a l =>
    cases l with
    | nil =>
      rcases hop with rfl | rfl | rfl <;> simp [Reads,normGate] at read <;> subst h
      · exact False.elim (live false (by simp [normGate,simplify,simpAnd,fixed]))
      · exact False.elim (live false (by simp [normGate,simplify,simpOr,fixed]))
      · exact False.elim (live true (by simp [normGate,simplify,simpNot,fixed]))
    | cons b l =>
      cases l with
      | cons c l => simp at len
      | nil =>
        rcases hop with rfl | rfl | rfl
        · rcases (by simpa [Reads,normGate] using read : h = a ∨ h = b) with rfl | rfl
          · exact False.elim (live false (by cases e : rho b <;> simp [normGate,simplify,simpAnd,fixed,e]))
          · exact False.elim (live false (by cases e : rho a <;> simp [normGate,simplify,simpAnd,fixed,e]))
        · change GateOp.or = .or ∧ _
          refine ⟨rfl,?_⟩
          rcases (by simpa [Reads,normGate] using read : h = a ∨ h = b) with rfl | rfl
          · refine ⟨b,?_,Or.inl rfl⟩
            rintro rfl
            exact live false (by simp [normGate,simplify,simpOr,fixed])
          · refine ⟨a,?_,Or.inr rfl⟩
            rintro rfl
            exact live false (by simp [normGate,simplify,simpOr,fixed])
        · have ha : h = a := by simpa [Reads,normGate] using read
          subst h
          exact False.elim (live true (by simp [normGate,simplify,simpNot,fixed]))

-- Each reader of h disappears when h is fixed to false. If the sole reader
-- produced a constant, its next reader would disappear too.
theorem cut_readers {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit n C) (nc : Varies n C)
    {h : ℕ} (ho : h < C.output) (dom : ∀ x, V n C x h = true → circuitFun n C x = true) :
    (∀ (i j : Fin C.gates.length), Reads (C.gates.get i) h → Reads (C.gates.get j) h → i = j) ∧
    ∀ (j : Fin C.gates.length), Reads (C.gates.get j) h →
      (C.output = n+j.val ∨ ∃ q : Fin C.gates.length, Reads (C.gates.get q) (n+j.val)) →
      OrReader (C.gates.get j) h := by
  by_cases empty : C.gates.length = 0
  · constructor <;> intro j <;> exact False.elim (by have := j.isLt; omega)
  let k := h+1-n
  let pre := C.gates.take k
  let gs := C.gates.drop k
  have split : pre ++ gs = C.gates := List.take_append_drop ..
  have vo := out_valid nc
  have hk : k < C.gates.length := by dsimp [k]; omega
  have lp : pre.length = k := by simp [pre, Nat.min_eq_left hk.le]
  have lg : gs.length = C.gates.length-k := List.length_drop
  let m := n+k
  have hh : h < m := by dsimp [m,k]; omega
  have bound := cut_bound hm nc pre gs split (by simpa [lp] using hh) (by omega) dom
  rw [lp] at bound
  change gs.length ≤ (st m h gs gs.length).2.length+1 ∧ _ at bound
  let idx (j : Fin C.gates.length) (hj : k ≤ j.val) : Fin gs.length :=
    ⟨j.val-k,by rw [lg]; omega⟩
  have idxVal (j : Fin C.gates.length) (hj : k ≤ j.val) :
      k+(idx j hj).val = j.val := by dsimp [idx]; omega
  have gate (j : Fin C.gates.length) (hj : k ≤ j.val) : gs.get (idx j hj) = C.gates.get j := by
    simp only [gs,List.get_eq_getElem,List.getElem_drop]
    congr 1
    exact idxVal j hj
  have later (j : Fin C.gates.length) (r : Reads (C.gates.get j) h) : k ≤ j.val := by
    have := reads_lt hm nc j r
    dsimp [k]; omega
  have elimReader (j : Fin C.gates.length) (r : Reads (C.gates.get j) h) :
      skipped m h gs (idx j (later j r)) := by
    let u := idx j (later j r)
    have gu : gs.get u = C.gates.get j := gate j (later j r)
    apply read_const_skip m h gs u (by rw [gu]; exact hm.1 _ (C.gates.get_mem j))
      (v := h) (by rw [gu]; exact r) (b := false)
    exact st_fixed m h gs u.isLt.le hh
  constructor
  · intro i j ri rj
    by_contra ne
    have en : idx i (later i ri) ≠ idx j (later j rj) := by
      intro e
      apply ne; apply Fin.ext
      simpa only [idxVal] using congrArg (fun t : Fin gs.length => k+t.val) e
    have s := two_skips m h gs _ _ en (elimReader i ri) (elimReader j rj)
    omega
  intro j r use
  let u := idx j (later j r)
  have gu : gs.get u = C.gates.get j := gate j (later j r)
  have uv : m+u.val = n+j.val := by have v := idxVal j (later j r); dsimp [m,u]; omega
  have live : ∀ b, (action m h gs u).2 ≠ .inl b := by
    intro b eb
    rcases use with out | ⟨q,rq⟩
    · apply bound.2 b
      rw [out, ← uv]
      exact (st_result m h gs u u.isLt le_rfl).trans eb
    · have lq := reads_lt hm nc q rq
      have hjq : j.val < q.val := by omega
      have kq : k ≤ q.val := le_trans (later j r) hjq.le
      let t := idx q kq
      have lt : u.val < t.val := by
        have := idxVal j (later j r); have := idxVal q kq
        dsimp [u,t,idx] at *; omega
      have ct : (st m h gs t).1.getD (n+j.val) (.inl false) = .inl b := by
        rw [← uv]
        exact (st_result m h gs u lt t.isLt.le).trans eb
      have gt : gs.get t = C.gates.get q := gate q kq
      have elimQ := read_const_skip m h gs t (by rw [gt]; exact hm.1 _ (C.gates.get_mem q))
        (v := n+j.val) (by rw [gt]; exact rq) ct
      have s := two_skips m h gs u t (by intro eq; exact (ne_of_lt lt) (congrArg Fin.val eq))
        (elimReader j r) elimQ
      omega
  rw [← gu] at r ⊢
  exact shape_of_status (gs.get u) (m+(st m h gs u).2.length) h
    (fun i => (st m h gs u).1.getD i (.inl false))
    (by rw [gu]; exact hm.1 _ (C.gates.get_mem j)) r (st_fixed m h gs u.isLt.le hh) live

end PEqualNP.Outside.Meta568

namespace PEqualNP.Outside.Meta568
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

def Diff (n : ℕ) (C : Circuit) (y : Fin n → Bool) (h : ℕ) : Prop :=
  V (n+1) C (Fin.snoc y false) h ≠ V (n+1) C (Fin.snoc y true) h

def Changing (n : ℕ) (C : Circuit) (y : Fin n → Bool) (a b : ℕ) : Prop :=
  Edge (n+1) C a b ∧ Diff n C y b

-- Trace a disagreement between the two evaluations backwards to the input that changed.
theorem diff_path {n : ℕ} {C : Circuit} (hm : IsMinimalCircuit (n+1) C) (nc : Varies (n+1) C)
    (y : Fin n → Bool) (v : ℕ) (dv : Diff n C y v) :
    ReflTransGen (Changing n C y) n v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    by_cases e : v = n
    · subst v; exact ReflTransGen.refl
    by_cases small : v < n+1
    · let i : Fin n := ⟨v,by omega⟩
      apply False.elim
      apply dv
      change V _ C (Fin.snoc y false) i.castSucc = V _ C (Fin.snoc y true) i.castSucc
      rw [in_val,in_val]
      simp
    have hv : v < n+1+C.gates.length := by
      by_contra! le
      have val (x : Fin (n+1) → Bool) : V (n+1) C x v = false := by
        apply List.getD_eq_default
        simpa [wires_eq,length_wiresFrom] using le
      exact dv ((val _).trans (val _).symm)
    let j : Fin C.gates.length := ⟨v-(n+1),by omega⟩
    have ej : n+1+j.val = v := by dsimp [j]; omega
    have ex : ∃ a, Reads (C.gates.get j) a ∧ Diff n C y a := by
      by_contra! no
      apply dv
      rw [← ej,gate_val hm nc,gate_val hm nc]
      congr 1
      apply List.map_congr_left
      intro a ra
      exact not_ne_iff.mp (no a ra)
    obtain ⟨a,r,da⟩ := ex
    have lt : a < v := ej ▸ reads_lt hm nc j r
    exact (ih a lt da).tail ⟨⟨j,ej.symm,r⟩,dv⟩

def Spec (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, circuitFun (n+1) C x = (x (Fin.last n) || H (fun i => x i.castSucc))

theorem spec_snoc {n C H} (hf : Spec n C H) (y : Fin n → Bool) (b : Bool) :
    circuitFun (n+1) C (Fin.snoc y b) = (b || H y) := by
  rw [hf (Fin.snoc y b)]
  simp

-- On every assignment with H false, a path of changing wires continues to the output.
def Active (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool) (h : ℕ) : Prop :=
  (∀ y, V (n+1) C (Fin.snoc y true) h = true) ∧
  ∀ y, H y = false → Diff n C y h ∧ ReflTransGen (Changing n C y) h C.output

theorem last_val (n : ℕ) (C : Circuit) (y : Fin n → Bool) (b : Bool) :
    V (n+1) C (Fin.snoc y b) n = b := by
  change V (n+1) C (Fin.snoc y b) (Fin.last n) = b
  rw [in_val]; simp

theorem root_active {n C H} (hm : IsMinimalCircuit (n+1) C) (nc : Varies (n+1) C)
    (hf : Spec n C H) : Active n C H n := by
  refine ⟨fun y => last_val n C y true, fun y hy => ⟨?_,?_⟩⟩
  · simp [Diff,last_val]
  · apply diff_path hm nc
    change circuitFun (n+1) C (Fin.snoc y false) ≠ circuitFun (n+1) C (Fin.snoc y true)
    simp [spec_snoc hf,hy]

theorem dominates_of_active {n C H h} (hf : Spec n C H) (ha : Active n C H h) :
    ∀ x, V (n+1) C x h = true → circuitFun (n+1) C x = true := by
  intro x hx
  let y := Fin.init x
  have ex : Fin.snoc y (x (Fin.last n)) = x := Fin.snoc_init_self x
  cases b : x (Fin.last n) with
  | true => simp [hf x,b]
  | false =>
    cases hy : H y with
    | true =>
      rw [← ex,spec_snoc hf,hy]; simp
    | false =>
      have d := (ha.2 y hy).1
      rw [b] at ex
      exact False.elim (d (by rw [ex,hx,ha.1]))

theorem path_le {n C y a b} (hm : IsMinimalCircuit (n+1) C) (nc : Varies (n+1) C)
    (p : ReflTransGen (Changing n C y) a b) : a ≤ b := by
  induction p with
  | refl => rfl
  | tail _ e ih => exact ih.trans (edge_lt hm nc e.1).le

def Link (n : ℕ) (C : Circuit) (h b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = n+j.val ∧ OrReader (C.gates.get j) h ∧
    ∀ q : Fin C.gates.length, Reads (C.gates.get q) h ↔ q = j

theorem or_reads {g : Gate} {h} (r : OrReader g h) : Reads g h := by
  obtain ⟨op,w,_,l|l⟩ := r <;> simp [Reads,normGate,op,l]

theorem advance {n C H h} (hm : IsMinimalCircuit (n+1) C) (nc : Varies (n+1) C)
    (hf : Spec n C H) (someZero : ∃ y, H y = false) (active : Active n C H h)
    (neq : h ≠ C.output) :
    ∃ b, Link (n+1) C h b ∧ Active n C H b ∧ h < b ∧ b ≤ C.output := by
  obtain ⟨y0,hy0⟩ := someZero
  have path0 := (active.2 y0 hy0).2
  have ho : h < C.output := lt_of_le_of_ne (path_le hm nc path0) neq
  obtain ⟨same,shape⟩ := cut_readers hm nc ho (dominates_of_active hf active)
  obtain ⟨b,⟨⟨j,ej,r⟩,db⟩,tail⟩ := path0.cases_head.resolve_left neq
  have used : C.output = n+1+j.val ∨ ∃ q, Reads (C.gates.get q) (n+1+j.val) := by
    rcases tail.cases_head with eq | ⟨v,⟨⟨q,_,rq⟩,_⟩,_⟩
    · exact Or.inl (eq.symm.trans ej)
    · exact Or.inr ⟨q,ej ▸ rq⟩
  have gate := shape j r used
  refine ⟨b, ⟨j,ej,gate,fun q => ⟨fun rq => same q j rq r, fun e => e ▸ r⟩⟩,
    ⟨?_,?_⟩, ej ▸ reads_lt hm nc j r, path_le hm nc tail⟩
  · intro y
    rw [ej,gate_val hm nc,normGate_eval,gate.1]
    obtain ⟨op,w,ne,l|l⟩ := gate <;> rw [l] <;> simp [GateOp.eval,active.1 y]
  · intro y hy
    obtain ⟨t,⟨⟨q,eq,rq⟩,diff⟩,rest⟩ := ((active.2 y hy).2).cases_head.resolve_left neq
    have e : t = b := by rw [eq, same q j rq r, ← ej]
    exact e ▸ And.intro diff rest

-- Each step strictly increases the wire index and stays at or below the output.
theorem route {n C H} (hm : IsMinimalCircuit (n+1) C) (nc : Varies (n+1) C) (hf : Spec n C H)
    (hz : ∃ y, H y = false) (h : ℕ) (ha : Active n C H h) :
    ∃ (s : ℕ) (d : Fin (s+1) → ℕ), d 0 = h ∧ d (Fin.last s) = C.output ∧
      ∀ i : Fin s, Link (n+1) C (d i.castSucc) (d i.succ) := by
  by_cases e : h = C.output
  · exact ⟨0,fun _ => h,rfl,e,fun i => Fin.elim0 i⟩
  obtain ⟨b,link,ab,lt,le⟩ := advance hm nc hf hz ha e
  obtain ⟨s,d,first,last,steps⟩ := route hm nc hf hz b ab
  refine ⟨s+1,Fin.cons h d,by simp,?_,?_⟩
  · simpa only [← Fin.succ_last,Fin.cons_succ] using last
  · intro i
    cases i using Fin.cases with
    | zero => simpa [first] using link
    | succ i => simpa using steps i
termination_by C.output-h
decreasing_by omega

end PEqualNP.Outside.Meta568

namespace PEqualNP.Outside.Meta568
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

theorem or_parts {g : Gate} {h : ℕ} (gate : OrReader g h) :
    g.inputs.length = 2 ∧ h ∈ g.inputs ∧ ∃ w ∈ g.inputs, w ≠ h ∧ Reads g w := by
  obtain ⟨op,w,ne,l|l⟩ := gate <;>
    refine ⟨by simp [l],by simp [l],w,by simp [l],ne,?_⟩ <;> simp [Reads,normGate,op,l]

end PEqualNP.Outside.Meta568

open PEqualNP.Outside.Meta568 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hm nonconstant hf
  classical
  have hz1 : (∃ y, H y = false) ∧ (∃ y, H y = true) := by
    obtain ⟨u,v,e⟩ := nonconstant
    cases hu : H u <;> cases hv : H v <;> simp_all
    · exact ⟨⟨u,hu⟩,v,hv⟩
    · exact ⟨⟨v,hv⟩,u,hu⟩
  obtain ⟨⟨y0,h0⟩,⟨y1,h1⟩⟩ := hz1
  have nc : Varies (n+1) C :=
    ⟨Fin.snoc y0 false, Fin.snoc y0 true, by simp [spec_snoc hf,h0]⟩
  have ne : C.output ≠ n := by
    intro e
    have a : circuitFun (n+1) C (Fin.snoc y1 false) = true := by simp [spec_snoc hf,h1]
    change V (n+1) C (Fin.snoc y1 false) C.output = true at a
    rw [e,last_val] at a
    contradiction
  obtain ⟨s,d,first,last,steps⟩ := route hm nc hf ⟨y0,h0⟩ n (root_active hm nc hf)
  cases s with
  | zero => exact False.elim (ne (last.symm.trans first))
  | succ k =>
    let c (i : Fin (k+1)) : Fin C.gates.length := Classical.choose (steps i)
    have atStep (i : Fin (k+1)) := Classical.choose_spec (steps i)
    have pos (i : Fin (k+1)) : d i.succ = n+1+(c i).val := (atStep i).1
    have gate (i : Fin (k+1)) : OrReader (C.gates.get (c i)) (d i.castSucc) := (atStep i).2.1
    have unique (i : Fin (k+1)) (q : Fin C.gates.length) :
        Reads (C.gates.get q) (d i.castSucc) ↔ q = c i := (atStep i).2.2 q
    have edge (i : Fin (k+1)) : Edge (n+1) C (d i.castSucc) (d i.succ) :=
      ⟨c i,pos i,or_reads (gate i)⟩
    have mono : StrictMono d := Fin.strictMono_iff_lt_succ.mpr fun i => edge_lt hm nc (edge i)
    have out : C.output = n+1+(c (Fin.last k)).val := by simpa only [Fin.succ_last,last] using pos (Fin.last k)
    have size := output_last hm (c (Fin.last k)) out
    have outgoing (i : Fin (k+1)) {v : ℕ} (e : Edge (n+1) C (d i.castSucc) v) : v = d i.succ := by
      obtain ⟨q,rfl,r⟩ := e
      rw [(unique i q).mp r,pos]
    have terminal {v : ℕ} (e : Edge (n+1) C (d (Fin.last (k+1))) v) : False := by
      have lt := edge_lt hm nc e
      obtain ⟨q,rfl,_⟩ := e
      rw [last,out] at lt
      omega
    have covers {v : ℕ} (p : TransGen (Edge (n+1) C) n v) :
        ∃ i : Fin (k+1), d i.succ = v := by
      induction p with
      | single e =>
        apply Exists.intro 0
        apply Eq.symm
        apply outgoing 0
        simpa only [Fin.castSucc_zero,first] using e
      | @tail u v p e ih =>
        obtain ⟨i,rfl⟩ := ih
        by_cases small : i.val+1 < k+1
        · let t : Fin (k+1) := ⟨i.val+1,small⟩
          have eq : t.castSucc = i.succ := Fin.ext rfl
          exact ⟨t,(outgoing t (by rw [eq]; exact e)).symm⟩
        · have ei : i.succ = Fin.last (k+1) := Fin.ext (by change i.val+1=k+1; omega)
          exact False.elim (terminal (ei ▸ e))
    have visits (i : Fin (k+1)) : TransGen (Edge (n+1) C) n (d i.succ) := by
      induction i using Fin.induction with
      | zero => exact .single (by simpa only [Fin.castSucc_zero,first] using edge 0)
      | succ i ih => exact ih.tail (edge i.succ)
    -- A reachable side input would have to send its unique edge to this same gate.
    have side (i : Fin (k+1)) :
        ∃ w ∈ (C.gates.get (c i)).inputs, w ≠ d i.castSucc ∧ w ≠ n ∧ w < d i.succ ∧
          ¬ TransGen (Edge (n+1) C) n w := by
      obtain ⟨w,mem,diff,r⟩ := (or_parts (gate i)).2.2
      have ew : Edge (n+1) C w (d i.succ) := ⟨c i,pos i,r⟩
      have lt := edge_lt hm nc ew
      have away (p : Fin (k+1+1)) : d p ≠ w := by
        intro eq
        have lt' : p < i.succ := mono.lt_iff_lt.mp (by rwa [eq])
        have small : p.val < k+1 := by change p.val < i.val+1 at lt'; omega
        let t : Fin (k+1) := ⟨p.val,small⟩
        have et : t.castSucc = p := Fin.ext rfl
        have next := outgoing t (v := d i.succ) (by rw [et,eq]; exact ew)
        have it : i = t := Fin.succ_inj.mp (mono.injective next)
        exact diff (by rw [it,et,eq])
      exact ⟨w,mem,diff,fun en => away 0 (first.trans en.symm),lt,fun pw => by
        obtain ⟨j,ej⟩ := covers pw
        exact away j.succ ej⟩
    have cm : StrictMono c := by
      intro i j ij
      have lt := mono (Fin.succ_lt_succ_iff.mpr ij)
      rw [pos,pos] at lt
      change (c i).val < (c j).val
      omega
    simp_rw [← reads_iff]
    refine ⟨k,c,cm,size,out,fun i => ⟨(gate i).1,(or_parts (gate i)).1⟩,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Fin.castSucc_zero,first] using (or_parts (gate 0)).2.1
    · intro i
      exact pos i.castSucc ▸ (or_parts (gate i.succ)).2.1
    · intro j r
      exact (unique 0 j).mp (by simpa only [Fin.castSucc_zero,first] using r)
    · intro i j r
      exact (unique i.succ j).mp (by change Reads _ (d i.castSucc.succ); rwa [pos])
    · intro j
      constructor
      · intro p
        obtain ⟨i,e⟩ := covers p
        rw [pos] at e
        exact ⟨i,Fin.ext (by omega)⟩
      · rintro ⟨i,rfl⟩
        exact pos i ▸ visits i
    · obtain ⟨w,mem,_,wn,lt,nr⟩ := side 0
      exact ⟨w,mem,wn,pos 0 ▸ lt,nr⟩
    · intro i
      obtain ⟨w,mem,neq,wn,lt,nr⟩ := side i.succ
      exact ⟨w,mem,pos i.castSucc ▸ neq,wn,pos i.succ ▸ lt,nr⟩
