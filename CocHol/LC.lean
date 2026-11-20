import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

namespace LC.PreTerm

inductive LTerm where
|   Ref : Nat → LTerm
|   App : LTerm → LTerm → LTerm
|   Lam : Nat → LTerm → LTerm

def FV (T : LTerm) : Finset Nat :=
    match T with
    | .Ref x => {x}
    | .App A B => (FV A) ∪ (FV B)
    | .Lam x M => (FV M) \ {x}

def V (T : LTerm) : Finset Nat :=
    match T with
    | .Ref x => {x}
    | .App A B => (V A) ∪ (V B)
    | .Lam x M => (V M) ∪ {x}

def Binders (T : LTerm) : Finset Nat :=
  match T with
  | .Ref _ => {}
  | .App A B => (Binders A) ∪ (Binders B)
  | .Lam y P => {y} ∪ (Binders P)

def fresh (s : Finset Nat) : Nat :=
  match s.max with
  | some m => m + 1
  | none => 0

def lsize : LTerm → Nat
  | .Ref _ => 1
  | .App A B => lsize A + lsize B + 1
  | .Lam _ B => lsize B + 1

-- Naming convention: Disjoint (V M) (V N)
def subst (x : Nat) (M N : LTerm) : LTerm :=
  match M with
  | .Ref y => if x = y then N else .Ref y
  | .App P Q => .App (subst x P N) (subst x Q N)
  | .Lam y P => if x = y then .Lam y P else .Lam y (subst x P N)

theorem lsize_subst_ref (x y : Nat) (M : LTerm) : lsize (subst x M (.Ref y)) = lsize M := by
  induction M <;> simp_all [lsize, subst] <;> split_ifs <;> simp_all [lsize];

inductive αEq : LTerm → LTerm → Prop where
| refl (a : LTerm) : αEq a a
| symm {a b : LTerm} (p1 : αEq a b) : αEq b a
| trans {a b c : LTerm} (p1 : αEq a b) (p2 : αEq b c) : αEq a c
| appL {P P' : LTerm} (Q : LTerm) (p1 : αEq P P') : αEq (.App P Q) (.App P' Q)
| appR {P P' : LTerm} (Q : LTerm) (p1 : αEq P P') : αEq (.App Q P) (.App Q P')
| lam {P P' : LTerm} (x : Nat) (p1 : αEq P P') : αEq (.Lam x P) (.Lam x P')
| alpha (P : LTerm) (x y : Nat) (p1 : y ∉ V P) : αEq (.Lam x P) (.Lam y (subst x P (.Ref y)))

theorem lsize_gt_zero (M : LTerm) : lsize M > 0 := by
  induction M <;> simp [lsize];

theorem FV_sub_V (P : LTerm) : FV P ⊆ V P := by
  induction P <;> simp_all [FV, V] <;> grind;

theorem Binders_sub_V (P : LTerm) : Binders P ⊆ V P := by
  induction P <;> simp_all [Binders, V]; grind;

theorem Binders_union_FV (P : LTerm) : Binders P ∪ FV P = V P := by
  induction P <;> simp_all [FV, V, Binders] <;> grind;

lemma FV_subst_l1 (x : Nat) (N : LTerm) (n : Nat) : ∀M, lsize M ≤ n → Disjoint (Binders M) (FV N) → ∀v, v ∈ FV M \ {x} → v ∈ FV (subst x M N) := by
  induction n;
  grind [lsize_gt_zero];

  intros; rw [subst.eq_def];
  split; split <;> simp_all [FV];

  simp_all [FV, Binders, lsize];
  expose_names;
  apply Or.elim h_3.left <;> intros;

  apply Or.inl; apply h <;> simp_all; omega;
  apply Or.inr; apply h <;> simp_all; omega;

  simp_all [FV, Binders]; split <;> simp_all [FV, lsize];

lemma FV_subst_l2 (x : Nat) (N : LTerm) (n : Nat) : ∀M, lsize M ≤ n → Disjoint (Binders M) (FV N) → ∀v, v ∈ FV N ∧ x ∈ FV M → v ∈ FV (subst x M N) := by
  induction n;
  grind [lsize_gt_zero];

  intros; rw [subst.eq_def]; split <;> simp_all [lsize, FV, Binders];

  expose_names;
  apply Or.elim h_3.right <;> intros <;> simp_all;

  apply Or.inl; apply h <;> (try simp_all); omega;
  apply Or.inr; apply h <;> (try simp_all); omega;

  expose_names;
  have h1 : v ∈ V N := (by grind [FV_sub_V];);
  grind;

lemma FV_subst_l3 (x : Nat) (N : LTerm) (n : Nat) : ∀M, lsize M ≤ n → ∀v, v ∈ FV (subst x M N) → (v ∈ FV M \ {x} ∨ v ∈ FV N ∧ x ∈ FV M) := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  induction M <;> simp_all [FV, lsize, subst];
  expose_names; by_cases x = a <;> simp_all [FV];
  intro; simp_all;

  expose_names;
  have h1 := h a (by omega) v;
  have h2 := h a_1 (by omega) v;
  apply Or.elim h_2;
  intros; simp_all; grind;
  intros; simp_all; grind;

  expose_names;
  have h1 := h a_1 (by omega) v;
  by_cases x = a;
  simp_all [FV];
  simp_all [FV];

theorem FV_subst (x : Nat) (M N : LTerm) (p1 : Disjoint (Binders M) (FV N)) : ∀v, v ∈ FV (subst x M N) ↔ (v ∈ FV M \ {x}) ∨ (v ∈ FV N ∧ x ∈ FV M) := by
  intros; apply Iff.intro;
  grind [FV_subst_l3 x N (lsize M) M (by simp) (by assumption)];
  intros a1; apply Or.elim a1 <;> intros;
  grind [FV_subst_l1 x N (lsize M) M (by simp) (by assumption)];
  grind [FV_subst_l2 x N (lsize M) M (by simp) (by assumption)];

theorem Binders_subst (x : Nat) (M N : LTerm) : ∀v, (v ∈ Binders (subst x M N)) ↔ ((x ∈ FV M ∧ v ∈ Binders N) ∨ (v ∈ Binders M)) := by
  intros; apply Iff.intro;

  induction M <;> intros <;> simp_all [subst, FV];

  expose_names;
  split_ifs at h <;> simp_all;

  expose_names;
  simp_all [Binders];
  apply h.elim <;> intros <;> simp_all;
  apply a_ih.elim <;> intros <;> simp_all;
  apply a_ih_1.elim <;> intros <;> simp_all;

  expose_names;
  split_ifs at h <;> simp_all [Binders];
  apply h.elim <;> intros <;> simp_all;
  apply a_ih.elim <;> intros <;> simp_all;

  induction M <;> intros <;> simp_all [FV, Binders, subst];

  expose_names;
  apply h.elim <;> intros <;> simp_all;

  expose_names;
  apply h.left.elim <;> intros <;> simp_all;

  expose_names;
  apply h.elim <;> intros <;> simp_all;

  split_ifs <;> simp_all [Binders];

  expose_names;
  apply h.elim <;> intros <;> simp_all;
  expose_names;
  apply h.elim <;> intros <;> simp_all;

theorem FV_αEq {a b : LTerm} (p1 : αEq a b) : FV a = FV b := by
  induction p1 <;> simp_all [FV];
  rw [subst.eq_def]; split;

  split_ifs;
  simp_all [FV];
  simp_all [FV, V]; grind;

  simp_all [FV]
  apply Finset.Subset.antisymm;

  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x (.App A B) (.Ref y) (by simp_all [FV, Binders, V]; grind [Binders_sub_V];) x_1).mpr;
  simp_all [FV, subst, V];
  intro; simp_all; grind [FV_sub_V];

  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x (.App A B) (.Ref y) (by simp_all [FV, Binders, V]; grind [Binders_sub_V];) x_1).mp;
  simp_all [FV, subst, V];

  split <;> simp_all [FV, V];

  apply Finset.Subset.antisymm;
  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x M (.Ref y) (by simp_all [FV]; grind [Binders_sub_V];) x_1).mpr;
  simp_all [FV];
  intro; simp_all; grind [FV_sub_V];

  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x M (.Ref y) (by simp_all [FV]; grind [Binders_sub_V];) x_1).mp;
  simp_all [FV];

  apply Finset.Subset.antisymm;
  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x M (.Ref y) (by simp_all [FV]; grind [Binders_sub_V];) x_2).mpr;
  simp_all [FV];
  grind [FV_sub_V];

  apply Finset.subset_iff.mpr;
  intros;
  expose_names;
  have h1 := (FV_subst x M (.Ref y) (by simp_all [FV]; grind [Binders_sub_V];) x_2).mp;
  simp_all [FV];

theorem subst_not_FV (x : Nat) (M N : LTerm) (p1 : x ∉ FV M) : subst x M N = M := by
  induction M <;> simp_all [FV, subst];
  intro;
  simp_all;

theorem subst_subst (x y : Nat) (M N P : LTerm) (p1 : Disjoint (V M) (V N))
  (p2 : Disjoint (V M) (V P)) (p4 : x ∉ FV P) (p5 : x ≠ y)
: subst y (subst x M N) P = subst x (subst y M P) (subst y N P) := by
  induction M <;> simp_all [subst, V] <;> split_ifs <;> simp_all [subst];

  expose_names;
  have h1 : a ∉ FV N := (by grind [FV_sub_V]);
  have h2 : a ∉ FV P := (by grind [FV_sub_V]);
  simp_all [subst_not_FV];

  expose_names;
  have h1 : a ∉ FV N := (by grind [FV_sub_V]);
  simp_all [subst_not_FV];

theorem subst_comm (x y : Nat) (P X Y : LTerm) (p1 : x ≠ y) (p2 : x ∉ FV Y) (p3 : y ∉ FV X)
: subst x (subst y P Y) X = subst y (subst x P X) Y := by
  induction P <;> simp_all [subst];

  split_ifs <;> simp_all [subst];

  simp_all [subst_not_FV];
  simp_all [subst_not_FV];

  split_ifs <;> simp_all [subst];

theorem fresh_subset (s S : Finset Nat) (p1 : s ⊆ S) : fresh s ≤ fresh S := by
  simp_all [fresh.eq_def];
  split <;> split <;> simp_all;

  expose_names;
  have h1 := Finset.mem_of_max (s := s) (by assumption);
  have h2 : m ∈ S := by grind;
  have h3 := Finset.le_max h2;
  simp_all;
  apply WithBot.le_coe_iff.mp h3;
  simp_all;

  expose_names;
  have h1 := Finset.mem_of_max (s := s) (by assumption);
  have h2 : m ∈ S := by grind;
  have h3 := Finset.max_eq_bot.mp heq_1;
  grind;

theorem fresh_notin (s : Finset Nat) : fresh s ∉ s := by
    simp [fresh]; split;
    intro a1;
    have h1 := Finset.le_max a1;
    simp_all;
    have h2 := WithBot.coe_le_coe.mp h1;
    omega;

    have h1 := (Finset.max_eq_bot (s := s)).mp;
    simp_all;
    have h2 := h1 (Eq.refl (Option.none (α := Nat)));
    simp_all;

theorem lt_fresh (s : Finset Nat) {x : Nat} (p1 : x ∈ s) : x < fresh s := by
    have h1 := Finset.le_max p1;
    simp [fresh]; split;
    simp_all;
    have h2 := WithBot.coe_le_coe.mp h1;
    omega;
    simp_all [WithBot.none_eq_bot];

theorem fresh_notmem_subset (s S : Finset Nat) (p1 : s ⊆ S) : fresh S ∉ s := by
  intro a1;
  have h1 := fresh_subset s S p1;
  have h2 := lt_fresh s a1;
  omega;

lemma ge_fresh (S : Finset Nat) (y : Nat) (p1 : ∀x, x ∈ S → x < y) : fresh S ≤ y := by
  simp [fresh]; split;
  expose_names;
  have h2 := p1 m (Finset.mem_of_max heq);
  omega;
  omega;

theorem fresh_union (a b : Finset Nat) : fresh (a ∪ b) = max (fresh a) (fresh b) := by
  simp_all [fresh];
  split <;> simp_all [Finset.max_union, max, SemilatticeSup.sup]
  expose_names;
  split at heq <;> simp_all [WithBot.some]; try grind;

  expose_names;
  split at heq <;> simp_all [WithBot.some];

theorem Binders_subst_ref (x y : Nat) (M : LTerm) : Binders (subst x M (.Ref y)) = Binders M := by
  induction M <;> simp_all [Binders, subst];
  split <;> simp_all [Binders];
  split_ifs <;> simp_all [Binders];


lemma αEq_disjoint_l1 (M : LTerm) (o : Nat) : ∃M', αEq M M' ∧ ∀x, x ∈ Binders M' → o ≤ x := by
  induction M;

  expose_names;
  exists (.Ref a); and_intros;
  apply αEq.refl;
  simp_all [Binders];

  expose_names;
  apply a_ih.elim; apply a_ih_1.elim; intros;
  expose_names;
  exists .App a_3 a_2;
  and_intros;
  apply αEq.trans;
  apply αEq.appL;
  exact h_1.left;
  apply αEq.appR;
  exact h.left;

  intros;
  simp_all [Binders];
  expose_names;
  apply h_2.elim <;> intro;
  simp_all;
  simp_all;

  expose_names;
  apply a_ih.elim; intros;
  expose_names;
  exists .Lam (fresh (insert o (V a_1 ∪ V a_2))) (subst a a_2 (.Ref (fresh (insert o (V a_1 ∪ V a_2)))));
  and_intros;

  apply αEq.trans;
  apply αEq.lam;
  exact h.left;
  apply αEq.alpha;
  grind [fresh_notin];

  intros;
  simp_all [Binders];
  expose_names;
  apply h_1.elim <;> intros;

  have h1 : o < fresh (insert o (V a_1 ∪ V a_2)) := lt_fresh (insert o (V a_1 ∪ V a_2)) (by grind);
  omega;

  have h1 := Binders_subst_ref a (fresh (insert o (V a_1 ∪ V a_2))) a_2;
  simp_all;


theorem αEq_disjoint (M : LTerm) : ∃M', αEq M M' ∧ Disjoint (FV M') (Binders M') := by
  have h1 := αEq_disjoint_l1 M (fresh (V M));
  apply h1.elim; intros;
  expose_names;
  exists a;
  simp_all;

  by_contra;
  simp_all [Disjoint];
  apply this.elim; intros;
  expose_names;
  have h5 := Finset.nonempty_of_ne_empty h_1.right.right;
  apply h5.elim; intros;
  expose_names;
  have h2 := FV_αEq h.left;
  have h3 := FV_sub_V M;
  have h4 : a_2 < fresh (V M) := lt_fresh (V M) (by grind);
  have h5 := h.right a_2 (by grind);
  omega;


theorem αEq_alpha (M : LTerm) (x y : Nat) (p1 : y ∉ FV M) : ∃M', αEq M M' ∧ αEq (.Lam x M') (.Lam y (subst x M' (.Ref y))) := by
  have h1 := αEq_disjoint_l1 M (fresh (insert y (V M)));
  apply h1.elim; intros;

  expose_names;
  have h2 := FV_αEq h.left;
  have h3 := FV_sub_V M;
  by_cases y ∈ Binders a;
  have h4 := h.right y (by assumption);
  have h5 : y < fresh (insert y (V M)) := lt_fresh (insert y (V M)) (by grind);
  omega;

  have h4 := Binders_union_FV a;
  have h5 : y ∉ V a := by grind;

  exists a;
  and_intros; simp_all;
  apply αEq.alpha; assumption;


lemma subst_subst_ref (x y z : Nat) (M : LTerm) (p1 : y ∉ V M): subst y (subst x M (.Ref y)) (.Ref z) = subst x M (.Ref z) := by
  induction M <;> simp_all [subst, V];

  split_ifs;
  simp_all [subst];
  simp_all [subst];

  split_ifs;
  simp_all [subst];
  apply subst_not_FV; grind [FV_sub_V];

  simp_all [subst];


lemma exists_V (M : LTerm) : ∃x, x ∈ V M := by
  induction M <;> simp_all [V];
  expose_names;
  apply a_ih.elim; intros;
  expose_names;
  exists a_2;
  simp_all;


theorem subst_self (x : Nat) (M : LTerm) (p1 : x ∉ Binders M) : M = (subst x M (.Ref x)) := by
  induction M;
  rw [subst]; split_ifs;
  simp_all;
  rfl;

  expose_names;
  rw [subst];
  rw [Binders] at p1;
  have := a_ih (by grind;)
  have := a_ih_1 (by grind;)
  grind;

  rw [subst]; split_ifs;
  rfl;
  grind [Binders];


theorem fresh_V_gt_zero (M : LTerm) : 0 < fresh (V M) := by
  have a1 := exists_V M;
  apply a1.elim; intro a _;
  have : a < fresh (V M) :=
    (by apply lt_fresh; grind;)
  omega;




def is_αEq'_lu (a a' : Nat) (B : List (Nat × Nat)) :=
  match B with
  | [] => a == a'
  | (x, y) :: rst =>
    if a == x || a' == y
      then a == x ∧ a' == y
      else is_αEq'_lu a a' rst

def is_αEq' (M M' : LTerm) (B : List (Nat × Nat)) :=
  match M, M' with
  | .Ref a, .Ref a' => is_αEq'_lu a a' B
  | .App a b, .App a' b' => is_αEq' a a' B ∧ is_αEq' b b' B
  | .Lam x p, .Lam x' p' => is_αEq' p p' ((x, x') :: B)
  | _, _ => false

def ctx_flip (B : List (Nat × Nat)) :=
  match B with
  | [] => []
  | (a, b) :: rst => (b, a) :: (ctx_flip rst)

theorem ctx_flip_is_αEq'_lu {ctx : List (Nat × Nat)} {x x' : Nat} (p1 : is_αEq'_lu x x' ctx = true) : is_αEq'_lu x' x (ctx_flip ctx) = true := by
  induction ctx <;> simp_all [is_αEq'_lu, ctx_flip]; grind;

def ValidCtx (M M' : LTerm) (ctx : List (Nat × Nat)) : Prop :=
  (∀x, x ∈ FV M ∧ x ∈ FV M' → is_αEq'_lu x x ctx)

lemma is_αEq'_refl_l1 (n : Nat) : ∀M ctx, lsize M ≤ n → ValidCtx M M ctx → is_αEq' M M ctx = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> simp_all [lsize, is_αEq', ValidCtx, is_αEq'_lu, FV];

  expose_names;
  and_intros;
  apply h; grind; grind;
  apply h; grind; grind;

lemma is_αEq'_refl {M : LTerm} {ctx : List (Nat × Nat)} (p1 : ValidCtx M M ctx) : is_αEq' M M ctx = true :=
  is_αEq'_refl_l1 (lsize M) M ctx (by grind;) p1

lemma is_αEq'_symm (n : Nat) : ∀M M' ctx, lsize M + lsize M' ≤ n → is_αEq' M M' ctx = true → is_αEq' M' M (ctx_flip ctx) = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [is_αEq', lsize];

  apply ctx_flip_is_αEq'_lu; assumption;

  and_intros;
  apply h; omega; grind;
  apply h; omega; grind;

  expose_names;
  exact h a_1 a_3 ((a, a_2) :: ctx) (by omega) h_2;

lemma is_αEq'_appL (n : Nat) : ∀M M' N ctx, lsize M + lsize M' + lsize N ≤ n → ValidCtx (.App M N) (.App M' N) ctx → is_αEq' M M' ctx = true → is_αEq' (.App M N) (.App M' N) ctx = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;

  have h1 : ValidCtx N N ctx :=
    (by simp_all [ValidCtx, FV];)

  cases M <;> cases M' <;> simp_all [is_αEq', ValidCtx, FV];
  apply is_αEq'_refl; simp_all [ValidCtx];
  apply is_αEq'_refl; simp_all [ValidCtx];
  apply is_αEq'_refl; simp_all [ValidCtx];

lemma is_αEq'_appR (n : Nat) : ∀M M' N ctx, lsize M + lsize M' + lsize N ≤ n → ValidCtx (.App N M) (.App N M') ctx → is_αEq' M M' ctx = true → is_αEq' (.App N M) (.App N M') ctx = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;

  have h1 : ValidCtx N N ctx :=
    (by simp_all [ValidCtx, FV];)

  cases M <;> cases M' <;> simp_all [is_αEq', ValidCtx, FV];
  apply is_αEq'_refl; simp_all [ValidCtx];
  apply is_αEq'_refl; simp_all [ValidCtx];
  apply is_αEq'_refl; simp_all [ValidCtx];

lemma is_αEq'_lu_swap (n : Nat) : ∀a b i x y x' y' ctx, ctx.length ≤ n → ctx[i]? = some (x, y) ∧ ctx[i + 1]? = some (x', y') ∧ x ≠ x' ∧ y ≠ y' → is_αEq'_lu a b ctx = true → is_αEq'_lu a b (ctx.swap i (i+1)) = true := by
  induction n;
  simp_all;

  intros;
  expose_names;
  cases ctx <;> cases i <;> simp_all;

  expose_names;
  cases tail <;> simp_all;

  simp_all [is_αEq'_lu];
  split; grind;
  split; grind; grind;

  simp_all [is_αEq'_lu];
  split;
  grind;
  expose_names;
  apply h a b n_1 x y x' y' <;> grind;

lemma is_αEq'_swap (n : Nat): ∀M M' i x y x' y' ctx, lsize M + lsize M' ≤ n → ctx[i]? = some (x, y) ∧ ctx[i + 1]? = some (x', y') ∧ x ≠ x' ∧ y ≠ y' → is_αEq' M M' ctx = true → is_αEq' M M' (ctx.swap i (i+1)) = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [lsize, is_αEq'];
  expose_names;
  apply is_αEq'_lu_swap (ctx.length) a a_1 i x y x' y';
  omega; grind; grind;

  expose_names;
  and_intros;
  apply h a a_2 i x y x' y' <;> grind;
  apply h a_1 a_3 i x y x' y' <;> grind;

  expose_names;
  have := h a_1 a_3 (i + 1) x y x' y' ((a, a_2) :: ctx)
    (by omega;) (by grind;) (by grind;) (by grind;) (by grind;)
    (by grind;)
  simp_all;

lemma is_αEq'_alpha (n : Nat) : ∀x P y ctx, lsize P ≤ n → ValidCtx (.Lam x P) (.Lam x P) ctx → y ∉ V P → is_αEq' (.Lam x P) (.Lam y (subst x P (.Ref y))) ctx = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases P <;> simp_all [is_αEq', V, ValidCtx, lsize, subst, FV];

  expose_names;
  split_ifs;
  simp_all [is_αEq', is_αEq'_lu];

  simp_all [is_αEq', is_αEq'_lu];
  split_ifs; grind; grind;

  and_intros;
  apply h; omega; grind; grind;
  apply h; omega; grind; grind;

  expose_names;
  split_ifs;
  apply is_αEq'_refl;
  rw [ValidCtx];
  intros;
  rw [is_αEq'_lu];
  split_ifs;
  simp_all [FV];
  grind [FV_sub_V];
  simp_all [FV];

  simp_all [is_αEq'];

  have := h x a_1 y ((a, a) :: ctx)
    (by omega;)
    (by
      intros;
      simp_all [is_αEq'_lu];)
    (by grind;)

  have := is_αEq'_swap (lsize a_1 + lsize (subst x a_1 (LTerm.Ref y))) a_1 (subst x a_1 (LTerm.Ref y)) 0 x y a a ((x, y) :: (a, a) :: ctx)
    (by omega) (by grind;) (by grind;)
  simp_all;

lemma is_αEq'_lu_zip (n : Nat) : ∀a b c (ac bc cc : List Nat), ac.length ≤ n ∧ ac.length = bc.length ∧ ac.length = cc.length
  → is_αEq'_lu a b (ac.zipWith (·, ·) bc) = true
  → is_αEq'_lu b c (bc.zipWith (·, ·) cc) = true
  → is_αEq'_lu a c (ac.zipWith (·, ·) cc) := by
  induction n;
  intros;
  expose_names;
  have : bc = [] :=
    (by grind;)
  have : cc = [] :=
    (by grind;)
  simp_all [is_αEq'_lu];

  intros;
  expose_names;
  cases ac <;> cases bc <;> cases cc <;> simp_all [is_αEq'_lu];

  expose_names;
  split at h_2 <;> split at h_3 <;> simp_all;

  apply h a b c tail tail_1 tail_2; omega; omega; omega; grind; grind;

lemma is_αEq'_trans (n : Nat) : ∀a b c (ac bc cc : List Nat), lsize a + lsize b + lsize c ≤ n → ac.length = bc.length ∧ ac.length = cc.length
  → is_αEq' a b (ac.zipWith (·, ·) bc) = true
  → is_αEq' b c (bc.zipWith (·, ·) cc) = true
  → is_αEq' a c (ac.zipWith (·, ·) cc)
:= by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases a <;> cases b <;> simp_all [is_αEq'];

  all_goals cases c <;> simp_all [lsize, is_αEq'];

  expose_names;
  apply is_αEq'_lu_zip (ac.length) a a_1 a_2 ac bc cc;
  omega; grind; grind;

  expose_names;
  and_intros;
  apply h a a_2 a_4 ac bc cc <;> grind;
  apply h a_1 a_3 a_5 ac bc cc <;> grind;


  expose_names;

  have h1 := h a_1 a_3 a_5 (a :: ac) (a_2 :: bc) (a_4 :: cc)
    (by omega;) (by grind;) (by grind;)
    (by
      rw [List.zipWith_cons_cons];
      grind;)
   (by
      rw [List.zipWith_cons_cons];
      grind;)

  rw [List.zipWith_cons_cons] at h1;
  exact h1;

lemma is_αEq'_lu_cat (n : Nat) : ∀x a b ctx, ctx.length ≤ n → is_αEq'_lu a b ctx = true → is_αEq'_lu a b (ctx ++ [(x, x)]) = true := by
  induction n;
  simp_all [is_αEq'_lu];

  intros;
  expose_names;
  cases ctx <;> simp_all [is_αEq'_lu];
  split <;> grind;

lemma is_αEq'_cat (n : Nat) : ∀x M M' ctx, lsize M + lsize M' ≤ n → is_αEq' M M' ctx = true → is_αEq' M M' (ctx ++ [(x, x)]) = true := by
  induction n;
  grind [lsize_gt_zero];
  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [is_αEq', lsize];
  apply is_αEq'_lu_cat ctx.length;
  omega; grind;
  expose_names;
  and_intros;
  apply h; omega; grind; grind; grind;

lemma is_αEq'_lu_pop (n : Nat) : ∀x a b ctx, ctx.length ≤ n → is_αEq'_lu a b (ctx ++ [(x, x)]) = true → is_αEq'_lu a b ctx = true := by
  induction n;
  intros;
  expose_names;
  simp_all [is_αEq'_lu];
  split at h_1 <;> simp_all;

  intros;
  expose_names;
  cases ctx <;> simp_all [is_αEq'_lu];

  split at h_2 <;> simp_all;

  split;
  simp_all;
  split at h_2 <;> simp_all;

  expose_names;
  apply h x a b tail; omega; grind;

lemma is_αEq'_pop (n : Nat) : ∀x M M' ctx, lsize M + lsize M' ≤ n → is_αEq' M M' (ctx ++ [(x, x)]) = true → is_αEq' M M' ctx = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [is_αEq', lsize];

  expose_names;
  apply is_αEq'_lu_pop (ctx.length) x a a_1; omega; grind;

  expose_names;
  and_intros;
  apply h x a a_2 ctx; omega; grind; grind;

  expose_names;
  apply h x a_1 a_3; omega; grind;

lemma is_αEq'_lam (n : Nat) : ∀x M M', lsize M + lsize M' ≤ n → is_αEq' M M' [] = true → is_αEq' (.Lam x M) (.Lam x M') [] = true := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [is_αEq', lsize];

  expose_names;
  have := is_αEq'_lu_cat 0 x a a_1 []
    (by grind;) (by grind;);
  simp_all;

  and_intros;
  grind; grind;

  expose_names;
  have := is_αEq'_cat (lsize a_1 + lsize a_3) x a_1 a_3 [(a , a_2)]
    (by grind;) (by grind;)
  simp_all;

lemma αEq_iff_is_αEq'_l1 (M M' : LTerm) : αEq M M' → is_αEq' M M' [] = true := by
  intro h;
  induction h;
  apply is_αEq'_refl;
  rw [ValidCtx];
  intros;
  simp_all [is_αEq'_lu];

  expose_names;
  have := is_αEq'_symm (lsize a + lsize b) a b [] (by grind;)
  grind [ctx_flip];

  expose_names;
  have := is_αEq'_trans (lsize a + lsize b + lsize c) a b c [] [] []
    (by grind;) (by grind;)
    (by simp_all;) (by simp_all;);
  simp_all;

  expose_names;
  have := is_αEq'_appL (lsize P + lsize P' + lsize Q) P P' Q []
    (by grind;)
    (by  rw [ValidCtx]; intros; simp_all [is_αEq'_lu];)
  simp_all;

  expose_names;
  have := is_αEq'_appR (lsize P + lsize P' + lsize Q) P P' Q []
    (by grind;)
    (by  rw [ValidCtx]; intros; simp_all [is_αEq'_lu];)
  simp_all;

  expose_names;
  apply is_αEq'_lam (lsize P + lsize P'); omega; grind;

  expose_names;
  apply is_αEq'_alpha (lsize P); omega; rw [ValidCtx]; intros;
  simp_all [FV, is_αEq'_lu]; grind;

lemma αEq_iff_is_αEq'_l2 (n : Nat) : ∀M M', lsize M + lsize M' ≤ n → is_αEq' M M' [] = true → αEq M M' := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases M' <;> simp_all [lsize, is_αEq', is_αEq'_lu];

  apply αEq.refl;

  expose_names;
  apply αEq.trans;
  apply αEq.appL (P' := a_2);
  apply h; omega; grind;
  apply αEq.appR (P' := a_3);
  apply h; omega; grind;


  expose_names;
  set X := (fresh (V a_1 ∪ V a_3))

  have h1 := is_αEq'_alpha (lsize a_3) a_2 a_3 X
    [] (by omega;)
    (by
      rw [ValidCtx];
      simp_all [is_αEq'_lu])
    (by
      apply fresh_notmem_subset;
      grind;)

  have h2 := is_αEq'_alpha (lsize a_1) a a_1 X
    [] (by omega;)
    (by
      rw [ValidCtx];
      simp_all [is_αEq'_lu])
    (by
      apply fresh_notmem_subset;
      grind;)

  have h3 := is_αEq'_symm (lsize (LTerm.Lam a a_1) + lsize (LTerm.Lam X (subst a a_1 (LTerm.Ref X))))
        (LTerm.Lam a a_1) (LTerm.Lam X (subst a a_1 (LTerm.Ref X)))
    [] (by omega;) (by grind;)

  simp_all [is_αEq', ctx_flip];
  have h4 := is_αEq'_trans (lsize (subst a a_1 (LTerm.Ref X)) + lsize a_1 + lsize a_3)
    (subst a a_1 (LTerm.Ref X)) a_1 a_3
    [X] [a] [a_2] (by omega;) (by simp_all;)
    (by simp_all;)
    (by simp_all;)

  have h5 := is_αEq'_trans (lsize (subst a a_1 (LTerm.Ref X)) + lsize a_3 +
      lsize (subst a_2 a_3 (LTerm.Ref X)))
    (subst a a_1 (LTerm.Ref X)) a_3 (subst a_2 a_3 (LTerm.Ref X))
    [X] [a_2] [X]
    (by omega;)
    (by simp_all;)
    (by simp_all;)
    (by simp_all;)

  simp_all;

  have h6 := is_αEq'_pop (lsize (subst a a_1 (LTerm.Ref X)) + lsize (subst a_2 a_3 (LTerm.Ref X)))
    X (subst a a_1 (LTerm.Ref X)) (subst a_2 a_3 (LTerm.Ref X))
    [] (by omega;) (by grind;)

  have h7 := h (subst a a_1 (LTerm.Ref X)) (subst a_2 a_3 (LTerm.Ref X))
    (by grind [lsize_subst_ref];)
    (by grind;)

  have h8 := αEq.lam X h7;

  have e1 := αEq.alpha a_1 a X (by apply fresh_notmem_subset; grind;)
  have e2 := αEq.alpha a_3 a_2 X (by apply fresh_notmem_subset; grind;)

  apply αEq.trans;
  exact e1;
  apply αEq.symm;
  apply αEq.trans;
  exact e2;
  apply αEq.symm;
  grind;

theorem αEq_iff_is_αEq' (M M' : LTerm) : αEq M M' ↔ is_αEq' M M' [] := by
  apply Iff.intro <;> intros;

  apply αEq_iff_is_αEq'_l1;
  grind;

  expose_names;
  apply αEq_iff_is_αEq'_l2 (lsize M + lsize M');
  omega; grind;

instance : DecidableRel αEq := fun M M' =>
  decidable_of_bool (is_αEq' M M' []) (by apply Iff.symm; exact αEq_iff_is_αEq' M M')

theorem αEq_strip_binder {M M' : LTerm} {x : Nat} (p1 : αEq (.Lam x M) (.Lam x M')) : αEq M M' := by
  have h1 := (αEq_iff_is_αEq' (.Lam x M) (.Lam x M')).mp p1
  simp_all [is_αEq'];
  have h2 := is_αEq'_pop (lsize M + lsize M') x M M' [] (by omega;) (by grind;)
  apply (αEq_iff_is_αEq' M M').mpr h2;

theorem αEq_split_app {M M' N N' : LTerm} (p1 : αEq (.App M N) (.App M' N')) : (αEq M M') ∧ (αEq N N') := by
  rw [αEq_iff_is_αEq'];
  rw [αEq_iff_is_αEq'];
  rw [αEq_iff_is_αEq'] at p1;
  simp_all [is_αEq'];






























def shift_binders (o : Nat) (M : LTerm) : LTerm :=
  match M with
  | .Ref a => .Ref a
  | .App A B => .App (shift_binders o A) (shift_binders o B)
  | .Lam x P =>
    let P' := shift_binders o P;
    let o' := fresh (V P') + o;
    .Lam (x + o') (subst x P' (.Ref (x + o')))

lemma shift_binders_disjoint_l1 (o : Nat) (n : Nat) : ∀M, lsize M ≤ n → ∀x, x ∈ Binders (shift_binders o M) → o ≤ x := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> simp_all [lsize, shift_binders, Binders];

  expose_names;
  have : fresh (V a) ≤ fresh (V a ∪ V a_1) :=
    (by apply fresh_subset; grind;);
  have : fresh (V a_1) ≤ fresh (V a ∪ V a_1) :=
    (by apply fresh_subset; grind;);
  apply h_2.elim <;> intros;
  apply h a; omega; assumption;
  apply h a_1; omega; assumption;

  apply h_2.elim <;> intros;

  omega;

  simp_all;
  expose_names;

  have : fresh (V a_1) ≤ fresh (insert a (V a_1)) :=
    (by apply fresh_subset; grind;);

  have := h a_1 (by omega) x;
  have := (Binders_subst a (shift_binders o a_1) (.Ref (a + (fresh (V (shift_binders o a_1)) + o))) x).mp;
  simp_all [Binders];

lemma αEq_shift_binders_l1 (o : Nat) (n : Nat) : ∀M, lsize M ≤ n → fresh (V M) ≤ o → αEq M (shift_binders o M) := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> simp_all [shift_binders, V, lsize];

  apply αEq.refl;

  expose_names;
  have : fresh (V a) ≤ fresh (V a ∪ V a_1) :=
    (by apply fresh_subset; grind;);
  have : fresh (V a_1) ≤ fresh (V a ∪ V a_1) :=
    (by apply fresh_subset; grind;);
  have h1 := h a (by omega) (by omega);
  have h2 := h a_1 (by omega) (by omega);

  apply αEq.trans;
  apply αEq.appL a_1 h1;
  apply αEq.appR; exact h2;

  expose_names;
  have : fresh (V a_1) ≤ fresh (insert a (V a_1)) :=
    (by apply fresh_subset; grind;);

  have := h a_1 (by omega) (by omega);

  apply αEq.trans;
  apply αEq.lam;
  exact this;
  apply αEq.alpha;

  intro a1;
  have := lt_fresh (V (shift_binders o a_1)) a1;
  omega;

theorem αEq_shift_binders (M : LTerm) (o : Nat) (p1 : fresh (V M) ≤ o) : αEq M (shift_binders o M) := by
  apply αEq_shift_binders_l1 o (lsize M) M (by omega) p1;

theorem shift_binders_disjoint (M : LTerm) (o : Nat) (p1 : fresh (V M) ≤ o) : Disjoint (FV (shift_binders o M)) (Binders (shift_binders o M)) := by
  rw [Disjoint]; intros;
  rw [Finset.subset_iff]; intros;
  expose_names;
  rw [Finset.subset_iff] at h;
  rw [Finset.subset_iff] at h_1;

  apply False.elim;

  have := h h_2;
  have := h_1 h_2;
  have := shift_binders_disjoint_l1 o (lsize M) (by omega) (by omega) x_1 this;
  have := fresh_subset (FV M) (V M) (by grind [FV_sub_V]);
  have := Eq.symm (FV_αEq (αEq_shift_binders M o p1));
  have := lt_fresh (FV M) (x := x_1) (by simp_all);

  omega;

def subst' (x : Nat) (M N : LTerm) :=
  let o := fresh (V M ∪ V N ∪ {x});

  -- Disjoint (Binders M') (FV N')
  let M' := shift_binders o M;
  let N' := shift_binders o N;

  subst x M' N'

lemma αEq_subst_l1 (x : Nat) (M N N' : LTerm) (p1 : αEq N N') : αEq (subst x M N) (subst x M N') := by
  induction M <;> simp_all [subst] <;> (try split_ifs) <;> (try simp_all [αEq.refl]);
  apply αEq.trans;
  apply αEq.appL; assumption;
  apply αEq.appR; assumption;

  apply αEq.lam;
  assumption;

lemma αEq_subst_l2 (n : Nat) : ∀M M' x N, lsize M + lsize M' ≤ n → x ∉ Binders N → is_αEq' M M' [] → Disjoint (Binders M) (FV N) → Disjoint (Binders M') (FV N) → αEq (subst x M N) (subst x M' N) := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;

  have h1 := (αEq_iff_is_αEq' M M').mpr h_3;
  have h2 := FV_αEq h1;
  by_cases x ∉ FV M
  have : x ∉ FV M' := by grind;
  simp_all [subst_not_FV];



  cases M <;> cases M' <;> simp_all [is_αEq', is_αEq'_lu, lsize, Binders, FV];

  apply αEq.refl;

  expose_names;
  apply αEq.trans;
  apply αEq.appL;
  apply h a a_2 <;> grind;
  apply αEq.appR;
  apply h <;> grind;

  expose_names;

  set X := fresh (V a_1 ∪ V a_3 ∪ {x} ∪ {a} ∪ {a_2} ∪ (V (subst x a_1 N)) ∪ (V (subst x a_3 N)));
  have xh1 : X ∉ V a_1 := (by apply fresh_notmem_subset; grind;)
  have xh2 : X ∉ V a_3 := (by apply fresh_notmem_subset; grind;)
  have xh2 : X ∉ V (subst x a_1 N) := (by apply fresh_notmem_subset; grind;)
  have xh2 : X ∉ V (subst x a_3 N) := (by apply fresh_notmem_subset; grind;)
  have xh2 : x < X := (by apply lt_fresh; grind;)
  have xh2 : a < X := (by apply lt_fresh; grind;)
  have xh2 : a_2 < X := (by apply lt_fresh; grind;)

  have h3 := αEq.symm (αEq.alpha a_1 a X (by grind;));
  have h4 := αEq.alpha a_3 a_2 X (by grind;);

  have h5 := αEq_strip_binder (αEq.trans (αEq.trans h3 h1) h4);

  have h6 := h (subst a a_1 (LTerm.Ref X)) (subst a_2 a_3 (LTerm.Ref X))
    x N (by grind [lsize_subst_ref];) (by grind) (by grind [αEq_iff_is_αEq'];)
    (by simp_all [Binders_subst_ref];)
    (by simp_all [Binders_subst_ref];)

  have : x ≠ a_2 :=
    (by
      intro;
      have : x ∈ FV a_1 \ {a} := by grind;
      have : x ∉ FV a_3 \ {a_2} := by grind;
      grind;)

  have f1 := FV_subst x a_1 N
    (by simp_all [];);
  have f2 := FV_subst x a_3 N
    (by simp_all [];);
  have f3 := FV_subst a_2 a_3 (.Ref X)
    (by
      simp_all [FV];
      grind [Binders_union_FV];);

  have := FV_αEq h5;

  by_cases a ∉ FV a_1;

  have : a_2 ∉ FV a_3 :=
    (by
      intro;
      simp_all [FV];
      grind [subst_not_FV, FV_sub_V];);

  have : a ∉ FV (subst x a_1 N) :=
    (by
      intro;
      have := (f1 a).mp
        (by
          grind;
        );
      simp_all;)

  have h9 := αEq.alpha (subst x a_1 N) a X
    (by grind;)
  have h10 := αEq.alpha (subst x a_3 N) a_2 X
    (by grind;)

  simp_all [subst_not_FV, subst];
  have hn := αEq.trans h9 (αEq.trans (αEq.lam X h6) (αEq.symm h10));
  exact hn;

  simp_all [subst];

  have e1 := αEq.alpha (subst x a_1 N) a X
    (by grind);
  have e2 := αEq.alpha (subst x a_3 N) a_2 X
    (by grind;);

  apply αEq.trans e1;
  apply αEq.symm;
  apply αEq.trans e2;
  apply αEq.symm;
  apply αEq.lam;

  have e3 := subst_comm a x a_1 (.Ref X) N
    (by grind;)
    (by grind;)
    (by simp_all [FV]; grind;)
  have e4 := subst_comm a_2 x a_3 (.Ref X) N
    (by grind;)
    (by grind;)
    (by simp_all [FV]; grind;)

  rw [e3, e4]
  exact h6;

theorem subst'_respects_αEq (x : Nat) (M M' N N' : LTerm) : αEq M M' → αEq N N' → αEq (subst' x M N) (subst' x M' N') := by
  intros;

  expose_names;
  set lo := fresh (V M ∪ V N ∪ {x}) with hlo;
  set lM' := shift_binders lo M with hM';
  set lN' := shift_binders lo N with hN';

  set ro := fresh (V M' ∪ V N' ∪ {x}) with hro;
  set rM' := shift_binders ro M' with hM';
  set rN' := shift_binders ro N' with hN';

  have e1 := αEq_shift_binders M lo
    (by apply fresh_subset; grind;)
  have e2 := αEq_shift_binders M' ro
    (by apply fresh_subset; grind;)

  have h1 : αEq lM' rM' := αEq.trans (αEq.symm e1) (αEq.trans h e2);

  have e3 := αEq_shift_binders N lo
    (by apply fresh_subset; grind;)
  have e4 := αEq_shift_binders N' ro
    (by apply fresh_subset; grind;)

  have h2 : αEq lN' rN' := αEq.trans (αEq.symm e3) (αEq.trans h_1 e4);

  have l1 := shift_binders_disjoint_l1 lo (lsize M) M (by omega;);
  have l2 := shift_binders_disjoint_l1 lo (lsize N) N (by omega;);
  have l3 := shift_binders_disjoint_l1 ro (lsize M') M' (by omega;);
  have l4 := shift_binders_disjoint_l1 ro (lsize N') N' (by omega;);

  have : x < lo := by apply lt_fresh; grind;
  have : x < ro := by apply lt_fresh; grind;

  have : x ∉ Binders lN' :=
    (by
      intro a1;
      have := l2 x a1;
      omega;)

  have : x ∉ Binders rN' :=
    (by
      intro a1;
      have := l4 x a1;
      omega;)

  have : Disjoint (Binders lM') (FV lN') :=
    (by
      rw [Disjoint];
      intro p q r s;
      rw [Finset.subset_iff] at q;
      rw [Finset.subset_iff] at r;
      simp;
      intro a1;
      expose_names;
      have := r a1;
      have := l1 s (q a1);
      have : s < lo := (by
        rw [hlo];
        apply lt_fresh;
        have := FV_αEq e3;
        grind [FV_sub_V];
      )
      omega;)

  have : Disjoint (Binders rM') (FV lN') :=
    (by
      rw [Disjoint];
      intro p q r s;
      rw [Finset.subset_iff] at q;
      rw [Finset.subset_iff] at r;
      simp;
      intro a1;
      expose_names;
      have := r a1;
      have := l3 s (q a1);
      have : s < ro := (by
        rw [hro];
        apply lt_fresh;
        have := FV_αEq e3;
        have := FV_αEq h_1;
        grind [FV_sub_V];
      )
      omega;)

  have f1  := αEq_subst_l2 (lsize lM' + lsize rM') lM' rM' x lN'
    (by grind;) (by grind;) ((αEq_iff_is_αEq' lM' rM').mp (by grind))
    (by grind;) (by grind;)

  have f2 := αEq_subst_l1 x rM' lN' rN' h2;

  exact αEq.trans f1 f2;



theorem subst'_ref (x y : Nat) (N : LTerm) : αEq (subst' x (.Ref y) N) (if x = y then N else (.Ref y)) := by
  by_cases x = y;
  simp_all [subst', shift_binders, subst, V];
  apply αEq.symm;
  apply αEq_shift_binders;
  apply fresh_subset;
  grind;

  simp_all [subst', shift_binders, subst, V];
  apply αEq.refl;

theorem subst'_app (x : Nat) (A B N : LTerm) : αEq (subst' x (.App A B) N) (.App (subst' x A N) (subst' x B N)) := by
  simp_all [subst', shift_binders, subst, V];

  set lo := (fresh (insert x (V A ∪ (V B ∪ V N))));
  set rao := (fresh (insert x (V A ∪ V N)));
  set rbo := (fresh (insert x (V B ∪ V N)));

  set lA' := (shift_binders lo A);
  set lB' := (shift_binders lo B);
  set lN' := (shift_binders lo N);

  set rA' := (shift_binders rao A);
  set raN' := (shift_binders rao N);
  set rB' := (shift_binders rbo B);
  set rbN' := (shift_binders rbo N);

  have : αEq A lA' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : αEq B lB' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : αEq N lN' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)

  have : αEq A rA' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : αEq B rB' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : αEq N raN' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : αEq N rbN' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)

  have : FV N = FV lN' :=
    (by
      apply FV_αEq;
      apply αEq_shift_binders;
      apply fresh_subset;
      grind;)

  apply αEq.trans (b := ((subst x rA' raN').App (subst x lB' lN')));
  apply αEq.appL;

  by_cases x ∉ FV A;
  have : x ∉ FV lA' :=
    (by grind [FV_αEq];)
  have : x ∉ FV rA' :=
    (by grind [FV_αEq];)
  simp_all [subst_not_FV];
  apply αEq.trans;
  apply αEq.symm;
  assumption;
  assumption;


  have := αEq_subst_l2 (lsize lA' + lsize rA') lA' rA' x lN'
    (by omega;)
    (by
      intro;
      have : lo ≤ x :=
        (by
          apply shift_binders_disjoint_l1 lo (lsize N) N (by omega) x;
          grind;)
      have : x < lo :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)
    (by grind [αEq_iff_is_αEq', αEq.trans, αEq.symm];)
    (by
      rw [Disjoint];
      intros;
      simp_all [Finset.subset_iff];
      intros; intro a1;
      expose_names;
      have := h_2 a1;
      have := h_1 a1;
      have : lo ≤ x_2 :=
        (by
          apply shift_binders_disjoint_l1 lo (lsize A) A (by omega) x_2;
          grind;)
      have : x_2 < lo :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)
    (by
      rw [Disjoint];
      intros;
      simp_all [Finset.subset_iff];
      intros; intro a1;
      expose_names;
      have := h_2 a1;
      have := h_1 a1;
      have : rao ≤ x_2 :=
        (by
          apply shift_binders_disjoint_l1 rao (lsize A) A (by omega) x_2;
          grind;)
      have : x_2 < rao :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)

  apply αEq.trans;
  assumption;
  apply αEq_subst_l1;
  grind [αEq.symm, αEq.trans];
  apply αEq.appR;

  have := αEq_subst_l2 (lsize lB' + lsize rB') lB' rB' x lN'
    (by omega;)
    (by
      intro;
      have : lo ≤ x :=
        (by
          apply shift_binders_disjoint_l1 lo (lsize N) N (by omega) x;
          grind;)
      have : x < lo :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)
    (by grind [αEq_iff_is_αEq', αEq.trans, αEq.symm];)
    (by
      rw [Disjoint];
      intros;
      simp_all [Finset.subset_iff];
      intros; intro a1;
      expose_names;
      have := h a1;
      have := h_1 a1;
      have : lo ≤ x_2 :=
        (by
          apply shift_binders_disjoint_l1 lo (lsize B) B (by omega) x_2;
          grind;)
      have : x_2 < lo :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)
    (by
      rw [Disjoint];
      intros;
      simp_all [Finset.subset_iff];
      intros; intro a1;
      expose_names;
      have := h a1;
      have := h_1 a1;
      have : rbo ≤ x_2 :=
        (by
          apply shift_binders_disjoint_l1 rbo (lsize B) B (by omega) x_2;
          grind;)
      have : x_2 < rbo :=
        (by
          apply lt_fresh;
          grind [FV_sub_V];)
      omega;)

  apply αEq.trans;
  assumption;
  apply αEq_subst_l1;
  grind [αEq.symm, αEq.trans];

theorem subst'_lam_l1 (y : Nat) (P N : LTerm) : αEq (subst' y (.Lam y P) N) (.Lam y P) := by
  set P' := (shift_binders (fresh (insert y (V P ∪ V N))) P) with hP';
  symm at hP';

  have : αEq P P' := (by
      apply αEq_shift_binders;
      apply fresh_subset; grind;)

  simp_all [subst', shift_binders, subst, V];

  set v := fresh (V (shift_binders (fresh (insert y (V P ∪ V N))) P)) with vh;
  have : 0 < v :=
    (by apply fresh_V_gt_zero;);
  have : v ≠ 0 := (by omega);
  simp_all;

  set Y := (y + (v + fresh (insert y (V P ∪ V N))));

  have : FV P = FV P' := by grind [FV_αEq];
  have := FV_subst y P' (.Ref Y)
    (by
      simp_all [FV];
      intro;
      have : Y < fresh (V P') :=
        (by apply lt_fresh; grind [Binders_union_FV];)

      rw [←hP'] at this;
      omega;) y;
  simp_all;

  have : y ∉ FV (subst y P' (LTerm.Ref Y)) :=
    (by
      intro;
      simp_all [FV];
      have : Y < fresh (V P') :=
        (by apply lt_fresh; grind [Binders_union_FV];)
      grind;)

  simp_all [subst_not_FV];
  apply αEq.symm;

  apply αEq.trans (b := (LTerm.Lam y P'));
  apply αEq.lam; assumption;
  apply αEq.alpha;
  intro;
  have : Y < fresh (V P') :=
    (by
      rw [←hP']
      apply lt_fresh;
      grind;)
  omega;

theorem subst'_lam_l2 (x y : Nat) (P N : LTerm) (p1 : x ≠ y) (p2 : y ∉ FV N) : αEq (subst' x (.Lam y P) N) (.Lam y (subst' x P N)) := by
  simp_all [subst', shift_binders, V];
  rw [subst];

  set v' := (y +
        (fresh (V (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) P)) +
          fresh (insert y (insert x (V P ∪ V N)))));

  set P' := (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) P);

  set N' := (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) N)

  set P'' := (shift_binders (fresh (insert x (V P ∪ V N))) P)

  set N'' := (shift_binders (fresh (insert x (V P ∪ V N))) N)

  have : αEq P P' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : FV P = FV P' := by grind [FV_αEq];

  have : αEq P P'' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : FV P = FV P'' := by grind [FV_αEq];

  have : αEq N N' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : FV N = FV N' := by grind [FV_αEq];

  have : αEq N N'' := (by
    apply αEq_shift_binders;
    apply fresh_subset; grind;)
  have : FV N = FV N'' := by grind [FV_αEq];

  split;
  have : x < fresh (insert y (insert x (V P ∪ V N))) :=
    (by apply lt_fresh; grind;)
  omega;

  have := subst_comm x y P' N' (.Ref v')
    (by grind;)
    (by simp_all [FV];)
    (by grind;)

  by_cases x ∉ FV P;
  rw [this];
  simp_all [subst_not_FV];
  apply αEq.symm;
  apply αEq.trans;
  apply αEq.lam;
  have h1 : αEq P'' P' := (by grind [αEq.symm, αEq.trans]);
  exact h1;
  apply αEq.alpha;
  intro a1;
  have : v' < fresh (V (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) P)) :=
    (by apply lt_fresh; grind;)
  omega;


  have : Disjoint (Binders P'') (FV N'') :=
    (by
      rw [Disjoint];
      intro h1 h2 h3;
      simp_all [Finset.subset_iff];
      intro x' a1;
      have := h2 a1;
      have := h3 a1;
      have := shift_binders_disjoint_l1 (fresh (insert x (V P ∪ V N)))
        (lsize P) P (by omega;) x' (by grind;)
      have : x' < fresh (insert x (V P ∪ V N)) :=
        (by apply lt_fresh; grind [FV_sub_V];);
      omega;)

  have f1 := FV_subst x P'' N''
    (by grind;)

  have : Disjoint (Binders P') (FV N') :=
    (by
      rw [Disjoint];
      intro h1 h2 h3;
      simp_all [Finset.subset_iff];
      intro x' a1;
      have := h2 a1;
      have := h3 a1;
      have := shift_binders_disjoint_l1 (fresh (insert y (insert x (V P ∪ V N))))
        (lsize P) P (by omega;) x' (by grind;)
      have : x' < (fresh (insert y (insert x (V P ∪ V N)))) :=
        (by apply lt_fresh; grind [FV_sub_V];);
      omega;)

  have f2 := FV_subst x P' N' (by grind;)




  by_cases y ∉ FV P;

  rw [subst_not_FV y]
  set Q := fresh (V (subst x P' N') ∪ V (subst x P'' N'') ∪ {v'} ∪ {y})
  apply αEq.trans;
  apply αEq.alpha (subst x P' N') v' Q;
  intro a1;
  have : Q < fresh (V (subst x P' N') ∪ V (subst x P'' N'') ∪ {v'} ∪ {y}) :=
    (by apply lt_fresh; grind;)
  omega;

  apply αEq.symm;
  apply αEq.trans;
  apply αEq.alpha (subst x P'' N'') y Q;
  intro a1;
  have : Q < fresh (V (subst x P' N') ∪ V (subst x P'' N'') ∪ {v'} ∪ {y}) :=
    (by apply lt_fresh; grind;)
  omega;

  apply αEq.lam;

  have : y ∉ FV (subst x P'' N'') :=
    (by
      intro;
      have := (f1 y).mp
      simp_all;)

  have : v' ∉ FV (subst x P' N') :=
    (by
      intro;
      have := (f2 v').mp;
      simp_all;
      expose_names;
      rcases h_3;
      have : v' < fresh (insert y (insert x (V P ∪ V N))) :=
        (by apply lt_fresh; grind [FV_sub_V];);
      omega;
      have : v' < fresh (insert y (insert x (V P ∪ V N))) :=
        (by apply lt_fresh; grind [FV_sub_V];);
      omega;)

  simp_all [subst_not_FV];
  apply αEq.trans;
  apply αEq_subst_l1 x P'' N'' N'
  grind [αEq.symm, αEq.trans];
  apply αEq_subst_l2 (lsize P'' + lsize P');
  omega;

  intro;
  have := shift_binders_disjoint_l1 (fresh (insert y (insert x (V P ∪ V N))))
    (lsize N) N (by omega;) x (by grind;)
  have : x < (fresh (insert y (insert x (V P ∪ V N)))) :=
    (by apply lt_fresh; grind [FV_sub_V];);
  omega;
  rw [←αEq_iff_is_αEq'];
  grind [αEq.symm, αEq.trans];

  grind;
  grind;
  grind;

  simp_all;








  apply αEq.symm;
  apply αEq.trans;
  apply αEq.lam;
  apply αEq_subst_l2 (lsize P'' + lsize P') P'' P';
  omega;
  intro;
  have := shift_binders_disjoint_l1 (fresh (insert x (V P ∪ V N)))
    (lsize N) N (by omega;) x (by grind;) ;
  have : x < fresh (insert x (V P ∪ V N)) :=
    (by apply lt_fresh; grind;);
  omega;
  rw [←αEq_iff_is_αEq'];
  grind [αEq.symm, αEq.trans];
  grind;
  grind;

  apply αEq.trans;
  apply αEq.lam;
  apply αEq_subst_l1 x P' N'' N;
  grind [αEq.symm, αEq.trans];

  apply αEq.trans;
  apply αEq.alpha (subst x P' N) y v';

  rw [←Binders_union_FV]
  intro a1;
  simp_all;
  rcases a1;
  have := (Binders_subst x P' N v').mp;
  simp_all;
  rcases this;

  have : v' < fresh (insert y (insert x (V P ∪ V N))) :=
    (by apply lt_fresh; grind [Binders_sub_V];)
  omega;

  have : v' < fresh (V (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) P)) :=
    (by apply lt_fresh; grind [Binders_sub_V];)
  omega;


  have := FV_subst x P' N
    (by simp_all;) v' |>.mp (by grind;)
  rcases this;

  have : v' < fresh (V (shift_binders (fresh (insert y (insert x (V P ∪ V N)))) P)) :=
    (by apply lt_fresh; grind [FV_sub_V];)
  omega;

  have : v' < fresh (insert y (insert x (V P ∪ V N))) :=
    (by apply lt_fresh; grind [FV_sub_V];)
  omega;

  apply αEq.lam;

  have := subst_comm x y P' N (.Ref v')
    (by grind;)
    (by simp_all [FV];)
    (by grind;)

  rw [←this]
  apply αEq.trans;
  apply αEq_subst_l1;
  expose_names;
  exact this_5;
  grind [αEq.refl];

theorem subst'_reduce {x : Nat} {M N : LTerm}
  {F : Nat → Nat → LTerm → LTerm → (Nat × LTerm)}
  {p1 : ∀x y P N, x ≠ (F x y P N).1 ∧ (F x y P N).1 ∉ FV N ∧ αEq (.Lam y P) (.Lam (F x y P N).1 (F x y P N).2)} :
  αEq (subst' x M N)
  (match M with
  | .Ref y => if x = y then N else (.Ref y)
  | .App A B => .App (subst' x A N) (subst' x B N)
  | .Lam y P =>
      let (y', P') := F x y P N
      .Lam y' (subst' x P' N)
  ) := by
  split;
  apply subst'_ref;
  apply subst'_app;

  split;
  expose_names;
  have := p1 x x_1 M N
  simp_all;

  apply αEq.trans;
  apply subst'_respects_αEq;
  exact this.right.right;
  apply αEq.refl;

  apply subst'_lam_l2;
  grind;
  grind;


theorem αEq_subst'_subst (x : Nat) (M N : LTerm) (p1 : Disjoint (Binders M) (FV N)) : αEq (subst' x M N) (subst x M N) := by
  induction M <;> simp_all [subst, subst'_ref, Binders];

  apply αEq.trans;
  apply subst'_app;
  apply αEq.trans;
  apply αEq.appL;
  assumption;
  apply αEq.appR;
  assumption;

  split;
  simp_all;
  apply subst'_lam_l1;

  apply αEq.trans;
  apply subst'_lam_l2;
  grind;
  grind;

  apply αEq.lam;
  grind;



lemma lsize_respects_αEq_l1 (n: Nat) : ∀M N, lsize M + lsize N ≤ n → is_αEq' M N [] → lsize M = lsize N := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M <;> cases N <;> simp_all [lsize, is_αEq'];

  grind;

  expose_names;

  set y' := fresh (V a_1 ∪ V a_3)
  have h1 := αEq.alpha a_3 a_2 y'
    (by
      intro;
      have : y' < fresh (V a_1 ∪ V a_3) :=
        (by apply lt_fresh; grind;)
      omega;)

  have h2 := αEq.alpha a_1 a y'
    (by
      intro;
      have : y' < fresh (V a_1 ∪ V a_3) :=
        (by apply lt_fresh; grind;)
      omega;)

  have h3 : αEq (.Lam a a_1) (.Lam a_2 a_3) :=
    (by grind [αEq_iff_is_αEq', is_αEq']);

  have h4 : αEq (.Lam y' (subst a a_1 (.Ref y'))) (.Lam y' (subst a_2 a_3 (.Ref y'))) :=
    (by grind [αEq.trans, αEq.symm])

  have h5 := αEq_strip_binder h4;
  rw [αEq_iff_is_αEq'] at h5;

  have := h (subst a a_1 (LTerm.Ref y')) (subst a_2 a_3 (LTerm.Ref y'))
    (by
      simp_all[lsize_subst_ref];
      omega;)
    (by grind;)

  simp_all [lsize_subst_ref];

theorem lsize_respects_αEq (M N : LTerm) (p1 : αEq M N) : lsize M = lsize N := by
  apply lsize_respects_αEq_l1 (lsize M + lsize N) M N (by omega;) (by grind [αEq_iff_is_αEq']);









def LTerm.show : LTerm → String
  | .Ref n => s!"v{n}"
  | .App M N => s!"({M.show} {N.show})"
  | .Lam x P => s!"(λ x{x}. {P.show})"

end PreTerm

def Λ := Quot PreTerm.αEq

unsafe def Λ.show (M : Λ) : String := M.unquot.show
unsafe instance : ToString Λ := ⟨Λ.show⟩
unsafe instance : Repr Λ := ⟨fun M _ => M.show⟩


def app (M N : Λ) : Λ :=
  Quot.lift₂ (fun M N => Quot.mk _ (.App M N))
    (by
      intros;
      apply Quot.sound;
      apply PreTerm.αEq.appR;
      grind;)
    (by
      intros;
      apply Quot.sound;
      apply PreTerm.αEq.appL;
      grind;)
    M N

def ref (n : Nat) : Λ := Quot.mk _ (.Ref n)

def lam (x : Nat) (M : Λ) : Λ :=
  Quot.lift (fun M => Quot.mk _ (.Lam x M))
    (by
      intros;
      apply Quot.sound;
      apply PreTerm.αEq.lam;
      grind;)
    M

@[elab_as_elim]
theorem Λind {P : Λ → Prop} (p1 : ∀x, P (ref x)) (p2 : ∀A B, P A → P B → P (app A B)) (p3 : ∀x A, P A → P (lam x A)) : ∀T, P T := by
  intro T;
  induction T using Quot.ind
  expose_names;
  induction a <;> try simp_all [ref];

  expose_names;
  have := p2 (Quot.mk PreTerm.αEq a) (Quot.mk PreTerm.αEq a_1)
  have : (app (Quot.mk PreTerm.αEq a) (Quot.mk PreTerm.αEq a_1)) = (Quot.mk PreTerm.αEq (a.App a_1)) :=
    (by
      apply Quot.sound;
      apply PreTerm.αEq.refl;)
  simp_all;

  expose_names;
  have := p3 a (Quot.mk PreTerm.αEq a_1) a_ih;

  have : (lam a (Quot.mk PreTerm.αEq a_1)) = (Quot.mk PreTerm.αEq (PreTerm.LTerm.Lam a a_1)) :=
    (by
      apply Quot.sound;
      apply PreTerm.αEq.refl;)
  simp_all;

@[elab_as_elim]
theorem Λcases {P : Λ → Prop}
    (ref : ∀ x, P (ref x))
    (app : ∀ A B, P (app A B))
    (lam : ∀ x A, P (lam x A)) : ∀ T, P T := by
  intro T;
  induction T using Λind <;> grind;




def FV (a : Λ) := Quot.lift PreTerm.FV (fun a b => PreTerm.FV_αEq (a := a) (b := b)) a

@[simp] theorem FV_ref {x : Nat} : FV (ref x) = {x} := by
  simp_all [FV, ref, PreTerm.FV];

@[simp] theorem FV_app {a b : Λ} : FV (app a b) = FV a ∪ FV b := by
  induction a using Quot.ind;
  induction b using Quot.ind;
  simp_all [app, FV, Quot.lift₂, PreTerm.FV];

@[simp] theorem FV_lam {x : Nat} {P : Λ} : FV (lam x P) = FV P \ {x} := by
  induction P using Quot.ind;
  simp_all [lam, FV, PreTerm.FV];

def lsize : Λ → Nat := Quot.lift PreTerm.lsize (PreTerm.lsize_respects_αEq)

@[simp] theorem lsize_ref {x : Nat} : lsize (ref x) = 1 := by
  simp_all [lsize, ref, PreTerm.lsize];

@[simp] theorem lsize_app {a b : Λ} : lsize (app a b) = lsize a + lsize b + 1 := by
  induction a using Quot.ind;
  induction b using Quot.ind;
  simp_all [lsize, app, Quot.lift₂, PreTerm.lsize];

@[simp] theorem lsize_lam {x : Nat} {P : Λ} : lsize (lam x P) = lsize P + 1 := by
  induction P using Quot.ind;
  simp_all [lam, lsize, PreTerm.lsize];


def subst : Nat → Λ → Λ → Λ := fun x => Quot.lift₂ (r := PreTerm.αEq) (s := PreTerm.αEq)
  (fun M N => Quot.mk PreTerm.αEq (PreTerm.subst' x M N))
  (by
    intros;
    apply Quot.sound;
    apply PreTerm.subst'_respects_αEq;
    apply PreTerm.αEq.refl; grind;)
  (by
    intros;
    apply Quot.sound;
    apply PreTerm.subst'_respects_αEq;
    grind; apply PreTerm.αEq.refl;)

@[simp] theorem subst_ref {x y : Nat} {N : Λ} : subst x (ref y) N = if x = y then N else ref y := by
  induction N using Quot.ind;
  by_cases x = y;
  simp_all [subst, PreTerm.subst', PreTerm.subst, ref, Quot.lift₂, subst, PreTerm.shift_binders];
  apply Quot.sound;
  apply PreTerm.αEq.symm;
  apply PreTerm.αEq_shift_binders;
  apply PreTerm.fresh_subset; grind;

  simp_all [subst, PreTerm.subst', PreTerm.subst, ref, Quot.lift₂, subst, PreTerm.shift_binders];
  rfl

@[simp] theorem subst_app {x : Nat} {A B N : Λ} : subst x (app A B) N = app (subst x A N) (subst x B N) := by
  induction A using Quot.ind;
  induction B using Quot.ind;
  induction N using Quot.ind;
  simp_all [subst, Quot.lift₂, app];
  apply Quot.sound;
  apply PreTerm.subst'_app;


@[simp] lemma subst_lam
 {x y : Nat} {P N : Λ} : subst x (lam y P) N =
  ( if x = y then lam y P else
    if y ∈ FV N then
      let y' := PreTerm.fresh (FV P ∪ FV N ∪ {x})
      let P' := subst y P (ref y')
      lam y' (subst x P' N)
    else lam y (subst x P N)
  ) := by
  induction P using Quot.ind;
  induction N using Quot.ind;
  split_ifs <;> simp_all [subst, ref, lam, FV, Quot.lift₂]
  apply Quot.sound;
  apply PreTerm.subst'_lam_l1;

  case neg;
  apply Quot.sound;
  apply PreTerm.subst'_lam_l2;
  grind; grind;


  expose_names;
  apply Quot.sound;

  set y' := (PreTerm.fresh (insert x (PreTerm.FV a ∪ PreTerm.FV a_1)))

  apply PreTerm.αEq.symm;
  apply PreTerm.αEq.trans;
  apply PreTerm.αEq.symm;
  apply PreTerm.subst'_lam_l2;

  intro;
  have : x < PreTerm.fresh (insert x (PreTerm.FV a ∪ PreTerm.FV a_1)) :=
    (by apply PreTerm.lt_fresh; grind;)
  omega;

  intro;
  have : y' < PreTerm.fresh (insert x (PreTerm.FV a ∪ PreTerm.FV a_1)) :=
    (by apply PreTerm.lt_fresh; grind;)
  omega;

  apply PreTerm.subst'_respects_αEq;
  apply PreTerm.αEq.symm;

  set yo := y' + PreTerm.fresh (PreTerm.V a)

  have h1 := PreTerm.αEq_shift_binders a yo
    (by omega;)

  set a' := PreTerm.shift_binders yo a;

  have h2 := PreTerm.shift_binders_disjoint_l1 yo (PreTerm.lsize a)
    a (by omega;);

  obtain ⟨q, qh⟩ := PreTerm.exists_V a;
  have : q < PreTerm.fresh (PreTerm.V a) :=
    (by apply PreTerm.lt_fresh; grind;)

  apply PreTerm.αEq.trans;
  apply PreTerm.αEq.lam;
  exact h1;

  apply PreTerm.αEq.trans;
  apply PreTerm.αEq.alpha a' y y';

  rw [←PreTerm.Binders_union_FV]
  intro a1;
  simp_all;
  rcases a1;

  have := h2 y' (by grind;)
  omega;

  have := PreTerm.FV_αEq h1;
  have : y' < PreTerm.fresh (insert x (PreTerm.FV a ∪ PreTerm.FV a_1)) :=
    (by apply PreTerm.lt_fresh; grind;)
  omega;

  apply PreTerm.αEq.lam;
  apply PreTerm.αEq.symm;
  apply PreTerm.αEq.trans;
  apply PreTerm.subst'_respects_αEq;
  exact h1;
  apply PreTerm.αEq.refl;

  apply PreTerm.αEq_subst'_subst;
  simp_all [PreTerm.FV];

  intro a1;
  have := h2 y' (by grind;)
  omega;

  apply PreTerm.αEq.refl;



theorem FV_subst (x : Nat) (M N : Λ) : ∀v, v ∈ FV (subst x M N) ↔ v ∈ FV M ∧ v ≠ x ∨ v ∈ FV N ∧ x ∈ FV M := by
  induction M using Quot.ind;
  induction N using Quot.ind;
  simp_all [FV, subst, Quot.lift₂, PreTerm.subst']
  expose_names;

  set M' := (PreTerm.shift_binders (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1))) a);
  set N' := (PreTerm.shift_binders (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1))) a_1);
  set o := (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1)));

  have : PreTerm.αEq a_1 N' :=
    (by
      apply PreTerm.αEq_shift_binders a_1 o;
      apply PreTerm.fresh_subset;
      grind;)

  have := PreTerm.FV_αEq this;

  have : PreTerm.αEq a M' :=
    (by
      apply PreTerm.αEq_shift_binders a o;
      apply PreTerm.fresh_subset;
      grind;)

  have := PreTerm.FV_αEq this;

  have : Disjoint (PreTerm.Binders M') (PreTerm.FV N') :=
    (by
      rw [Disjoint];
      intro h1 h2 h3;
      simp_all [Finset.subset_iff];
      intro x' p1;
      have := h2 p1;
      have := h3 p1;

      have := PreTerm.shift_binders_disjoint_l1 o
        (PreTerm.lsize a) a (by omega;) x' (by grind;)
      have : x' < PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1)) :=
        (by apply PreTerm.lt_fresh; grind [PreTerm.FV_sub_V];)
      omega;)

  intro v;

  have := PreTerm.FV_subst x M' N' (by grind;) v;
  simp_all;

@[simp] theorem subst_not_FV (x : Nat) (M N : Λ) (p1 : x ∉ FV M) : (subst x M N) = M := by
  induction M using Quot.ind;
  induction N using Quot.ind;
  simp_all [FV, subst, Quot.lift₂, PreTerm.subst'];
  apply Quot.sound;

  expose_names;
  set M' := (PreTerm.shift_binders (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1))) a);
  set N' := (PreTerm.shift_binders (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1))) a_1);
  set o := (PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1)));

  have : PreTerm.αEq a_1 N' :=
    (by
      apply PreTerm.αEq_shift_binders a_1 o;
      apply PreTerm.fresh_subset;
      grind;)

  have := PreTerm.FV_αEq this;

  have : PreTerm.αEq a M' :=
    (by
      apply PreTerm.αEq_shift_binders a o;
      apply PreTerm.fresh_subset;
      grind;)

  have := PreTerm.FV_αEq this;

  have : Disjoint (PreTerm.Binders M') (PreTerm.FV N') :=
    (by
      rw [Disjoint];
      intro h1 h2 h3;
      simp_all [Finset.subset_iff];
      intro x' p1;
      have := h2 p1;
      have := h3 p1;

      have := PreTerm.shift_binders_disjoint_l1 o
        (PreTerm.lsize a) a (by omega;) x' (by grind;)
      have : x' < PreTerm.fresh (insert x (PreTerm.V a ∪ PreTerm.V a_1)) :=
        (by apply PreTerm.lt_fresh; grind [PreTerm.FV_sub_V];)
      omega;)

  simp_all [PreTerm.subst_not_FV];
  grind [PreTerm.αEq.symm];

theorem alpha (y y' : Nat) (P : Λ) (p1 : y' ∉ FV P) : lam y P = lam y' (subst y P (ref y')) := by
  induction P using Quot.ind;
  simp_all [lam, ref, subst, Quot.lift₂, FV];
  apply Quot.sound;
  expose_names;

  set o := (PreTerm.fresh (insert y (PreTerm.V a ∪ PreTerm.V (PreTerm.LTerm.Ref y'))));
  have h1 := PreTerm.αEq_shift_binders a o
    (by apply PreTerm.fresh_subset; grind;)

  set P' := (PreTerm.shift_binders o a);

  have := PreTerm.FV_αEq h1;
  have h2 := PreTerm.shift_binders_disjoint_l1 o (PreTerm.lsize a) a (by omega;)

  have : y' ∉ PreTerm.V P' :=
    (by
      rw [←PreTerm.Binders_union_FV];
      intro a1;
      simp_all;
      have := h2 y' (by grind;)
      have : y' < PreTerm.fresh (insert y (PreTerm.V a ∪ PreTerm.V (PreTerm.LTerm.Ref y'))) :=
        (by apply PreTerm.lt_fresh; grind [PreTerm.V]);
      omega;)

  have h3 := PreTerm.αEq.alpha P' y y' (by grind;)

  apply PreTerm.αEq.trans;
  exact PreTerm.αEq.trans (PreTerm.αEq.lam y h1) h3;
  apply PreTerm.αEq.lam;
  apply PreTerm.αEq.symm;

  apply PreTerm.αEq.trans;
  apply PreTerm.subst'_respects_αEq;
  exact h1;
  apply PreTerm.αEq.refl;
  apply PreTerm.αEq_subst'_subst;
  simp_all [PreTerm.FV];
  intro;

  grind [PreTerm.Binders_sub_V];

theorem lsize_gt_zero (M : Λ) : 0 < lsize M := by
  induction M using Λind <;> simp;

theorem lsize_subst_ref_l1 (n : Nat) : ∀x y M, lsize M ≤ n → lsize (subst x M (ref y)) = lsize M := by
  induction n;
  grind [lsize_gt_zero];

  intros;
  expose_names;
  cases M using Λcases <;> simp_all;
  split <;> simp;

  expose_names;
  have := h x y A (by grind;)
  have := h x y B (by grind;)
  omega;

  expose_names;
  split_ifs;
  simp;
  simp;
  have := h y (PreTerm.fresh (insert y (insert x (FV A)))) A (by grind;);
  have := h x y (subst y A (ref (PreTerm.fresh (insert y (insert x (FV A)))))) (by grind;);
  omega;

  simp;
  apply h;
  omega;










inductive βstep : Λ → Λ → Prop where
| redex (x : Nat) (P Q : Λ) : βstep (app (lam x P) Q) (subst x P Q)
| lam (x : Nat) {P Q : Λ} (p1 : βstep P Q) : βstep (lam x P) (lam x Q)
| appL {P Q : Λ} (N : Λ) (p1 : βstep P Q) : βstep (app P N) (app Q N)
| appR {P Q : Λ} (N : Λ) (p1 : βstep P Q) : βstep (app N P) (app N Q)

inductive βmstep : Λ → Λ → Prop where
| redex (x : Nat) (P Q : Λ) : βmstep (app (lam x P) Q) (subst x P Q)
| lam (x : Nat) {P Q : Λ} (p1 : βmstep P Q) : βmstep (lam x P) (lam x Q)
| appL {P Q : Λ} (N : Λ) (p1 : βmstep P Q) : βmstep (app P N) (app Q N)
| appR {P Q : Λ} (N : Λ) (p1 : βmstep P Q) : βmstep (app N P) (app N Q)
| refl (P : Λ) : βmstep P P
| trans {P Q R : Λ} (p1 : βmstep P Q) (p2 : βmstep Q R) : βmstep P R

inductive βEq : Λ → Λ → Prop where
| redex (x : Nat) (P Q : Λ) : βEq (app (lam x P) Q) (subst x P Q)
| lam (x : Nat) {P Q : Λ} (p1 : βEq P Q) : βEq (lam x P) (lam x Q)
| appL {P Q : Λ} (N : Λ) (p1 : βEq P Q) : βEq (app P N) (app Q N)
| appR {P Q : Λ} (N : Λ) (p1 : βEq P Q) : βEq (app N P) (app N Q)
| refl (P : Λ) : βEq P P
| trans {P Q R : Λ} (p1 : βEq P Q) (p2 : βEq Q R) : βEq P R
| symm  {P Q : Λ} (p1 : βEq P Q) : βEq Q P



-- diamond property
def DP (r : Λ → Λ → Prop) : Prop :=
  ∀A B C, r A B ∧ r A C → ∃D, r B D ∧ r C D


lemma cr_l1  {r s : Λ → Λ → Prop} (p2 : ∀A B, Relation.TransGen r A B ↔ s A B) (p1 : DP r) (M M' N : Λ) : r M M' → s M N → ∃N', s M' N' ∧ r N N' := by
  simp_all [DP]; intros;
  expose_names;

  have a1 := (p2 M N).mpr h_1;
  induction a1;

  expose_names;
  have a2 := p1 M M' b
    (by grind) (by grind);
  apply a2.elim; intros;
  expose_names;
  exists a;
  grind;

  expose_names;
  simp_all;
  apply a_ih.elim; intros;
  expose_names;

  have := p1 b c a (by grind;) (by grind;)
  apply this.elim; intros;
  expose_names;
  exists a_1;
  grind;

lemma cr_l2 {r s : Λ → Λ → Prop} (p2 : ∀A B, Relation.TransGen r A B ↔ s A B) (p1 : DP r) : DP s := by
  simp [DP];

  intros;
  expose_names;
  have a1 := (p2 A B).mpr h;
  induction a1;

  expose_names;
  have h1 := cr_l1 (r := r) p2 p1 A b C
    (by grind;) (by grind;)
  apply h1.elim; intros;
  expose_names;
  exists a;
  grind;

  simp_all;
  expose_names;
  apply a_ih.elim; intros;
  expose_names;
  have h1 := cr_l1 (r := r) p2 p1 b c a
    (by grind;) (by grind;)
  apply h1.elim;  intros;
  expose_names;
  exists a_1;
  grind;

inductive ιstep : Λ → Λ → Prop where
| refl (P : Λ) : ιstep P P
| lam (x : Nat) {P Q : Λ} (p1 : ιstep P Q) : ιstep (lam x P) (lam x Q)
| app {P P' Q Q' : Λ} (p2 : ιstep P P') (p1 : ιstep Q Q') : ιstep (app P Q) (app P' Q')
| redex {P P' Q Q' : Λ} (x : Nat) (p2 : ιstep P P') (p1 : ιstep Q Q') : ιstep (app (lam x P) Q) (subst x P' Q')





end LC
