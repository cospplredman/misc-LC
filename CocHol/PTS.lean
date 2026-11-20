import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

inductive PTS {S : Type} where
  | sort (s : S) : PTS
  | ref (x : Nat) : PTS
  | app (a b : PTS (S := S)) : PTS
  | lam (T p : PTS (S := S)) : PTS
  | pi (T p : PTS (S := S)) : PTS
deriving DecidableEq

def shift' {S : Type} (M : PTS (S := S)) (n : Nat) (k : Nat) : PTS (S := S) :=
  match M with
  | .sort s => .sort s
  | .ref a => if a ≥ k then .ref (a + n) else .ref a
  | .app a b => .app (shift' a n k) (shift' b n k)
  | .lam T p => .lam (shift' T n k) (shift' p n (k + 1))
  | .pi T p => .pi (shift' T n k) (shift' p n (k + 1))

@[simp]
def shift {S : Type} := (shift' (S := S) · · 0)

def subst' {S : Type} (M N : PTS (S := S)) (k : Nat) : PTS (S := S) :=
  match M with
  | .sort s => .sort s
  | .ref a =>
    if a = k then shift N k
    else if a > k then .ref (a-1)
    else .ref a
  | .app a b => .app (subst' a N k) (subst' b N k)
  | .lam T p => .lam (subst' T N k) (subst' p N (k + 1))
  | .pi T p => .pi (subst' T N k) (subst' p N (k + 1))

@[simp]
def subst {S : Type} := (subst' (S := S) · · 0)

-- church rosser
section
variable {𝕊 : Type} -- sort type

inductive βstep : PTS (S := 𝕊) → PTS (S := 𝕊) → Prop where
  | redex (T M N) : βstep (.app (.lam T M) N) (subst M N)
  | appL (M M' N) (h : βstep M M') : βstep (.app M N) (.app M' N)
  | appR (N N' M) (h : βstep N N') : βstep (.app M N) (.app M N')
  | lamT (T T' M) (h : βstep T T') : βstep (.lam T M) (.lam T' M)
  | lamB (T M M') (h : βstep M M') : βstep (.lam T M) (.lam T M')
  | piT  (T T' M) (h : βstep T T') : βstep (.pi T M) (.pi T' M)
  | piB  (T M M') (h : βstep M M') : βstep (.pi T M) (.pi T M')

inductive βmstep : PTS (S := 𝕊) → PTS (S := 𝕊) → Prop where
  | refl (a) : βmstep a a
  | trans (a b c) (h : βmstep a b) (h1 : βmstep b c) : βmstep a c
  | redex (T M N) : βmstep (.app (.lam T M) N) (subst M N)
  | app (M M' N N') (h1 : βmstep M M') (h2 : βmstep N N') : βmstep (.app M N) (.app M' N')
  | lam (T T' M M') (h1 : βmstep T T') (h2 : βmstep M M') : βmstep (.lam T M) (.lam T' M')
  | pi (T T' M M') (h1 : βmstep T T') (h2 : βmstep M M') : βmstep (.pi T M) (.pi T' M')

@[simp]
theorem βmstep_refl {t : PTS (S := 𝕊)} : βmstep t t := by apply βmstep.refl;

def βrstep := Relation.ReflGen (βstep (𝕊 := 𝕊))

@[simp]
theorem βrstep_refl (a) : βrstep (𝕊 := 𝕊) a a := by
  apply Relation.ReflGen.refl;

inductive ιstep : PTS (S := 𝕊) → PTS (S := 𝕊) → Prop where
| refl {P} : ιstep P P
| lam {T T' P P'} (p1 : ιstep T T') (p2 : ιstep P P') : ιstep (.lam T P) (.lam T' P')
| pi {T T' P P'} (p1 : ιstep T T') (p2 : ιstep P P') : ιstep (.pi T P) (.pi T' P')
| app {P P' Q Q'} (p2 : ιstep P P') (p1 : ιstep Q Q') : ιstep (.app P Q) (.app P' Q')
| redex {T P P' Q Q'} (p2 : ιstep P P') (p3 : ιstep Q Q')
  : ιstep (.app (.lam T P) Q) (subst P' Q')

@[simp]
theorem ιstep_refl {P} : ιstep (𝕊 := 𝕊) P P := ιstep.refl (P := P)

instance : IsTrans (PTS (S := 𝕊)) βmstep where
  trans (a b c) := βmstep.trans a b c

@[simp]
theorem shift_zero (M : PTS (S := 𝕊)) : ∀k, shift' M 0 k = M := by
  induction M <;> simp! <;> grind;

@[simp]
theorem shift_shift (M : PTS (S := 𝕊)) : ∀a b c c', c ≤ c' → c' ≤ c + a → shift' (shift' M a c) b c' = shift' M (a + b) c := by
  induction M <;> intros <;> simp! <;> grind [shift'];

@[simp]
theorem subst_shift (M N : PTS (S := 𝕊)) (k : Nat) : ∀c' c, c' ≤ c → c < c' + k → subst' (shift' M k c') N c = shift' M (k - 1) c' := by
  induction M <;> simp_all! <;> grind [subst'];

theorem shift_inj {S : Type} {a b n k} (p1 : shift' (S := S) a n k = shift' b n k) : a = b := by
  induction a generalizing n k b <;> cases b <;> simp! at p1
  <;> (try repeat' split at p1 <;> try simp! at p1) <;> simp_all! <;> grind;

@[simp]
theorem shift_subst (M N : PTS (S := 𝕊)) : ∀n k, shift' (subst' M N k) n k = subst' (shift' M n (k+1)) (shift' N n 0) k := by
  induction M <;> intros <;> simp_all!;
  (repeat' split; (try simp_all!;)) <;> (try simp!;) <;> grind only;

theorem shift_shift_comm (N : PTS (S := 𝕊)) (m k v c : Nat) (h : c ≥ k) :
    shift' (shift' N k m) v (c + m) =
    shift' (shift' N v (c - k + m)) k m := by
  induction N generalizing m k c <;> simp_all!;
  (repeat' split <;> (try simp!;)) <;> omega;
  all_goals grind only;


theorem shift_after_subst (M N : PTS (S := 𝕊)) (v k c : Nat) (h : c ≥ k) :
    shift' (subst' M N k) v c =
    subst' (shift' M v (c + 1)) (shift' N v (c - k)) k := by
  induction M generalizing k c <;> simp_all!;
  (repeat' split <;> (try simp!)) <;> (try omega);
  apply shift_shift_comm;
  omega;

theorem shift_subst_comm (T S : PTS (S := 𝕊)) (c d m : Nat) (hm : m ≤ c) :
    shift' (subst' T S c) d m
  = subst' (shift' T d m) S (c + d) := by
  induction T generalizing c d m <;> simp_all!;
  (repeat' split <;> (try simp_all!)) <;> omega;
  all_goals grind only;

theorem subst_subst (M S T : PTS (S := 𝕊)) (c d : Nat) :
    subst' (subst' M S (c + d + 1)) (subst' T S c) d
  = subst' (subst' M T d) S (c + d) := by
  induction M generalizing c d <;> simp_all!;
  (repeat' split <;> (try simp_all!)) <;> (try omega)
  grind only [shift_subst_comm];
  all_goals
  ( expose_names;
    exact p_ih (c := c) (d := d + 1))

-- diamond property
def DP {Λ : Type} (r : Λ → Λ → Prop) : Prop :=
  ∀A B C, r A B ∧ r A C → ∃D, r B D ∧ r C D

theorem TransGen_le {Λ : Type} {r1 r2 : Λ → Λ → Prop} : (∀A B, r1 A B → r2 A B) → (∀A B, Relation.TransGen r1 A B → Relation.TransGen r2 A B) := by
  intros;
  expose_names;
  induction h_1;
  apply Relation.TransGen.single;
  grind;
  grind;

theorem cr_l1  {Λ : Type} {r s : Λ → Λ → Prop} (p2 : ∀A B, Relation.TransGen r A B ↔ s A B) (p1 : DP r) (M M' N : Λ) : r M M' → s M N → ∃N', s M' N' ∧ r N N' := by
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

theorem TransGen_DP {Λ : Type} {r s : Λ → Λ → Prop} (p2 : ∀A B, Relation.TransGen r A B ↔ s A B) (p1 : DP r) : DP s := by
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

theorem ιstep_shift : ∀N N' v c, ιstep (𝕊 := 𝕊) N N' → ιstep (shift' N v c) (shift' N' v c) := by
  intro N N' v c p1;
  induction p1 generalizing c;
  apply ιstep.refl;
  apply ιstep.lam <;> grind only;
  apply ιstep.pi <;> grind only;
  apply ιstep.app <;> grind only;

  expose_names;
  have := ιstep.redex (p2_ih (c+1)) (p3_ih c) (T := (shift' T v c))
  have := shift_after_subst P' Q' v 0 c (by omega;)
  simp_all!;

theorem ιstep_subst { M M' N N'} (p1 : ιstep (𝕊 := 𝕊) M M') (p2 : ιstep N N') : ∀c, ιstep (subst' M N c) (subst' M' N' c) := by
  induction p1 <;> intros;
  expose_names;

  induction P generalizing c <;> simp!;
  split; apply ιstep_shift; grind;
  apply ιstep.refl;
  apply ιstep.app <;> grind;

  apply ιstep.lam <;> grind;
  apply ιstep.pi <;> grind;

  apply ιstep.lam <;> grind;
  apply ιstep.pi <;> grind;

  apply ιstep.app <;> grind;

  expose_names;
  simp!;
  have := subst_subst P' N' Q' c 0;
  have := ιstep.redex (p2_ih (c := c + 1)) (p3_ih (c := c)) (T := (subst' T N c))
  simp_all;

theorem ιstep_pi_inv {A B A' B'} (h : ιstep (.pi (S := 𝕊) A B) (.pi A' B')) :
    ιstep A A' ∧ ιstep B B' := by
  cases h;
  grind [ιstep.refl];
  simp_all!;

theorem ιstep_sort {s S} (h : ιstep (𝕊 := 𝕊) (.sort s) S) : S = (.sort s) := by
  cases h; simp!;

theorem shift_ιstep {S : Type} {a n k B} (p1 : ιstep (shift' (S := S) a n k) B) : ∃Q, shift' Q n k = B := by
  induction a generalizing n k B <;> simp_all!;
  cases p1;
  expose_names;
  exists (.sort s)

  split at p1;
  cases p1;
  expose_names;
  exists .ref x;
  simp_all!;

  cases p1;
  expose_names;
  exists .ref x
  simp_all!;

  expose_names;
  cases h1 : ((shift' a n k).app (shift' b n k)) <;> simp_all!;
  cases p1;

  expose_names;
  exists .app a b;
  simp_all!;

  expose_names;
  rw [←h1.left] at p2
  rw [←h1.right] at p1
  obtain ⟨P, Ph⟩ := a_ih p2;
  obtain ⟨Q, Qh⟩ := b_ih p1;
  exists .app P Q;
  simp_all!;

  expose_names;
  rw [←h1.right] at p3
  obtain ⟨Q, Qh⟩ := b_ih p3;
  cases a <;> simp_all!;
  split at h1 <;> simp_all!;
  expose_names;

  have := a_ih (n := n) (k := k) (B := .lam T P')

  rw [h1.left.left, h1.left.right] at this;

  obtain ⟨P, Ph⟩ := this
    (by
      apply ιstep.lam;
      apply ιstep.refl;
      assumption;)

  cases P <;> simp_all!;
  split at Ph <;> simp_all!;
  expose_names;

  exists subst p_1 Q
  have := shift_after_subst p_1 Q n 0 k
  simp_all!;

  cases p1;

  expose_names;
  exists .lam T p

  expose_names;
  obtain ⟨T', T'h⟩ := T_ih p1;
  obtain ⟨p', p'h⟩ := p_ih p2;
  exists .lam T' p'
  simp_all!;

  cases p1;

  expose_names;
  exists .pi T p

  expose_names;
  obtain ⟨T', T'h⟩ := T_ih p1;
  obtain ⟨p', p'h⟩ := p_ih p2;
  exists .pi T' p'
  simp_all!;

theorem ιstep_shift_inv' {S : Type} {P Q a b n k} (p1 : ιstep P Q)
  (p2 : P = (shift' (S := S) a n k))
  (p3 : Q = (shift' b n k)) : ιstep a b := by
  induction p1 generalizing a b n k;


  simp_all;
  have := shift_inj p2;
  simp_all;


  case redex =>
    cases a <;> simp_all!;
    split at p2 <;> simp_all!;

    expose_names;
    cases a <;> simp_all!;
    split at p2 <;> simp_all!;

    obtain ⟨Da, Dah⟩ := shift_ιstep p2_1;
    obtain ⟨Db, Dbh⟩ := shift_ιstep p3_1;

    symm at Dah;
    symm at Dbh;
    simp_all!;

    have := p2_ih (by rfl) (by rfl)
    have := p3_ih (by rfl) (by rfl)
    expose_names;

    have := ιstep_subst this_1 this 0;
    have := ιstep_shift (subst' p b_1 0) (subst' Da Db 0) n k this

    have := shift_after_subst Da Db n 0 k (by omega;)
    simp_all!;
    have := shift_inj this;
    simp_all!;

    rw [←this]
    apply ιstep.redex;
    assumption;
    assumption;


  all_goals (
    cases a <;> simp_all!;
    split at p2 <;> simp_all!;
    cases b <;> simp_all!;
    split at p3 <;> simp_all!;

    expose_names;
    grind [ιstep.lam, ιstep.pi, ιstep.app];)

theorem ιstep_shift_inv {S : Type} {a b n k} (p1 : ιstep (shift' (S := S) a n k) (shift' b n k)) : ιstep a b := by
  apply ιstep_shift_inv' p1 rfl rfl;

--TODO clean this up...
theorem cr_l4 : DP (ιstep (𝕊 := 𝕊))  := by
  rw [DP]; intro A B C h;
  induction h.left generalizing C;

  exists C;
  grind [ιstep.refl];



  expose_names;
  simp_all;
  cases h.right;
  obtain ⟨D, hD⟩ := p2_ih P (by grind [ιstep.refl])
  exists T'.lam D;
  grind [ιstep.lam, ιstep.refl];
  expose_names;
  obtain ⟨D, hD⟩ := p2_ih P'_1 (by grind;);
  obtain ⟨T'', hT''⟩ := p1_ih T'_1 (by grind;);
  exists T''.lam D;
  grind [ιstep.lam, ιstep.refl];



  expose_names;
  simp_all;
  cases h.right;
  obtain ⟨D, hD⟩ := p2_ih P (by grind [ιstep.refl])
  exists T'.pi D;
  grind [ιstep.pi, ιstep.refl];
  expose_names;
  obtain ⟨D, hD⟩ := p2_ih P'_1 (by grind;);
  obtain ⟨T'', hT''⟩ := p1_ih T'_1 (by grind;);
  exists T''.pi D;
  grind [ιstep.pi, ιstep.refl];




  expose_names;

  cases h.right;

  obtain ⟨D1, hD1⟩ := p2_ih P (by grind [ιstep.refl]);
  obtain ⟨D2, hD2⟩ := p1_ih Q (by grind [ιstep.refl]);

  exists (.app D1 D2)
  grind [ιstep.app];

  expose_names;
  obtain ⟨D1, hD1⟩ := p2_ih P'_1 (by grind;);
  obtain ⟨D2, hD2⟩ := p1_ih Q'_1 (by grind [ιstep.refl]);
  exists .app D1 D2
  grind [ιstep.app];


  expose_names;
  obtain ⟨D1, hD1⟩ := p2_ih (T.lam P'_1) (by grind [ιstep.lam, ιstep.refl];)
  obtain ⟨D2, hD2⟩ := p1_ih Q'_1 (by grind;)

  have := ιstep.redex (T := T) hD1.left hD2.left;

  cases hD1.2;
  have := ιstep_subst (ιstep.refl (P := P'_1)) hD2.2 (c := 0);
  exists subst P'_1 D2;
  simp_all!;
  have := ιstep.redex (T := T) p2_1 hD2.1

  cases p2;
  simp_all;

  expose_names;
  apply ιstep.redex;

  cases hD1 with
  | lam h h1 => exact h1
  | refl => exact ιstep.refl

  grind;

  expose_names;
  exists subst P'_2 D2;
  have := ιstep.redex (T := T') p2_2 hD2.1;

  have := ιstep_subst p2_2 hD2.right (c := 0);
  simp_all;

  cases p2 with
  | refl =>
      cases hD1.left with
      | refl => exact ιstep.redex (ιstep.refl (P := P)) hD2.left
      | lam h h1 => exact ιstep.redex h1 hD2.left
  | lam hP =>
      expose_names;
      cases hD1.left with
      | refl => exact ιstep.redex (ιstep.refl (P := P'_2)) hD2.left
      | lam h h1 => exact ιstep.redex h1 hD2.left

  expose_names;
  cases h.right with
  | refl =>
      exact ⟨subst P' Q', ιstep.refl, h.left⟩
  | app p2 p1 =>
      cases p2 with
      | refl =>
          -- C1 = P✝.lam
          expose_names;
          obtain ⟨D2, hQ'D2, hC2D2⟩ := p3_ih Q'_1 ⟨p3, p1⟩
          exact ⟨subst P' D2,
            ιstep_subst (ιstep.refl) hQ'D2 (c := 0),
            ιstep.redex p2 hC2D2⟩
      | lam hT hP =>
          -- C1 = .lam P0, hP : ιstep P✝ P0
          expose_names;
          obtain ⟨D1, hP'D1, hP0D1⟩ := p2_ih P'_1 ⟨p2, hP⟩
          obtain ⟨D2, hQ'D2, hC2D2⟩ := p3_ih Q'_1 ⟨p3, p1⟩
          exact ⟨subst D1 D2,
            ιstep_subst hP'D1 hQ'D2 (c := 0),
            ιstep.redex hP0D1 hC2D2⟩
  | redex p2 p1 =>
    expose_names;
    obtain ⟨D1, hP'D1, hP''D1⟩ := p2_ih P'_1 ⟨p2_1, p2⟩
    obtain ⟨D2, hQ'D2, hQ''D2⟩ := p3_ih Q'_1 ⟨p3, p1⟩
    exact ⟨subst D1 D2,
      ιstep_subst hP'D1 hQ'D2 (c := 0),
      ιstep_subst hP''D1 hQ''D2 (c := 0)⟩

theorem βmstep_ιstep (A B) : ιstep (𝕊 := 𝕊) A B → βmstep A B := by
  intro a1;
  induction a1;
  apply βmstep.refl;
  apply βmstep.lam <;> assumption;
  apply βmstep.pi <;> assumption;

  apply βmstep.trans;
  apply βmstep.app <;> assumption;
  apply βmstep.refl;

  apply βmstep.trans;
  apply βmstep.trans;
  apply βmstep.app;
  apply βmstep.lam;
  apply βmstep.refl;
  assumption;
  assumption;
  apply βmstep.redex;
  apply βmstep.refl;

theorem βmstep_βrstep (A B) : βrstep (𝕊 := 𝕊) A B → βmstep A B := by
  intro a1;
  induction a1;
  apply βmstep.refl;
  rename_i h; induction h;
  apply βmstep.redex;
  apply βmstep.app <;> simp_all!;
  apply βmstep.app <;> simp_all!;
  apply βmstep.lam <;> simp_all!;
  apply βmstep.lam <;> simp_all!;
  apply βmstep.pi <;> simp_all!;
  apply βmstep.pi <;> simp_all!;

theorem ιstep_βrstep (A B) : βrstep (𝕊 := 𝕊) A B → ιstep A B := by
  intro a1;
  induction a1;
  apply ιstep.refl;
  rename_i h; induction h;
  apply ιstep.redex <;> apply ιstep.refl;
  apply ιstep.app <;> simp_all!;
  apply ιstep.app <;> simp_all!;
  apply ιstep.lam <;> simp_all!;
  apply ιstep.lam <;> simp_all!;
  apply ιstep.pi <;> simp_all!;
  apply ιstep.pi <;> simp_all!;

theorem TransGenβrstep_iff_βmstep (A B) : Relation.TransGen (βrstep (𝕊 := 𝕊)) A B ↔ βmstep A B := by
  apply Iff.intro;
  intro a1;
  induction a1;
  apply βmstep_βrstep; assumption;
  grind [βmstep_βrstep, βmstep.trans];

  intro a1;
  induction a1;
  apply Relation.TransGen.single; simp!;

  apply Relation.TransGen.trans <;> assumption;

  apply Relation.TransGen.single;
  apply Relation.ReflGen.single;
  apply βstep.redex;



  have h1 : (∀ (M M' N N' : PTS (S := 𝕊)), Relation.TransGen βrstep M M' → Relation.TransGen βrstep N N' → Relation.TransGen βrstep (M.app N) (M'.app N')) :=
    (by
      intro M M' N N' p1 p2;
      induction p1 <;> induction p2;
      expose_names;
      cases h <;> cases h_1;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.refl;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.appR; assumption;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.appL; assumption;


      apply Relation.TransGen.tail;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.appL; assumption;
      apply Relation.ReflGen.single;
      apply βstep.appR; assumption;

      rename_i a _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.appR; assumption;

      rename_i a _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.appL; assumption;

      rename_i a _ _ _ _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.appL; assumption;)

  apply h1 <;> assumption;

  have h1 : (∀ (M M' N N' : PTS (S := 𝕊)), Relation.TransGen βrstep M M' → Relation.TransGen βrstep N N' → Relation.TransGen βrstep (M.lam N) (M'.lam N')) :=
    (by
      intro M M' N N' p1 p2;
      induction p1 <;> induction p2;
      expose_names;
      cases h <;> cases h_1;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.refl;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.lamB; assumption;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.lamT; assumption;


      apply Relation.TransGen.tail;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.lamB; assumption;
      apply Relation.ReflGen.single;
      apply βstep.lamT; assumption;

      rename_i a _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.lamB; assumption;

      rename_i a _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.lamT; assumption;

      rename_i a _ _ _ _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.lamT; assumption;)

  apply h1 <;> assumption;

  have h1 : (∀ (M M' N N' : PTS (S := 𝕊)), Relation.TransGen βrstep M M' → Relation.TransGen βrstep N N' → Relation.TransGen βrstep (M.pi N) (M'.pi N')) :=
    (by
      intro M M' N N' p1 p2;
      induction p1 <;> induction p2;
      expose_names;
      cases h <;> cases h_1;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.refl;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.piB; assumption;

      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.piT; assumption;


      apply Relation.TransGen.tail;
      apply Relation.TransGen.single;
      apply Relation.ReflGen.single;
      apply βstep.piB; assumption;
      apply Relation.ReflGen.single;
      apply βstep.piT; assumption;

      rename_i a _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.piB; assumption;

      rename_i a _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.piT; assumption;

      rename_i a _ _ _ _ _ _;
      cases a; assumption;
      apply Relation.TransGen.tail; assumption;
      apply Relation.ReflGen.single;
      apply βstep.piT; assumption;)

  apply h1 <;> assumption;

theorem TransGenιstep_iff_βmstep : ∀A B, Relation.TransGen (ιstep (𝕊 := 𝕊)) A B ↔ βmstep A B := by
  intro A B;
  have := Relation.transGen_minimal (r := βmstep) (r' := βmstep)
    (by intro _ _ _; assumption;) A B
  have := TransGen_le βmstep_βrstep A B;
  have := TransGen_le βmstep_ιstep A B;
  have := TransGen_le ιstep_βrstep A B;
  have := TransGenβrstep_iff_βmstep A B;

  expose_names;
  apply Iff.intro;
  intro a1;
  exact this_1 (this_3 a1);
  grind;

theorem church_rosser : DP (βmstep (𝕊 := 𝕊)) := by
  apply TransGen_DP;
  apply TransGenιstep_iff_βmstep;
  apply cr_l4;

theorem βmstep_subst  { M M' N N'} (p1 : βmstep (𝕊 := 𝕊) M M') (p2 : βmstep N N') : ∀c, βmstep (subst' M N c) (subst' M' N' c) := by
  intro c;
  rw [←TransGenιstep_iff_βmstep] at p1 p2 ⊢

  induction p1 <;> induction p2;
  apply Relation.TransGen.single;
  apply ιstep_subst <;> assumption;

  all_goals (
    apply Relation.TransGen.tail; assumption;
    apply ιstep_subst <;> simp_all!;
  )

theorem βmstep_shift : ∀N N' v c, βmstep (𝕊 := 𝕊) N N' → βmstep (shift' N v c) (shift' N' v c) := by
  intro N N' v c p1 ;
  rw [←TransGenιstep_iff_βmstep] at p1 ⊢ ;

  induction p1;

  apply Relation.TransGen.single;
  apply ιstep_shift; assumption;

  apply Relation.TransGen.tail; assumption;
  apply ιstep_shift; simp_all!;

theorem βmstep.source_pi {X C : PTS (S := 𝕊)}
    (h : βmstep X C) :
    ∀ {A B : PTS}, X = .pi A B →
    ∃ A' B', C = .pi A' B' ∧ βmstep A A' ∧ βmstep B B' := by
  induction h with
  | refl =>
      intro A B hX
      subst hX
      exact ⟨A, B, rfl, βmstep.refl A, βmstep.refl B⟩
  | trans h1 h2 ih1 ih2 =>
      expose_names;
      intro A B hX
      obtain ⟨A', B', hY, hA', hB'⟩ := h_ih hX
      obtain ⟨A'', B'', hC, hA'', hB''⟩ := h1_ih hY
      exact ⟨A'', B'', hC,
        βmstep.trans _ _ _ hA' hA'',
        βmstep.trans _ _ _ hB' hB''⟩
  | redex T M N => intro A B hX; cases hX
  | app _ _ _ _ _ _ => intro A B hX; cases hX
  | lam _ _ _ _ _ _ => intro A B hX; cases hX
  | pi h1 h2 =>
      expose_names;
      intro A B hX
      cases hX
      exact ⟨_, _, rfl, h1_1, h2_1⟩

theorem βmstep.pi_inv {A B A' B'}
    (h : βmstep (.pi (S := 𝕊) A B) (.pi A' B')) :
    βmstep A A' ∧ βmstep B B' := by
  have := βmstep.source_pi h (by rfl);
  grind;

theorem βmstep_sort {s S} (h : βmstep (𝕊 := 𝕊) (.sort s) S) : S = (.sort s) := by
  rw [←TransGenιstep_iff_βmstep] at h;
  induction h;
  apply ιstep_sort;
  assumption;

  simp_all!;
  apply ιstep_sort;
  assumption;

def βeq := Relation.Join (βmstep (𝕊 := 𝕊))

@[simp]
theorem βeq.refl (a) : βeq (𝕊 := 𝕊) a a := by
  exists a; simp!;

theorem βeq.symm (a b) : βeq (𝕊 := 𝕊) a b → βeq b a := by
  intro a1;
  obtain ⟨D, Dh⟩ := a1;
  exists D;
  grind;

theorem βeq.trans (a b c) : βeq (𝕊 := 𝕊) a b → βeq b c → βeq a c := by
  intro a1 a2;
  obtain ⟨Dl, Dlh⟩ := a1;
  obtain ⟨Dr, Drh⟩ := a2;
  obtain ⟨D, Dh⟩ := church_rosser b Dl Dr ⟨Dlh.2, Drh.1⟩
  exists D;
  grind [βmstep.trans];

theorem βeq_subst { M M' N N'} (p1 : βeq (𝕊 := 𝕊) M M') (p2 : βeq N N') : ∀c, βeq (subst' M N c) (subst' M' N' c) := by
  intro c;
  obtain ⟨DM, DMh⟩ := p1
  obtain ⟨DN, DNh⟩ := p2
  exists subst' DM DN c
  grind only [βmstep_subst]

theorem βeq_shift : ∀N N' v c, βeq (𝕊 := 𝕊) N N' → βeq (shift' N v c) (shift' N' v c) := by
  intro N N' v c p1;
  obtain ⟨DM, DMh⟩ := p1
  exists shift' DM v c
  grind only [βmstep_shift]

theorem βeq.pi_inv {A B A' B'} (h : βeq (.pi (S := 𝕊) A B) (.pi A' B')) :
    βeq A A' ∧ βeq B B' := by

  obtain ⟨D, Dh⟩ := h;
  obtain ⟨Dla, Dlb, Dlh⟩ := βmstep.source_pi Dh.left (by rfl);
  obtain ⟨Dra, Drb, Drh⟩ := βmstep.source_pi Dh.right (by rfl);

  simp_all!;

  and_intros;
  exists Dla;
  grind;
  exists Dlb;
  grind;

theorem βeq_βmstep (A B) (p1 : βmstep (𝕊 := 𝕊) A B) : βeq A B := by
  exists B;
  grind [βmstep.refl];

theorem βeq.source_pi {A B C : PTS (S := 𝕊)} (h : βeq (.pi A B) C) :
    ∃ A' B', βeq C (.pi A' B') ∧ βeq A A' ∧ βeq B B' := by
  obtain ⟨D, hD1, hD2⟩ := h
  obtain ⟨A', B', rfl, hA', hB'⟩ := βmstep.source_pi hD1 (by rfl)

  exists A', B'
  grind [βeq_βmstep];

def SN {𝕊} (T : PTS (S := 𝕊)) : Prop := Acc (Function.swap (βstep (𝕊 := 𝕊))) T

def NF {𝕊} (T : PTS (S := 𝕊)) : Prop := ∀y, ¬βstep T y

theorem acc_normal_form {α : Type} {r : α → α → Prop} {x : α}
    (h : Acc r x) :
    ∃ n, Relation.ReflTransGen r n x ∧ ∀ y, ¬ r y n := by
  induction h with
  | intro x _ ih =>
    by_cases hx : ∃ y, r y x
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨n, hreach, hnf⟩ := ih y hy
      exists n
      simp_all!;
      apply Relation.ReflTransGen.tail <;> assumption;
    · push Not at hx
      exact ⟨x, Relation.ReflTransGen.refl, hx⟩

theorem ReflTransGenιstep_TransGenιstep {a b}
  (p1 : Relation.ReflTransGen (ιstep (𝕊 := 𝕊)) a b)
  : Relation.TransGen ιstep a b := by
  induction p1;
  apply Relation.TransGen.single;
  apply ιstep.refl;

  apply Relation.TransGen.tail <;> assumption;

theorem SN_NF {𝕊} (T : PTS (S := 𝕊)) (p1 : SN T) : ∃y, βmstep T y ∧ NF y := by
  obtain ⟨y, yh⟩ := acc_normal_form p1
  exists y;
  simp_all! [NF, flip];
  rw [←TransGenβrstep_iff_βmstep];
  rw [βrstep, Relation.transGen_reflGen];
  exact yh.left.swap;

theorem NF_βmstep (a b) (p1 : NF (𝕊 := 𝕊) a) (p2 : βmstep a b) : a = b := by
  rw [←TransGenβrstep_iff_βmstep, βrstep, Relation.transGen_reflGen] at p2;
  cases p2.swap;
  rfl;

  expose_names;
  rw [Function.swap] at h_1;
  have := p1 b_1;
  grind;

theorem unique_NF {𝕊} (T : PTS (S := 𝕊)) {x y} (p1 : βmstep T x ∧ NF x) (p2 : βmstep T y ∧ NF y) : x = y := by
  obtain ⟨D, Dh⟩ := church_rosser T x y (by grind;)
  have := p1.right D;
  simp_all [NF];
  have := NF_βmstep x D p1.2;
  have := NF_βmstep y D p2.2;
  simp_all!;

end


inductive PTSHasType (𝕊 : Type) (𝔸 : (𝕊 × 𝕊) → Prop) (ℝ : (𝕊 × 𝕊 × 𝕊) → Prop)
  («≅» : PTS (S := 𝕊) → PTS (S := 𝕊) → Prop)
  : List (PTS (S := 𝕊)) → PTS (S := 𝕊) → PTS (S := 𝕊) → Prop where

  | ax {Γ s1 s2} (p1 : 𝔸 (s1, s2))
    : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.sort s1) (.sort s2)

  | st {Γ A s}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A s)
    : PTSHasType 𝕊 𝔸 ℝ «≅» (A :: Γ) (.ref 0) (shift A 1)

  | wk {Γ A B C s}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A B)
    (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ C s)
    : PTSHasType 𝕊 𝔸 ℝ «≅» (C :: Γ) (shift A 1) (shift B 1)

  | pi {Γ A B s1 s2 s3}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A (.sort s1))
    (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» (A :: Γ) B (.sort s2))
    (p3 : ℝ (s1, s2, s3))
    : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.pi A B) (.sort s3)

  | app {Γ a A B C}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ C (.pi A B))
    (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ a A)
    : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.app C a) (subst B a)

  | lam {Γ A b B s}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» (A :: Γ) b B)
    (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.pi A B) (.sort s))
    : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.lam A b) (.pi A B)

  | conv {Γ A B B' s}
    (p1 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A B)
    (p2 : «≅» B B')
    (p3 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ B' s)
    : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A B'

def ctx_subst {S : Type} (Γ : List (PTS (S := S))) (t : PTS (S := S)) :=
  match Γ with
  | .cons x xs => (subst' x t (xs.length)) :: (ctx_subst xs t)
  | [] => []

@[simp]
theorem ctx_subst_length {S : Type} : ∀(Δ : List (PTS (S := S))) t, (ctx_subst Δ t).length = Δ.length := by
  intro Δ t;
  induction Δ <;> simp_all!;

def ctx_shift {S : Type} (Γ : List (PTS (S := S))) :=
  match Γ with
  | .cons x xs => (shift' x 1 xs.length) :: (ctx_shift xs)
  | [] => []

@[simp]
theorem ctx_shift_length {S : Type} : ∀(Δ : List (PTS (S := S))), (ctx_shift Δ).length = Δ.length := by
  intro Δ;
  induction Δ <;> simp_all!;

@[simp]
theorem ctx_shift_get {S : Type} (Δ : List (PTS (S := S))) {i} (p2 : i < Δ.length) : (ctx_shift Δ)[i]'(by rw[←ctx_shift_length] at p2; simp_all!;) = shift' (Δ[i]'p2) 1 (Δ.length - i - 1) := by
  induction Δ generalizing i <;> cases i <;> simp_all!;
  grind;
  grind;

  simp! at p2;
  expose_names;
  exact tail_ih p2;

def wf_ctx (𝕊 𝔸 ℝ «≅») (Γ : List (PTS (S := 𝕊))) :=
  match Γ with
  | .cons x xs => (∃T, PTSHasType 𝕊 𝔸 ℝ «≅» xs x T) ∧ wf_ctx 𝕊 𝔸 ℝ «≅» xs
  | [] => True

theorem PTSHasType.ctx_lu {𝕊 𝔸 ℝ «≅»} (Γ i) (p0 : wf_ctx 𝕊 𝔸 ℝ «≅» Γ) (p1 : i < Γ.length) : PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.ref i) (shift' Γ[i] (i + 1) 0) := by
  induction i generalizing Γ;

  cases Γ <;> simp_all!;
  grind;
  rcases p0.left;
  rename_i h;
  apply PTSHasType.st h;

  cases Γ <;> try simp_all!;
  grind;
  expose_names;
  simp at p1;
  have := h tail (by grind;) p1;
  rcases p0.left;
  rename_i h2;
  have := PTSHasType.wk this h2;
  simp_all!;

theorem PTSHasType.weak {𝕊 𝔸 ℝ «≅»} {Γ Γl Γr T s b B}
    (h : PTSHasType 𝕊 𝔸 ℝ «≅» Γ b B) (p1 : Γ = Γl ++ Γr)
    (hT : PTSHasType 𝕊 𝔸 ℝ «≅» Γr T s)
    (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
    : PTSHasType 𝕊 𝔸 ℝ «≅» (ctx_shift Γl ++ T :: Γr)
      (shift' b 1 Γl.length) (shift' B 1 Γl.length) := by
  induction h generalizing Γl Γr T s <;> simp_all!;

  apply PTSHasType.ax; assumption;

  expose_names;
  induction Γl <;> simp_all!;

  have h1 : shift' (S := 𝕊) (.ref 0) 1 0 = .ref 1 := by simp!;
  have h2 : shift' (shift' A 1 0) 1 0 = shift' A 2 0 := by simp!;

  rw [←h1, ←h2];
  apply PTSHasType.wk;
  rw [←p1]
  apply PTSHasType.st;
  assumption;
  assumption;

  expose_names;
  have := shift_shift_comm head 0 1 1 (tail.length + 1) (by grind;)
  simp_all!;
  apply PTSHasType.st;
  apply p1_ih;
  grind;
  assumption;



  induction Γl;
  apply PTSHasType.wk;
  simp_all!;
  rw [←p1];
  apply PTSHasType.wk;
  assumption;
  assumption;
  assumption;

  expose_names;
  have h1 := shift_shift_comm A 0 1 1 (tail.length + 1) (by omega;)
  have h2 := shift_shift_comm B_1 0 1 1 (tail.length + 1) (by omega;)
  simp_all!;

  apply PTSHasType.wk;
  apply p1_ih;
  grind;
  assumption;
  apply p2_ih;
  grind;
  assumption;






  expose_names;
  apply PTSHasType.pi;
  have := p1_ih (Γl := Γl) (Γr := Γr) (by grind;) hT;
  assumption;

  have := p2_ih (Γl := A :: Γl) (Γr := Γr) (by grind;) hT;
  simp_all!;
  assumption;
  assumption;


  expose_names;
  have := shift_after_subst B_1 a 1 0 Γl.length (by grind;)
  simp_all!;
  apply PTSHasType.app;

  apply p1_ih;
  grind;
  assumption;
  apply p2_ih;
  grind;
  assumption;



  expose_names;
  apply PTSHasType.lam;

  apply p1_ih (Γl := A :: Γl)
  grind;
  assumption;
  apply p2_ih;
  grind;
  assumption;


  expose_names;
  apply PTSHasType.conv;
  apply p1_ih;
  grind;
  assumption;
  apply pc; assumption;

  apply p3_ih;
  grind;
  assumption;

theorem PTSHasType.subst_gen {𝕊 𝔸 ℝ «≅»} {Γ A a}
    (ha : PTSHasType 𝕊 𝔸 ℝ «≅» Γ a A)
    (pc1 : ∀p, «≅» p p)
    (pc2 : ∀a b x y k, «≅» a b → «≅» x y → «≅» (subst' a x k) (subst' b y k))
    :
    ∀ {Γ' B b}, PTSHasType 𝕊 𝔸 ℝ «≅» Γ' b B →
    (∀ Δ, Γ' = Δ ++ A :: Γ →
      PTSHasType 𝕊 𝔸 ℝ «≅» (ctx_subst Δ a ++ Γ)
        (subst' b a Δ.length)
        (subst' B a Δ.length)) := by

  intro Γ' B b hb
  induction hb generalizing a A Γ <;> intro Δ Δh <;> simp_all!;

  apply PTSHasType.ax; assumption;

  cases Δ;
  simp!; simp at Δh;
  grind;

  simp!;
  expose_names;

  have h1 : A_1 = head := (by grind;)
  have h2 : Γ_1 = (tail ++ A :: Γ) := (by grind;)

  have h3 := p1_ih ha tail h2;
  have h4 := shift_subst_comm head a tail.length 1 0
    (by omega;);

  apply PTSHasType.conv;
  apply PTSHasType.st;
  rwa [h1] at h3;

  simp! [h1];
  simp_all!;

  rw [h1, ←h4]
  apply PTSHasType.wk;
  rwa [←h1];

  rwa [←h1]




  cases Δ <;> simp_all!;
  expose_names;
  have h1 := shift_subst_comm A_1 a tail.length 1 0
    (by omega)
  have h2 := shift_subst_comm B_1 a tail.length 1 0
    (by omega)

  rw [←h1, ←h2]
  apply PTSHasType.wk;
  apply p1_ih;
  assumption;
  grind;
  apply p2_ih;
  assumption;
  grind;



  expose_names;
  have := p1_ih ha Δ (by grind;);
  apply PTSHasType.pi;
  assumption;

  have := p2_ih ha (A_1 :: Δ) (by grind;);
  simp_all!;
  assumption;

  assumption;



  expose_names;
  have h1 := subst_subst B_1 a a_1 Δ.length 0
  simp_all!;
  rw [←h1]
  apply PTSHasType.app;

  apply p1_ih;
  assumption;
  grind;

  apply p2_ih;
  assumption;
  grind;




  expose_names;
  apply PTSHasType.lam;

  have := p1_ih ha (A_1 :: Δ) (by grind;)
  simp_all!;

  have := p2_ih ha Δ (by grind;)
  assumption;





  expose_names;
  apply PTSHasType.conv;

  have := p1_ih ha Δ (by grind;);
  assumption;

  apply pc2;
  assumption;
  apply pc1;

  apply p3_ih;
  assumption;
  grind;

theorem PTSHasType.app_gen {𝕊 𝔸 ℝ «≅»} {Γ M N T B}
    (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
    (pc1 : ∀p, «≅» p p)
    (pc3 : ∀a b, «≅» a b → «≅» b a)
    (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)
    (h : PTSHasType 𝕊 𝔸 ℝ «≅» Γ T B) (p1 : T = (.app M N)) :
    ∃ A₀ B₀, PTSHasType 𝕊 𝔸 ℝ «≅» Γ M (.pi A₀ B₀) ∧
             PTSHasType 𝕊 𝔸 ℝ «≅» Γ N A₀ ∧
             «≅» B (subst B₀ N) := by
    induction h generalizing M N;
    grind; grind;

    expose_names;
    cases A <;> simp_all!;
    expose_names;

    obtain ⟨Da, Db, Dh⟩ := p1_ih;
    exists shift' Da 1 0, shift' Db 1 1;

    apply And.intro;
    rw [←p1.left]
    apply PTSHasType.wk Dh.left p2

    apply And.intro;
    rw [←p1.right]
    apply PTSHasType.wk;
    grind;

    assumption;
    rw [←p1.right]

    have := shift_subst Db b 1 0;
    rw [←this]

    apply pc;
    grind;

    grind;


    expose_names;
    exists A, B_1;
    simp_all!;

    grind;


    expose_names;
    cases p1; simp!;
    obtain ⟨Da, Db, Dh⟩ := p1_ih (by rfl);
    exists Da, Db;

    and_intros <;> (try simp_all!);

    apply pc4;
    apply pc3;
    assumption;
    grind;

theorem PTSHasType.pi_gen {𝕊 𝔸 ℝ «≅»} {Γ V A B T}
  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc1 : ∀p, «≅» p p)
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)

  (h : PTSHasType 𝕊 𝔸 ℝ «≅» Γ V T) (p1 : V = (.pi A B)) :
  ∃ s1 s2 s3, PTSHasType 𝕊 𝔸 ℝ «≅» Γ A (.sort s1) ∧
              PTSHasType 𝕊 𝔸 ℝ «≅» (A :: Γ) B (.sort s2) ∧
              ℝ (s1, s2, s3) ∧ «≅» T (.sort s3) := by
  induction h generalizing A B;
  grind; grind;

  expose_names;
  cases A_1 <;> simp_all!;

  expose_names;
  obtain ⟨hA, hB⟩ := p1
  subst hA; subst hB
  obtain ⟨s1, hT1, s2, hT2, s3, hR, hBeq⟩ := p1_ih

  have hA' := PTSHasType.weak hT1 (Γl := [])
      (T := C) (s := s) rfl p2 pc

  have hB' := PTSHasType.weak hT2 (Γl := [T_1])
      (T := C) (s := s) rfl p2 pc

  exact ⟨s1, hA', s2, hB', s3, hR, pc B_1 (.sort s3) 1 0 hBeq⟩

  expose_names;
  exists s1, s2, s3;
  and_intros <;> simp_all!;

  grind;
  grind;

  simp_all!;
  expose_names;

  obtain ⟨s1, hA, s2, hB, s3, hS, hE⟩ := p1_ih;

  exists s1;
  and_intros;
  assumption;
  exists s2;
  and_intros;
  assumption;

  exists s3;
  and_intros;
  assumption;

  apply pc4;
  apply pc3;
  assumption;
  assumption;

theorem PTSHasType.lam_gen {𝕊 𝔸 ℝ «≅»} {Γ V T b B}
  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc1 : ∀p, «≅» p p)
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)

  (h : PTSHasType 𝕊 𝔸 ℝ «≅» Γ V B) (p1 : V = (.lam T b)) :
  ∃ B₀ s, PTSHasType 𝕊 𝔸 ℝ «≅» (T :: Γ) b B₀ ∧
          PTSHasType 𝕊 𝔸 ℝ «≅» Γ (.pi T B₀) (.sort s) ∧
          «≅» B (.pi T B₀) := by
  induction h generalizing T b <;> simp_all!

  -- wk
  expose_names;
  · cases A <;> simp_all!
    expose_names
    obtain ⟨hT, hb⟩ := p1
    subst hT; subst hb
    obtain ⟨B₀, hb', ⟨s₀, hpi'⟩, heq⟩ := p1_ih

    refine ⟨shift' B₀ 1 1, ?_, ⟨s₀, ?_⟩, ?_⟩
    · exact PTSHasType.weak hb' (Γl := [T_1]) (Γr := Γ_1) rfl p2 pc
    · exact PTSHasType.weak hpi' (Γl := []) (Γr := Γ_1) rfl p2 pc
    · exact pc B_1 (.pi T_1 B₀) 1 0 heq

  -- abs'
  expose_names;
  exists B_1;
  and_intros;
  assumption;
  · exact ⟨s, by assumption⟩

  grind;
  -- conv
  expose_names;
  · obtain ⟨B₀, hb', ⟨s₀, hpi'⟩, heq⟩ := p1_ih
    exact ⟨B₀, hb', ⟨s₀, hpi'⟩,
      pc4 _ _ _ (pc3 _ _ ‹_›) heq⟩

theorem PTSHasType.type_correctness {𝕊 𝔸 ℝ «≅»} {Γ A T}
  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc1 : ∀p, «≅» p p)
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)
  (pc2 : ∀a b x y k, «≅» a b → «≅» x y → «≅» (subst' a x k) (subst' b y k))

  (p1 : wf_ctx 𝕊 𝔸 ℝ «≅» Γ)
  (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A T)
  : (∃s, T = .sort s) ∨ (∃S, PTSHasType 𝕊 𝔸 ℝ «≅» Γ T S) := by
  induction p2;
  expose_names;
  grind;

  simp_all!;
  rename_i h;
  apply Or.inr;
  expose_names;
  exists (shift' s 1 0);
  apply PTSHasType.wk <;> assumption;

  expose_names;
  simp_all!;
  rcases p1_ih;
  rename_i h;
  apply Or.inl;
  apply h.elim; intros;
  simp_all!;

  rename_i h;
  apply Or.inr;
  obtain ⟨T, Th⟩ := h;
  exists (shift' T 1 0);
  apply PTSHasType.wk <;> assumption;

  grind;
  case lam;
  grind;
  case conv;
  grind;


  expose_names;
  simp_all!;
  apply p1_ih.elim;
  intros;
  rename_i a1;
  obtain ⟨s1, s2, s3, sh⟩ := PTSHasType.pi_gen pc pc1 pc3 pc4 a1 rfl;

  have := PTSHasType.subst_gen p2 pc1
    (by
      intros;
      apply pc2 <;> assumption;)
    sh.right.left
    []
    (by grind;)

  simp_all!;
  apply Or.inr;
  exists .sort s2;

theorem PTSHasType.ctx_conv {𝕊 𝔸 ℝ «≅»}
    (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
    (pc3 : ∀a b, «≅» a b → «≅» b a)

    (Δ : List (PTS (S := 𝕊))) {Γ Γ' A A' M B s s'}
    (hA  : PTSHasType 𝕊 𝔸 ℝ «≅» Γ' A (.sort s))
    (hA' : PTSHasType 𝕊 𝔸 ℝ «≅» Γ' A' (.sort s'))
    (heq : «≅» A A')
    (hM  : PTSHasType 𝕊 𝔸 ℝ «≅» Γ M B) (p1 : Γ = Δ ++ A :: Γ') :
    PTSHasType 𝕊 𝔸 ℝ «≅» (Δ ++ A' :: Γ') M B := by
  -- induction on hM, generalising Δ
  induction hM generalizing Δ

  apply PTSHasType.ax; assumption;

  induction Δ;
  simp!;
  apply PTSHasType.conv;
  apply PTSHasType.st;
  assumption;
  apply pc;
  grind [βeq.symm];

  apply PTSHasType.wk;
  simp at p1;
  rwa [p1.left];
  assumption;

  simp_all!;
  apply PTSHasType.st;
  assumption;

  induction Δ;
  simp!;
  apply PTSHasType.wk;
  simp at p1;
  rwa [←p1.right]
  assumption;


  simp_all!;
  apply  PTSHasType.wk;
  assumption;
  assumption;


  expose_names;
  apply PTSHasType.pi;
  apply p1_ih;
  grind;
  apply p2_ih (A_1 :: Δ)
  grind;
  assumption;


  expose_names;
  simp_all!;
  apply PTSHasType.app;
  assumption;
  assumption;


  expose_names;
  simp_all!;
  apply PTSHasType.lam;
  apply p1_ih (A_1 :: Δ);
  grind;
  apply p2_ih



  simp_all!;
  apply PTSHasType.conv;
  assumption;
  assumption;
  assumption;

theorem PTSHasType.sort_type {𝕊 𝔸 ℝ «≅»} {Γ s' s T}
  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc1 : ∀p, «≅» p p)
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)

    (h : PTSHasType 𝕊 𝔸 ℝ «≅» Γ s T) (p1 : s = (.sort s')) :
    ∃ S, «≅» T (.sort S) ∧ 𝔸 (s', S) := by
  induction h generalizing s'
  simp_all!;
  expose_names;
  exists s2;
  simp_all!;

  grind;

  expose_names;
  cases A <;> simp_all!;

  obtain ⟨S, Sh⟩ := p1_ih;
  exists S;
  simp_all!;
  have : shift' (.sort S) 1 0 = .sort S := by simp!;
  rw [←this];
  apply pc;
  grind;

  grind;
  grind;
  grind;

  expose_names;
  cases A <;> simp_all!;
  obtain ⟨S, Sh⟩ := p1_ih;
  exists S;
  simp_all;
  apply pc4;
  apply pc3;
  assumption;
  grind;

theorem PTSHasType.subject_reduction_step {𝕊 𝔸 ℝ «≅» Γ A B A'}
  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pch : ∀a b, ιstep a b → «≅» a b)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)
  (pc2 : ∀a b x y k, «≅» a b → «≅» x y → «≅» (subst' a x k) (subst' b y k))
  (pch2 : ∀{A B A' B'}, «≅» (A.pi B) (A'.pi B') → «≅» A A' ∧ «≅» B B')

  (p1 : wf_ctx 𝕊 𝔸 ℝ «≅» Γ)
  (ht : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A B)
  (hs : ιstep A A')
  : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A' B := by
  induction ht generalizing A';

  cases hs;
  apply PTSHasType.ax; assumption;

  cases hs;
  apply PTSHasType.st <;> assumption;

  expose_names;
  obtain ⟨Q, Qh⟩ := shift_ιstep hs;
  rw [←Qh];
  apply PTSHasType.wk;
  rw [←Qh] at hs;
  have := ιstep_shift_inv hs;
  have := p1_ih (by simp_all!;) this;
  assumption;

  assumption;

  cases hs;
  apply PTSHasType.pi <;> assumption;

  simp_all!;

  expose_names;
  have := p1_ih p1_1;
  have := p1_ih (ιstep.refl)
  have := p2_ih (.sort s1) this p2_1;

  apply PTSHasType.pi;
  assumption;

  apply PTSHasType.ctx_conv pc pc3 [];
  assumption;
  assumption;
  apply pch;
  assumption;
  assumption;
  grind;
  assumption;



  cases hs;
  apply PTSHasType.app;
  assumption;
  assumption;

  expose_names;
  simp_all!;
  have h1 := p1_ih p2_1;
  have h2 := p2_ih p1_2;

  have := PTSHasType.app h1 h2;


  have h3 := p1_ih ιstep.refl;
  have h4 := p2_ih ιstep.refl;
  have h5 := PTSHasType.app h3 h4;

  have h6 := PTSHasType.type_correctness pc
    (by
      intros;
      apply pch;
      simp!;) pc3 pc4 pc2 p1 h5;
  have h7 := PTSHasType.type_correctness pc
    (by
      intros;
      apply pch;
      simp!;) pc3 pc4 pc2 p1 h1;
  simp at h7;
  obtain ⟨S', S'h⟩ := h7;
  obtain ⟨s1, s2, s3, sh⟩ := PTSHasType.pi_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 S'h rfl;

  apply PTSHasType.conv;
  assumption;
  apply pc2;
  apply pch;
  simp!; apply pc3;
  apply pch;
  assumption;

  apply PTSHasType.subst_gen h4 (by
      intros;
      apply pch;
      simp!;)
    (by
      intros;
      apply pc2 <;> assumption;)
    (Δ := [])

  exact sh.right.left;
  grind;

  expose_names;
  simp_all!;
  have h1 := p2_ih p3;
  have h2 := p1_ih (ιstep.lam (ιstep.refl) p2_1)
  obtain ⟨S, s, Sh⟩ := PTSHasType.lam_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 h2 rfl;

  have := pch2 Sh.right.right;
  obtain ⟨s1, s2, s3, sh⟩ := PTSHasType.pi_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 Sh.right.left rfl;
  have h1 := PTSHasType.conv h1 this.left sh.left;

  have := p2_ih ιstep.refl;
  have := type_correctness pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 pc2 p1 h2;
  simp_all!;

  obtain ⟨z, zh⟩ := this;
  obtain ⟨z1, z2, z3, zh⟩ := PTSHasType.pi_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 zh rfl;

  have := p2_ih ιstep.refl;

  have qq := PTSHasType.subst_gen this (by
      intros;
      apply pch;
      simp!;)
    (by
      intros;
      apply pc2 <;> assumption;) zh.right.left
    [] (by grind)

  have := PTSHasType.subst_gen h1 (by
      intros;
      apply pch;
      simp!;)
    (by
      intros;
      apply pc2 <;> assumption;) Sh.left
    [] (by grind)

  simp_all!;
  apply PTSHasType.conv this (by
    apply pc2;
    apply pc3;
    grind;
    apply pc3;
    apply pch
    assumption;) qq;



  cases hs;
  apply PTSHasType.lam;
  assumption;
  assumption;


  expose_names;
  simp_all!;
  have := p2_ih (ιstep.pi p1_2 ιstep.refl)
  obtain ⟨z1, z2, z3, zh⟩ := PTSHasType.pi_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 this rfl;
  have := p2_ih ιstep.refl
  obtain ⟨s1, s2, s3, sh⟩ := PTSHasType.pi_gen pc (by
      intros;
      apply pch;
      simp!;) pc3 pc4 this rfl;

  have := p1_ih (.sort s1) (by grind;) p2_1;

    -- 1. Move P' from A₁ :: Γ₁ to T' :: Γ₁
  have hP'_T' : PTSHasType 𝕊 𝔸 ℝ «≅» (T' :: Γ_1) P' B_1 :=
    (by
      apply PTSHasType.ctx_conv pc pc3 [] (Γ' := Γ_1) (A := A_1) (A' := T')
      exact sh.left;
      exact zh.left;
      apply pch;
      assumption;
      assumption;
      grind;)

  apply PTSHasType.conv;
  apply PTSHasType.lam;
  assumption;
  assumption;
  apply pc3;
  apply pch;
  apply ιstep.pi;
  assumption;
  simp!;

  assumption;




   simp_all!;
   expose_names;
   have := p1_ih hs;
   apply PTSHasType.conv;
   assumption;
   assumption;
   apply p3_ih;
   simp!;

theorem PTSHasType.subject_reduction {𝕊 𝔸 ℝ «≅» Γ A B A'}
  (pc3 : ∀a b, «≅» a b → «≅» b a)
  (pc4 : ∀a b c, «≅» a b → «≅» b c → «≅» a c)

  (pc : ∀a b n k, «≅» a b → «≅» (shift' a n k) (shift' b n k))
  (pc2 : ∀a b x y k, «≅» a b → «≅» x y → «≅» (subst' a x k) (subst' b y k))

  (pch : ∀a b, ιstep a b → «≅» a b)
  (pch2 : ∀{A B A' B'}, «≅» (A.pi B) (A'.pi B') → «≅» A A' ∧ «≅» B B')

  (p1 : wf_ctx 𝕊 𝔸 ℝ «≅» Γ)
  (ht : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A B)
  (hs : βmstep A A')
  : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A' B := by
  rw [←TransGenιstep_iff_βmstep] at hs;
  induction hs <;> apply PTSHasType.subject_reduction_step <;> assumption;

theorem PTSHasType.sub_eq {𝕊 𝔸 ℝ «≅» Γ A T}
  (p1 : ∀a b, «≅» a b → a = b)
  (p2 : PTSHasType 𝕊 𝔸 ℝ «≅» Γ A T) :
  PTSHasType 𝕊 𝔸 ℝ (· = ·) Γ A T := by
  induction p2;

  apply PTSHasType.ax; assumption;
  apply PTSHasType.st <;> assumption;
  apply PTSHasType.wk <;> assumption;
  apply PTSHasType.pi <;> assumption;
  apply PTSHasType.app <;> assumption;
  apply PTSHasType.lam <;> assumption;
  apply PTSHasType.conv;
  assumption;
  grind;
  assumption;

def map_sort {𝕊₁ 𝕊₂} (F : 𝕊₁ → 𝕊₂) (T : PTS (S := 𝕊₁)) : PTS (S := 𝕊₂) :=
  match T with
  | .sort s => .sort (F s)
  | .ref n => .ref n
  | .app a b => .app (map_sort F a) (map_sort F b)
  | .pi t p => .pi (map_sort F t) (map_sort F p)
  | .lam t p => .lam (map_sort F t) (map_sort F p)

@[simp]
theorem map_sort_shift {𝕊₁ 𝕊₂ F A n k} :  map_sort F (shift' A n k) = shift' (map_sort (𝕊₁ := 𝕊₁) (𝕊₂ := 𝕊₂) F A) n k := by
  induction A generalizing n k <;> simp_all!;
  split <;> simp_all!;

@[simp]
theorem map_sort_subst {𝕊₁ 𝕊₂ F A B k} :
  map_sort F (subst' A B k) = subst' (map_sort (𝕊₁ := 𝕊₁) (𝕊₂ := 𝕊₂) F A) (map_sort F B) k := by
  induction A generalizing B k <;> simp_all!;
  split_ifs <;> simp_all!;

theorem map_sort_id {𝕊} {A : PTS (S := 𝕊)} : map_sort id A = A := by
  induction A <;> simp_all!

theorem map_sort_comp {𝕊₁ 𝕊₂ 𝕊₃} {F : 𝕊₂ → 𝕊₃} {G : 𝕊₁ → 𝕊₂} {A : PTS (S := 𝕊₁)} :
    map_sort F (map_sort G A) = map_sort (F ∘ G) A := by
  induction A <;> simp_all!

theorem PTSHasType.map_sort {𝕊₁ 𝔸₁ ℝ₁ «≅₁»} {𝕊₂ 𝔸₂ ℝ₂ «≅₂»} {Γ A T} {F : 𝕊₁ → 𝕊₂}
  (p1 : PTSHasType 𝕊₁ 𝔸₁ ℝ₁ «≅₁» Γ A T)
  (p2 : ∀a b, 𝔸₁ (a, b) → 𝔸₂ (F a, F b))
  (p3 : ∀a b c, ℝ₁ (a, b, c) → ℝ₂ (F a, F b, F c))
  (p4 : ∀a b, «≅₁» a b → «≅₂» (map_sort F a) (map_sort F b)) :
  PTSHasType 𝕊₂ 𝔸₂ ℝ₂ «≅₂» (Γ.map (map_sort F)) (map_sort F A) (map_sort F T) := by
  induction p1 <;> try simp_all!;

  apply PTSHasType.ax; grind;
  apply PTSHasType.st <;> assumption;
  apply PTSHasType.wk <;> assumption;

  apply PTSHasType.pi;
  assumption;
  assumption;
  grind;

  apply PTSHasType.app <;> assumption;
  apply PTSHasType.lam <;> assumption;
  apply PTSHasType.conv;
  assumption;
  grind;
  assumption;
