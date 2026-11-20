import Mathlib.Data.Finset.Basic
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec

namespace DeBruijn
-- debruijn
inductive DB where
  | ref : Nat → DB
  | app : DB → DB → DB
  | lam : DB → DB
deriving DecidableEq

def shift' (M : DB) (n : Nat) (k : Nat) : DB :=
  match M with
  | .ref a => if a ≥ k then .ref (a + n) else .ref a
  | .app a b => .app (shift' a n k) (shift' b n k)
  | .lam p => .lam (shift' p n (k + 1))

@[simp]
def shift (M : DB) (n : Nat) := shift' M n 0

def subst' (M N : DB) (k : Nat) : DB :=
  match M with
  | .ref a =>
    if a = k then shift N k
    else if a > k then .ref (a-1)
    else .ref a
  | .app a b => .app (subst' a N k) (subst' b N k)
  | .lam p => .lam (subst' p N (k + 1))

@[simp]
def subst := (subst' · · 0)

inductive βmstep : DB → DB → Prop where
  | refl (a : DB) : βmstep a a
  | trans {a b c : DB} (h : βmstep a b) (h1 : βmstep b c) : βmstep a c
  | redex {M N : DB} : βmstep (.app (.lam M) N) (subst M N)
  | app {M M' N N'} (h : βmstep M M') (h : βmstep N N') : βmstep (.app M N) (.app M' N')
  | lam {M M'} (h : βmstep M M') : βmstep (.lam M) (.lam M')

@[simp]
theorem βmstep_refl {t : DB} : βmstep t t := by apply βmstep.refl;

instance : IsTrans DB βmstep where
  trans (a b c) := βmstep.trans (a := a) (b := b) (c := c);



@[simp]
theorem shift_zero (M : DB) : ∀k, shift' M 0 k = M := by
  induction M <;> simp! <;> grind;

@[simp]
theorem shift_shift (M : DB) : ∀a b c c', c ≤ c' → c' ≤ c + a → shift' (shift' M a c) b c' = shift' M (a + b) c := by
  induction M <;> intros <;> simp! <;> grind [shift'];

@[simp]
theorem subst_shift (M N : DB) (k : Nat) : ∀c' c, c' ≤ c → c < c' + k → subst' (shift' M k c') N c = shift' M (k - 1) c' := by
  induction M <;> simp_all! <;> grind [subst'];

@[simp]
theorem shift_subst (M N : DB) : ∀k n, shift' (subst' M N k) n k = subst' (shift' M n (k+1)) (shift' N n 0) k := by
  induction M <;> intros <;> simp_all!;
  (repeat' split; (try simp_all!;)) <;> (try simp!;) <;> grind;

theorem shift_shift_comm (N : DB) (m k v c : Nat) (h : c ≥ k) :
    shift' (shift' N k m) v (c + m) =
    shift' (shift' N v (c - k + m)) k m := by
  induction N generalizing m k c <;> simp_all!;
  (repeat' split <;> (try simp!;)) <;> omega;
  grind only;

theorem shift_after_subst (M N : DB) (v k c : Nat) (h : c ≥ k) :
    shift' (subst' M N k) v c =
    subst' (shift' M v (c + 1)) (shift' N v (c - k)) k := by
  induction M generalizing k c <;> simp_all!;
  (repeat' split <;> (try simp!)) <;> (try omega);
  apply shift_shift_comm;
  omega;

theorem shift_subst_comm (T S : DB) (c d m : Nat) (hm : m ≤ c) :
    shift' (subst' T S c) d m
  = subst' (shift' T d m) S (c + d) := by
  induction T generalizing c d m <;> simp_all!;
  (repeat' split <;> (try simp_all!)) <;> omega;
  grind;

theorem subst_subst (M S T : DB) (c d : Nat) :
    subst' (subst' M S (c + d + 1)) (subst' T S c) d
  = subst' (subst' M T d) S (c + d) := by
  induction M generalizing c d <;> simp_all!;
  (repeat' split <;> (try simp_all!)) <;> (try omega)
  grind only [shift_subst_comm];
  expose_names;
  exact a_ih (c := c) (d := d + 1)

-- diamond property
@[simp]
def DP {Λ} (r : Λ → Λ → Prop) : Prop :=
  ∀A B C, r A B ∧ r A C → Relation.Join r B C

theorem cr_strip
    {Λ}
    {r : Λ → Λ → Prop}
    (p1 : DP r)
  : ∀M M' N, r M M' → Relation.TransGen r M N → ∃N', Relation.TransGen r M' N' ∧ r N N' := by
  simp_all;
  intros;
  rename_i h1 h2;
  induction h2;

  rename_i h3;
  obtain ⟨w, _⟩ := p1 _ _ _ h1 h3;
  grind;

  rename_i h3;
  obtain ⟨_, h4⟩ := h3;

  obtain ⟨w, _⟩ := p1 _ _ _ (by assumption) h4.2
  grind;

theorem cr_dia
    {Λ}
    {r : Λ → Λ → Prop}
    (p1 : DP r)
  : DP (Relation.TransGen r) := by
  simp!; intros _ _ _ h1 h2;
  induction h1;

  rename_i h3;
  obtain ⟨a, _⟩ := cr_strip p1 _ _ _ h3 h2
  exists a;
  grind;

  simp_all;
  rename_i h5 h3;
  obtain ⟨_, h4⟩ := h3;
  obtain ⟨a_1, _⟩ := cr_strip (by simp!; exact p1) _ _ _ h5 h4.1;
  exists a_1;
  grind;

inductive ιstep : DB → DB → Prop where
| refl (P : DB) : ιstep P P
| lam {P Q : DB} (p1 : ιstep P Q) : ιstep (.lam P) (.lam Q)
| app {P P' Q Q' : DB} (p2 : ιstep P P') (p1 : ιstep Q Q') : ιstep (.app P Q) (.app P' Q')
| redex {P P' Q Q' : DB} (p2 : ιstep P P') (p1 : ιstep Q Q') : ιstep (.app (.lam P) Q) (subst P' Q')

@[simp]
theorem ιstep_refl {p : DB} : ιstep p p := by apply ιstep.refl;

theorem ιstep_shift : ∀N N' v c, ιstep N N' → ιstep (shift' N v c) (shift' N' v c) := by
  intro N N' v c p1;
  induction p1 generalizing c;
  apply ιstep.refl;
  apply ιstep.lam; grind only;
  apply ιstep.app <;> grind only;

  expose_names;
  have := ιstep.redex (p2_ih (c+1)) (p1_ih c)
  have := shift_after_subst P' Q' v 0 c (by omega;)
  simp_all!;

theorem ιstep_subst { M M' N N' c } (p1 : ιstep M M') (p2 : ιstep N N') : ιstep (subst' M N c) (subst' M' N' c) := by
  induction p1 generalizing c;
  expose_names;

  induction P generalizing c <;> simp!;
  split; apply ιstep_shift; grind;
  apply ιstep.refl;
  apply ιstep.app <;> grind;
  apply ιstep.lam; grind;
  apply ιstep.lam; grind;
  apply ιstep.app <;> grind;

  expose_names;
  simp!;
  have := subst_subst P' N' Q' c 0;
  have := ιstep.redex (p2_ih (c := c + 1)) (p1_ih (c := c))
  simp_all;

theorem cr_l4 : DP ιstep := by
  rw [DP]; intros _ _ C h;
  induction h.left generalizing C;

  exists C; grind [ιstep.refl];

  ·
    expose_names;
    simp_all;
    cases h.right;
    obtain ⟨D, hD⟩ := p1_ih P (by grind [ιstep.refl])
    exists D.lam;
    grind [ιstep.lam];

    expose_names;
    obtain ⟨D, hD⟩ := p1_ih Q_1 (by grind;);
    exists D.lam;
    grind [ιstep.lam];


  ·
    expose_names;
    cases h.right;
    obtain ⟨D1, hD1⟩ := p2_ih P (by simpa);
    obtain ⟨D2, hD2⟩ := p1_ih Q (by simpa);
    exists (.app D1 D2)
    grind [ιstep.app];

    expose_names;
    obtain ⟨D1, hD1⟩ := p2_ih P'_1 (by grind;);
    obtain ⟨D2, hD2⟩ := p1_ih Q'_1 (by grind [ιstep.refl]);
    exists .app D1 D2
    grind [ιstep.app];

    expose_names;
    obtain ⟨D1, hD1⟩ := p2_ih P'_1.lam (by grind [ιstep.lam];)
    obtain ⟨D2, hD2⟩ := p1_ih Q'_1 (by grind;)

    cases hD1.2;
    have := ιstep_subst (ιstep.refl P'_1) hD2.2 (c := 0);
    have := ιstep.redex p2_1 hD2.1

    exists subst P'_1 D2;
    cases p2 <;> simp_all;
    apply ιstep.redex;

    cases hD1 <;> simp_all!;
    grind;

    expose_names;
    exists subst Q_1 D2;
    have := ιstep_subst p1_2 hD2.right (c := 0);
    simp_all;

    cases p2 with
    | refl =>
      cases hD1.left with
      | refl => exact ιstep.redex ιstep_refl hD2.left
      | lam h => exact ιstep.redex h hD2.left
    | lam hP =>
      expose_names;
      cases hD1.left with
      | refl => exact ιstep.redex ιstep_refl hD2.left
      | lam h => exact ιstep.redex h hD2.left




  ·
    expose_names;
    cases h.right
    exact ⟨subst P' Q', ιstep.refl _, h.left⟩

    case app p2 p1 =>
        cases p2 with
        | refl =>
            -- C1 = P✝.lam
            expose_names;
            obtain ⟨D2, hQ'D2, hC2D2⟩ := p1_ih Q'_1 ⟨p1_1, p1⟩
            exact ⟨subst P' D2,
              ιstep_subst (ιstep.refl P') hQ'D2 (c := 0),
              ιstep.redex p2 hC2D2⟩
        | lam hP =>
            -- C1 = .lam P0, hP : ιstep P✝ P0
            expose_names;
            obtain ⟨D1, hP'D1, hP0D1⟩ := p2_ih Q_1 ⟨p2, hP⟩
            obtain ⟨D2, hQ'D2, hC2D2⟩ := p1_ih Q'_1 ⟨p1_1, p1⟩
            exact ⟨subst D1 D2,
              ιstep_subst hP'D1 hQ'D2 (c := 0),
              ιstep.redex hP0D1 hC2D2⟩

    case redex p2 p1 =>
      expose_names;
      obtain ⟨D1, hP'D1, hP''D1⟩ := p2_ih P'_1 ⟨p2_1, p2⟩
      obtain ⟨D2, hQ'D2, hQ''D2⟩ := p1_ih Q'_1 ⟨p1_1, p1⟩
      exact ⟨subst D1 D2,
        ιstep_subst hP'D1 hQ'D2 (c := 0),
        ιstep_subst hP''D1 hQ''D2 (c := 0)⟩

theorem βmstep_ιstep {A B} : ιstep A B → βmstep A B := by
  intro a1;
  induction a1;
  apply βmstep.refl;
  apply βmstep.lam; assumption;
  apply βmstep.app <;> assumption;

  apply βmstep.trans;
  apply βmstep.trans;
  apply βmstep.app;
  apply βmstep.lam;
  assumption;
  assumption;
  apply βmstep.redex;
  apply βmstep.refl;

inductive βstep : DB → DB → Prop where
  | redex {M N : DB} : βstep (.app (.lam M) N) (subst M N)
  | appL {M M' N} (h : βstep M M') : βstep (.app M N) (.app M' N)
  | appR {N N' M} (h : βstep N N') : βstep (.app M N) (.app M N')
  | lam {M M'} (h : βstep M M') : βstep (.lam M) (.lam M')

theorem βmstep_βstep {A B} : βstep A B → βmstep A B := by
  intro a1;
  induction a1;
  apply βmstep.redex;
  apply βmstep.app; assumption; simp!;
  apply βmstep.app; simp!; assumption;
  apply βmstep.lam; assumption;

theorem Relation.TransGen_sub {α} {r1 r2 : α → α → Prop} : (∀A B, r1 A B → r2 A B) →
  (∀A B, Relation.TransGen r1 A B → Relation.TransGen r2 A B) := by
  intros;
  expose_names;
  induction h_1;
  apply Relation.TransGen.single;
  grind;
  grind;

@[simp]
theorem ReflTransGenβstep_iff_βmstep {A B} : Relation.ReflTransGen βstep A B ↔ βmstep A B := by
  apply Iff.intro;
  intro a1;
  induction a1;

  apply βmstep.refl;
  apply βmstep.trans; assumption;
  apply βmstep_βstep; assumption;

  intro a1;
  induction a1;
  apply Relation.ReflTransGen.refl;



  apply Relation.ReflTransGen.trans <;> assumption;

  apply Relation.ReflTransGen.single;
  apply βstep.redex;

  have h1 : (∀ (M N N' : DB), Relation.ReflTransGen βstep N N' → Relation.ReflTransGen βstep (N.app M) (N'.app M)) :=
    (by
      intros;
      expose_names;
      induction h_2;
      apply Relation.ReflTransGen.refl;
      apply Relation.ReflTransGen.tail;
      assumption;
      apply βstep.appL; assumption;)

  have h2 : (∀ (M N N' : DB), Relation.ReflTransGen βstep N N' → Relation.ReflTransGen βstep (M.app N) (M.app N')) :=
    (by
      intros;
      expose_names;
      induction h_2;
      apply Relation.ReflTransGen.refl;
      apply Relation.ReflTransGen.tail;
      assumption;
      apply βstep.appR; assumption;)

  apply Relation.ReflTransGen.trans;
  apply h1;
  assumption;
  apply h2;
  assumption;

  have h1 : (∀ (N N' : DB), Relation.ReflTransGen βstep N N' → Relation.ReflTransGen βstep (.lam N) (.lam N')) :=
    (by
      intros;
      expose_names;
      induction h_1;
      apply Relation.ReflTransGen.refl;
      apply Relation.ReflTransGen.tail;
      assumption;
      apply βstep.lam; assumption;)

  apply h1; assumption;

@[simp]
theorem ιstep_ReflGenβstep {A B} : Relation.ReflGen βstep A B → ιstep A B := by
  intro a1;
  cases a1;
  apply ιstep.refl;
  rename_i a1;
  induction a1;
  apply ιstep.redex <;> apply ιstep.refl;
  apply ιstep.app; assumption; apply ιstep.refl;
  apply ιstep.app; apply ιstep.refl; assumption;
  apply ιstep.lam; assumption;

@[simp]
theorem TransGenιstep_iff_βmstep {A B} : Relation.TransGen ιstep A B ↔ βmstep A B := by
  apply Iff.intro;
  intro a1;
  apply Relation.transGen_minimal (r := βmstep) (r' := βmstep) (by grind;);
  apply Relation.TransGen_sub (by apply βmstep_ιstep);
  assumption;

  intro a1;
  rw [←ReflTransGenβstep_iff_βmstep] at a1;
  apply Relation.TransGen_sub;
  apply ιstep_ReflGenβstep;
  rwa [Relation.transGen_reflGen];

theorem church_rosser : DP βmstep := by
  simp!;
  intros;
  expose_names;
  suffices h1 : ∃D, Relation.TransGen ιstep B D ∧ Relation.TransGen ιstep C D from
    (by
      obtain ⟨D, Dh⟩ := h1;
      exists D;
      simp_all!;)

  apply cr_dia;
  apply cr_l4;
  simp_all!
  exact ⟨h, h_1⟩

theorem lam_βmstep {a b} (p1 : βmstep (.lam a) b) : ∃c, b = .lam c := by
    rw [←TransGenιstep_iff_βmstep] at p1;
    induction p1;
    expose_names;
    cases h;
    grind; grind;

    expose_names;
    obtain ⟨q, qh⟩ := a_ih;
    simp_all!;
    cases h_1;
    grind; grind;

theorem βmstep_strip_lam' {a b p q} (p1 : βmstep p q) (p2 : p = a.lam ∧ q = b.lam) : βmstep a b := by
  rw [←TransGenιstep_iff_βmstep] at p1;
  induction p1 generalizing a b;

  expose_names;
  rw [p2.1, p2.2] at h;
  cases h;
  apply βmstep.refl;
  apply βmstep_ιstep;
  assumption;

  expose_names;
  simp_all!;
  obtain ⟨c', c'h⟩ := lam_βmstep h;
  simp_all!;
  cases h_1;
  simp_all!;
  apply βmstep.trans a_ih;
  apply βmstep_ιstep;
  assumption;

theorem βmstep_strip_lam {a b} (p1 : βmstep a.lam b.lam) : βmstep a b := by
  apply βmstep_strip_lam' p1; grind;

theorem βmstep_ref' {p a b} (p1 : βmstep p b) (p2 : p = (.ref a)) : b = .ref a := by
  rw [←TransGenιstep_iff_βmstep] at p1;
  induction p1 generalizing a;
  simp_all!;
  expose_names;
  cases h;
  rfl;

  expose_names;
  simp_all!;
  cases h_1;
  rfl;

theorem βmstep_ref {a b} (p1 : βmstep (.ref a) b) : b = .ref a := by
  apply βmstep_ref' p1;
  rfl;




theorem βmstep_subst {M M' N N'} (k : Nat) (p1 : βmstep M M') (p2 : βmstep N N') : βmstep (subst' M N k) (subst' M' N' k) := by
  rw [←TransGenιstep_iff_βmstep] at p1;
  rw [←TransGenιstep_iff_βmstep] at p2;
  induction p1;
  induction p2;
  apply βmstep_ιstep;
  apply ιstep_subst <;> assumption;

  rw [←TransGenιstep_iff_βmstep];
  apply Relation.TransGen.tail;
  simp_all!;
  assumption;

  apply ιstep_subst;
  apply ιstep_refl;
  assumption;

  rw [←TransGenιstep_iff_βmstep];
  apply Relation.TransGen.tail;
  simp_all!;
  assumption;

  apply ιstep_subst;
  assumption;
  apply ιstep.refl;

def βeq := Relation.Join βmstep

theorem βeq_βmstep {a b} (p1 : βmstep a b) : βeq a b := by
  exists b;
  simp!;
  assumption;

theorem βeq.symm {a b} (p1 : βeq a b) : βeq b a := by
  simp_all! [βeq, Relation.Join];
  grind;

@[simp]
theorem βeq.refl (a) : βeq a a := by
  apply βeq_βmstep;
  apply βmstep.refl;

@[simp]
theorem βeq.trans {a b c} (p1 : βeq a b) (p2 : βeq b c) : βeq a c := by
  obtain ⟨Da, Dah⟩ := p1;
  obtain ⟨Db, Dbh⟩ := p2;
  obtain ⟨D, Dh⟩ := church_rosser b Da Db (by grind;)
  exists D;
  and_intros;
  apply βmstep.trans Dah.1 Dh.1;
  apply βmstep.trans Dbh.2 Dh.2;

instance : IsTrans DB βeq where
  trans (a b c) := βeq.trans (a := a) (b := b) (c := c);


inductive βηeq : DB → DB → Prop where
  | symm {a b : DB} (p1 : βηeq a b) : βηeq b a
  | refl (a : DB) : βηeq a a
  | trans {a b c : DB} (h : βηeq a b) (h1 : βηeq b c) : βηeq a c
  | redex {M N : DB} : βηeq (.app (.lam M) N) (subst M N)
  | app {M M' N N'} (h : βηeq M M') (h : βηeq N N') : βηeq (.app M N) (.app M' N')
  | lam {M M'} (h : βηeq M M') : βηeq (.lam M) (.lam M')
  | eta {M : DB} : βηeq (.lam (.app (shift M 1) (.ref 0))) M

instance : IsTrans DB βηeq where
  trans (a b c) := βηeq.trans (a := a) (b := b) (c := c);

theorem βηeq_βmstep {a b} (p1 : βmstep a b) : βηeq a b := by
  induction p1;
  apply βηeq.refl;
  apply βηeq.trans <;> assumption;
  apply βηeq.redex;
  apply βηeq.app <;> assumption;
  apply βηeq.lam; assumption;

theorem βηeq_βeq {a b} (p1 : βeq a b) : βηeq a b := by
  obtain ⟨D, Dh⟩ := p1;
  apply βηeq.trans;
  apply βηeq_βmstep Dh.1;
  apply βηeq.symm;
  apply βηeq_βmstep Dh.2;





inductive SK where
  | S
  | K
  | app (a b : SK) : SK
  | ref (x : Nat) : SK

inductive sred : SK → SK → Prop where
  | refl (a : SK) : sred a a
  | trans {a b c : SK} (h : sred a b) (h1 : sred b c) : sred a c
  | k (x y : SK) : sred (.app (.app .K x) y) x                      -- K x y → x
  | s (x y z : SK) : sred (.app (.app (.app .S x) y) z) (.app (.app x z) (.app y z))  -- S x y z → x z (y z)
  | app {M M' N N'} (h : sred M M') (h : sred N N') : sred (.app M N) (.app M' N')

def S : DB := .lam<| .lam<| .lam<| .app (.app (.ref 2) (.ref 0)) (.app (.ref 1) (.ref 0))
def K : DB := .lam<| .lam<| .ref 1

def to_LC : SK → DB
  | .app a b => .app (to_LC a) (to_LC b)
  | .S => S
  | .K => K
  | .ref x => .ref x

theorem red_SK_red_LC {p q : SK} (p1 : sred p q) : βmstep (to_LC p) (to_LC q) := by
  induction p1 <;> try simp! [S, K];
  apply βmstep.trans <;> assumption;

  apply βmstep.trans;
  apply βmstep.app;
  apply βmstep.redex;
  apply βmstep.refl;
  apply βmstep.trans;
  apply βmstep.redex;
  simp! [βmstep.refl];

  apply βmstep.trans;
  apply βmstep.app;
  apply βmstep.trans;
  apply βmstep.app;
  apply βmstep.redex;
  apply βmstep.refl;
  apply βmstep.redex;
  apply βmstep.refl;
  apply βmstep.trans;
  apply βmstep.redex;
  simp! [βmstep.refl];

  apply βmstep.app <;> assumption;

def bracket (t : SK) : SK :=
  match t with
  | .S => .app .K .S
  | .K => .app .K .K
  | .ref x =>
    if x = 0 then .app (.app .S .K) .K else .app .K (.ref (x - 1))
  | .app a b => .app (.app .S (bracket a)) (bracket b)

def to_SK (t : DB) : SK :=
  match t with
  | .ref x => .ref x
  | .app a b => .app (to_SK a) (to_SK b)
  | .lam p => bracket (to_SK p)

theorem K_βηeq (M : DB) : βηeq (.lam (shift M 1)) (.app K M) := by
  rw [K];
  apply βηeq.symm;
  apply βηeq.trans;
  apply βηeq.redex;
  simp_all!;
  apply βηeq.refl;

theorem S_βηeq (a b : DB) : βηeq (DB.app a b).lam (.app (.app S a.lam) b.lam) := by
  rw [S];
  apply βηeq.symm;
  apply βηeq.trans;
  apply βηeq.app;
  apply βηeq.redex;
  apply βηeq.refl;
  apply βηeq.trans;
  apply βηeq.redex;
  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.app;
  apply βηeq.redex;
  apply βηeq.refl;
  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.app;
  apply βηeq.refl;
  apply βηeq.redex;
  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.symm;
  simp_all!;
  apply βηeq.redex (M := shift' (.app a b) 1 1) (N := .ref 0);
  have := βηeq.eta (M := (DB.app a b).lam);
  simp_all!;

theorem shift_βηeq (M M') (p1 : βηeq M M') (k : Nat) : βηeq (shift' M 1 k) (shift' M' 1 k) := by
  induction p1 generalizing k;
  apply βηeq.symm; grind;
  apply βηeq.refl;

  expose_names;
  apply βηeq.trans (h_ih k) (h1_ih k);


  expose_names;
  apply βηeq.trans;
  apply βηeq.redex;

  have := shift_after_subst M_1 N 1 0 k
  simp_all;
  apply βηeq.refl;

  apply βηeq.app <;> simp_all!;

  expose_names;
  apply βηeq.lam;
  apply h_ih;

  expose_names;
  have := shift_shift_comm M_1 0 1 1 (k + 1) (by omega)
  simp_all!;
  apply βηeq.eta;

theorem bracket_correct (X : SK) : βηeq (to_LC (bracket X)) (.lam (to_LC X)) := by
  induction X <;> simp_all!;

  have := βηeq.symm (K_βηeq S);
  simp_all! [S, K];

  have := βηeq.symm (K_βηeq K);
  simp_all! [S, K];

  expose_names;
  have := βηeq.symm (S_βηeq (to_LC a) (to_LC b));

  apply βηeq.trans;
  apply βηeq.app;
  apply βηeq.refl;
  assumption;
  apply βηeq.trans;
  apply βηeq.app;
  apply βηeq.app;
  apply βηeq.refl;
  assumption;
  apply βηeq.refl;
  assumption;

  split <;> simp_all!;

  expose_names;
  simp_all [S, K];
  apply βηeq.trans;
  apply βηeq.app;
  apply βηeq.redex;
  apply βηeq.refl;
  apply βηeq.trans;
  apply βηeq.redex;

  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.app;
  apply βηeq.redex;
  apply βηeq.refl;

  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.app;
  apply βηeq.refl;
  apply βηeq.redex;

  apply βηeq.trans;
  apply βηeq.lam;
  apply βηeq.redex;
  apply βηeq.refl;

  expose_names;
  simp [K];
  apply βηeq.trans;
  apply βηeq.redex;
  simp!

  have : x - 1 +  1 = x := by omega;
  simp_all!;
  apply βηeq.refl;

theorem to_SK_correct (M : DB) : βηeq M (to_LC (to_SK M)) := by
  induction M;

  simp!; apply βηeq.refl;

  simp!;
  apply βηeq.trans;
  apply βηeq.app;
  assumption;
  apply βηeq.refl;
  apply βηeq.app;
  apply βηeq.refl;
  assumption;

  apply βηeq.trans;
  apply βηeq.lam;
  assumption;
  apply βηeq.symm;
  apply bracket_correct;



@[simp]
def closed (t : DB) := shift' t 1 0 = t

theorem to_LC_bracket_closed (M : SK) (k : Nat) (p1 : shift' (to_LC M) 1 (k + 1) = (to_LC M)) : shift' (to_LC (bracket M)) 1 k = (to_LC (bracket M)) := by
  induction M generalizing k <;> simp_all! [S, K];
  repeat' split <;> (try simp_all! [S, K]);
  omega;

theorem to_LC_to_SK_closed (M : DB) (k : Nat) (p1 : shift' M 1 k = M) : shift' (to_LC (to_SK M)) 1 k = (to_LC (to_SK M)) := by
  induction M generalizing k <;> simp_all! [S, K];
  apply to_LC_bracket_closed;
  grind;

@[simp]
theorem shift_closed (M : DB) (k : Nat) (p1 : shift' M 1 k = M) (n k' : Nat) (p1 : k' > k) : shift' M n k' = M := by
  induction M generalizing n k k' <;> simp_all!;
  intros; omega;
  grind;

  expose_names;
  apply a_ih;
  assumption;
  omega;

def proper (t : SK) :=
  match t with
  | .S => True
  | .K => True
  | .ref _ => False
  | .app a b => proper a ∧ proper b

theorem bracket_proper {T} (p1 : proper T) : proper (bracket T) := by
  induction T <;> simp_all!;

theorem proper_closed {T} : closed (to_LC T) ↔ proper T := by
  apply Iff.intro;
  induction T <;> simp_all!;
  induction T <;> simp_all! [S, K];

theorem subst_closed (A T) (k : Nat) (p1 : shift' A 1 k = A) : subst' A T k = A := by
  induction A generalizing k <;> simp_all!;
  expose_names;
  split <;> simp_all!;
  intro;
  omega;

def closed' (T : DB) : Bool :=
  shift' T 1 0 = T

instance : DecidablePred closed := fun T =>
  decidable_of_bool (closed' T) (by induction T <;> simp_all! [closed, closed'];)

theorem ιstep_closed {a b n k} (p1 : ιstep a b) (p2 : shift' a n k = a) : shift' b n k = b := by
  induction p1 generalizing n k <;> simp_all!;
  expose_names;
  have := shift_after_subst P' Q' n 0 k (by omega)
  simp_all;

theorem βmstep_closed {a b n k} (p1 : βmstep a b) (p2 : shift' a n k = a) : shift' b n k = b := by
  rw [←TransGenιstep_iff_βmstep] at p1;
  induction p1;
  apply ιstep_closed <;> assumption;
  apply ιstep_closed <;> assumption;




def SN (T : DB) : Prop := Acc (Function.swap βstep) T

def NF (T : DB) : Prop := ∀y, ¬βstep T y

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

theorem SN_NF (T : DB) (p1 : SN T) : ∃y, βmstep T y ∧ NF y := by
  obtain ⟨y, yh⟩ := acc_normal_form p1
  exists y;
  simp_all! [NF, flip];

  rw [←ReflTransGenβstep_iff_βmstep];
  exact yh.left.swap;

theorem NF_βmstep (a b) (p1 : NF a) (p2 : βmstep a b) : a = b := by
  by_contra;
  rw [←ReflTransGenβstep_iff_βmstep] at p2;
  induction p2;
  simp_all!;
  simp_all! [NF];

theorem unique_NF (T : DB) {x y} (p1 : βmstep T x ∧ NF x) (p2 : βmstep T y ∧ NF y) : x = y := by
  obtain ⟨D, Dh⟩ := church_rosser T x y (by grind;)
  have := p1.right D;
  simp_all [NF];
  have := NF_βmstep x D p1.2;
  have := NF_βmstep y D p2.2;
  simp_all!;

def normal : DB → Bool
  | .ref _          => True
  | .lam M          => normal M
  | .app (.lam _) _ => False
  | .app M N        => normal M ∧ normal N

theorem normal_NF (n : Nat) t : sizeOf t ≤ n → normal t → ∀t', ¬βstep t t' := by
  induction n generalizing t;
  cases t <;> simp_all!;

  intro _ p1 t' a1;
  cases t <;> cases a1 <;> simp_all!;

  rw [normal] at p1;
  expose_names;
  grind;
  intros;
  simp_all!;

  expose_names;
  rw [normal] at p1;
  grind;
  intros;
  simp_all!;

  grind;

theorem NF_normal t : (∀t', ¬βstep t t') → normal t := by
  intro a1;
  induction t <;> try simp_all!;

  expose_names;
  cases a <;> simp_all!;
  apply a_ih_1;
  intro t' a2;
  expose_names;
  apply a1;
  apply βstep.appR a2;

  and_intros;
  apply a_ih;
  intros;
  intro a2;
  apply a1;
  apply βstep.appL a2;

  apply a_ih_1;
  intros;
  intro a2;
  apply a1;
  apply βstep.appR a2;

  apply a1;
  apply βstep.redex;

  expose_names;
  apply a_ih;
  intros;
  intro a2;
  apply a1;
  apply βstep.lam a2;

theorem NF_iff_normal t : NF t ↔ normal t := by
  apply Iff.intro;
  apply NF_normal;
  apply normal_NF;
  rfl;

instance : DecidablePred NF := fun T =>
  decidable_of_bool (normal T) (Iff.symm (NF_iff_normal T))






--TODO show ¬DecidablePred HaltsLC
def HaltsLC (M : DB) : Prop :=
  ∃ N, βmstep M N ∧ NF N

def toNat : DB → Nat
  | .ref x   => 2 * x
  | .lam p   => 2 * (Nat.pair 0 (toNat p)) + 1
  | .app a b => 2 * (Nat.pair (toNat a + 1) (toNat b)) + 1

def ofNat (n : Nat) : DB :=
  if n % 2 = 0 then
    .ref (n / 2)
  else
    match _ : Nat.unpair (n / 2) with
    | (0, b)    => .lam (ofNat b)
    | (a + 1, b) => .app (ofNat a) (ofNat b)
termination_by n
decreasing_by
  all_goals
    have := Nat.unpair_left_le (n / 2)
    have := Nat.unpair_right_le (n / 2)
    simp_all!;
    try omega

theorem ofNat_toNat (t : DB) : ofNat (toNat t) = t := by
  induction t with
  | ref x =>
    simp [ofNat, toNat]
  | lam p ih =>
    rw [ofNat];
    simp_all!;
    rw [Nat.add_div_of_dvd_add_add_one]
    simp!;
    rw [Nat.mul_comm, Nat.mul_div_cancel (n := 2) (Nat.pair 0 (toNat p)) (by omega), Nat.unpair_pair]
    simp_all!;
    omega;
  | app a b iha ihb =>
    rw [ofNat]
    simp_all!;
    rw [Nat.add_div_of_dvd_add_add_one]
    simp!;
    rw [Nat.mul_comm, Nat.mul_div_cancel (n := 2) (Nat.pair (toNat a + 1) (toNat b)) (by omega), Nat.unpair_pair]
    simp_all!;
    omega;

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  induction n using Nat.strongRecOn
  unfold ofNat
  split_ifs
  simp [toNat]; omega
  split <;> simp_all!;
  expose_names;
  have := Nat.unpair_right_le (n / 2)
  have := Nat.pair_eq_of_unpair_eq heq;
  simp_all!;
  have := h b (by omega)
  simp_all!;
  omega;

  expose_names;
  have := Nat.unpair_left_le (n / 2)
  have := Nat.unpair_right_le (n / 2)
  have := Nat.pair_eq_of_unpair_eq heq;
  simp_all!;
  have := h a (by omega)
  have := h b (by omega)
  simp_all!;
  omega;

instance : Encodable DB where
  encode := toNat
  decode n := some (ofNat n)
  encodek t := by simp [ofNat_toNat]

instance : Denumerable DB where
  decode_inv := by
    intros;
    expose_names;
    exists (ofNat n)
    simp_all! [Encodable.decode, Encodable.encode, toNat_ofNat];

instance : Primcodable DB where
  prim := by
    have h : (fun n => Encodable.encode (Encodable.decode n : Option DB))
           = Nat.succ := by
      funext n
      simp [Encodable.decode, Encodable.encode, toNat_ofNat]
    rw [h]
    exact Nat.Primrec.succ

@[simp]
theorem encode_DB (t : DB) : (Encodable.encode t : Nat) = toNat t := rfl

@[simp]
theorem decode_DB (n : Nat) : (Encodable.decode n : Option DB) = some (ofNat n) := rfl










inductive CClo' (𝔽 : DB → Prop) : DB → Prop where
  | atom {a} (p2 : closed a ∧ 𝔽 a) : CClo' 𝔽 a
  | app {a b} (p1 : CClo' 𝔽 a) (p2 : CClo' 𝔽 b) : CClo' 𝔽 (.app a b)

def CClo 𝔽 t := ∃t', βηeq t t' ∧ CClo' 𝔽 t'

def CComplete 𝔽 := ∀t, closed t → CClo 𝔽 t

def to_LC' (s' k' : DB) : SK → DB
  | .app a b => .app (to_LC' s' k' a) (to_LC' s' k' b)
  | .S => s'
  | .K => k'
  | .ref x => .ref x

theorem βηeq_to_LC' {s' k'} t (p1 : βηeq s' S) (p2 : βηeq k' K) : βηeq (to_LC' s' k' t) (to_LC t) := by
  induction t <;> simp_all! [βηeq.refl];
  apply βηeq.app <;> assumption;

theorem CClo'_to_LC' {𝔽 t S K} (p1 : CClo' 𝔽 S) (p2 : CClo' 𝔽 K) (p3 : proper t) : CClo' 𝔽 (to_LC' S K t) := by
  induction t <;> simp_all!;
  apply CClo'.app <;> assumption;

theorem SK_CComplete {𝔽}
  (p1 : CClo 𝔽 S)
  (p2 : CClo 𝔽 K)
  : CComplete 𝔽 := by
  obtain ⟨s', s'h⟩ := p1;
  obtain ⟨k', k'h⟩ := p2;
  intro t ch;
  have := to_SK_correct t;
  have := βηeq_to_LC' (to_SK t) (βηeq.symm s'h.1) (βηeq.symm k'h.1);
  exists (to_LC' s' k' (to_SK t));
  and_intros;
  apply βηeq.trans; assumption;
  apply βηeq.symm; assumption;

  apply CClo'_to_LC';
  grind; grind;

  have := to_LC_to_SK_closed t 0 ch;
  exact proper_closed.mp this












end DeBruijn
