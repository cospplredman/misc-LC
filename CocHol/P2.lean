
inductive prop where
| ref : Nat → prop
| arr : prop → prop → prop
| not : prop → prop

inductive derive : prop → Prop where
| A1 (a b : prop) : derive (.arr a (.arr b a))
| A2 (a b c : prop) : derive (.arr (.arr a (.arr b c)) (.arr (.arr a b) (.arr a c)))
| A3 (a b : prop) : derive (.arr (.arr (.not a) (.not b)) (.arr b a))
| MP (a b : prop) (p1 : derive (.arr a b)) (p2 : derive a) : derive b

def eval (f : Nat → Bool) (P : prop) : Bool :=
  match P with
  | .ref x => f x
  | .arr a b => (eval f a) -> (eval f b)
  | .not p => !(eval f p)

def psize (P : prop) :=
  match P with
  | .ref _ => 1
  | .arr a b => psize a + psize b + 1
  | .not p => psize p + 1

theorem psize_gt_zero (p : prop) : 0 < psize p := by
  induction p <;> simp_all [psize]

theorem A1_taut (a b : prop) f : eval f (.arr a (.arr b a)) := by
  by_cases eval f a <;> simp_all [eval];

theorem A2_taut (a b c : prop) f : eval f (.arr (.arr a (.arr b c)) (.arr (.arr a b) (.arr a c))) := by
  by_cases eval f a <;> simp_all [eval];

theorem A3_taut (a b : prop) f : eval f (.arr (.arr (.not a) (.not b)) (.arr b a)) := by
  by_cases eval f a <;> simp_all [eval]

theorem MP_taut {a b : prop} (p1 : ∀f, eval f (.arr a b)) (p2 : ∀f, eval f a) : ∀f, eval f b := by
  simp_all [eval];

theorem derivation_taut {p : prop} (p1 : derive p) : ∀f, eval f p = true := by
  induction p1
  apply A1_taut
  apply A2_taut
  apply A3_taut
  expose_names;
  exact MP_taut p1_ih p2_ih;

theorem and_def (a b : Nat) f : (f a ∧ f b) ↔ eval f (.not (.arr (.ref a) (.not (.ref b)))) := by
  apply Iff.intro <;> simp_all [eval];

theorem or_def (a b : Nat) f : (f a ∨ f b) ↔ eval f (.arr (.not (.ref a)) (.ref b)) := by
  apply Iff.intro <;> simp_all [eval];

inductive deduction : List prop → prop → Prop where
| A1 (ctx : List prop) (a b : prop) : deduction ctx (.arr a (.arr b a))
| A2 (ctx : List prop) (a b c : prop) : deduction ctx (.arr (.arr a (.arr b c)) (.arr (.arr a b) (.arr a c)))
| A3 (ctx : List prop) (a b : prop) : deduction ctx (.arr (.arr (.not a) (.not b)) (.arr b a))
| MP (ctx : List prop) {a b : prop} (p1 : deduction ctx (.arr a b)) (p2 : deduction ctx a) : deduction ctx b
| hyp (ctx : List prop) (i : Fin ctx.length) : deduction ctx (ctx.get i)

theorem ded_thm_base (p : prop) : deduction [] p → derive p := by
  intro p1;
  induction p1
  apply derive.A1;
  apply derive.A2;
  apply derive.A3;
  apply derive.MP; assumption; assumption;
  grind;

theorem ded_thm {tail : List prop} (h p : prop) : deduction (h :: tail) p → deduction tail (.arr h p) := by
  intro h1;
  have thm {p : prop} (p1 : deduction tail p) := deduction.MP tail (deduction.A1 tail p h) p1
  have id (p : prop) :=
    deduction.MP tail
    (deduction.MP tail (deduction.A2 tail p (.arr p p) p)
      (deduction.A1 tail p (.arr p p)))
        (deduction.A1 tail p p)

  induction h1 <;> expose_names;
  apply thm; apply deduction.A1;
  apply thm; apply deduction.A2;
  apply thm; apply deduction.A3;

  exact deduction.MP tail (deduction.MP tail (deduction.A2 tail h a b) p1_ih) p2_ih

  cases i <;> simp_all;
  expose_names;
  cases val <;> simp_all;
  apply thm;
  apply deduction.hyp;
