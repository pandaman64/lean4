#eval Lean.versionString

theorem zero_div_eq_zero: ∀x, 0 / x = 0 := by {
  intro x;
  rw [Nat.div_eq];
  have h: ∀y, ¬(0 < y ∧ y ≤ 0) := by {
    intro y contra;
    have h': y = 0 := by {
      apply Nat.eq_zero_of_le_zero;
      apply contra.right;
    };
    rw [h'] at contra;
    apply Nat.lt_irrefl;
    apply contra.left;
  };
  simp [h];
}

theorem div_lt: ∀x y, x > 0 → y > 1 → x / y < x := by {
  intro x y x_gt_0 y_gt_1;
  induction x, y using Nat.div.inductionOn with
  | ind x y prems ih => {
    conv => {
      lhs;
      rw [Nat.div_eq];
      simp [prems];
    };

    have x_sub_y_add_y: x = x - y + y := by {
      apply Eq.symm;
      apply Nat.sub_add_cancel;
      apply prems.right;
    };
    have h: (x - y) / y + 1 < x := by {
      conv =>
        rhs;
        rw [x_sub_y_add_y];
      have or: y = x ∨ y < x := by {
        apply Nat.eq_or_lt_of_le;
        apply prems.right;
      };
      match or with
      | Or.inl y_eq_x => {
        simp [y_eq_x, zero_div_eq_zero];
        rw [y_eq_x] at y_gt_1;
        assumption;
      }
      | Or.inr y_lt_x => {
        apply Nat.add_lt_add;
        . {
          apply ih;
          . {
            apply Nat.zero_lt_sub_of_lt;
            assumption;
          }
          . assumption;
        }
        . assumption;
      }
    };
    assumption
  }
  | base x y prems => {
    rw [Nat.div_eq];
    simp [prems];
    assumption;
  }
}

def PositionalNotation {base: Nat} {h: base > 1} := List (Fin base)
def PositionalNotation.toNat {base: Nat} {h: base > 1}: @PositionalNotation base h → Nat :=
  List.foldr (fun (digit: Fin base) (accum: Nat) => accum + base * digit) 0

def toPositionalNotation {base: Nat} {h: base > 1} (n: Nat): @PositionalNotation base h :=
  if isLt: n < base then
    [Fin.mk n isLt]
  else
    let rem := n % base;
    let quot := n / base;
    let h': base > 0 := by {
      apply Nat.lt_trans;
      case m => apply 1;
      decide;
      assumption;
    };
    let n_gt_0: n > 0 := by {
      apply Nat.lt_of_lt_of_le;
      case m => apply base;
      . apply h';
      . match Nat.lt_or_ge n base with
        | Or.inl _ => contradiction;
        | Or.inr _ => assumption;
    };
    Fin.mk rem (Nat.mod_lt n h') :: @toPositionalNotation base h quot
termination_by _ n => n
decreasing_by {
  apply div_lt;
  . apply n_gt_0;
  . apply h;
}

theorem add_div_mod_eq: ∀x y: Nat, x = x / y * y + x % y := by {
  intro x y;
  induction x, y using Nat.div.inductionOn with
  | ind x y prems ih => {
    rw [Nat.div_eq, Nat.mod_eq];
    simp [prems];
    conv in _ * y => {
      apply Nat.add_mul;
    };
    simp;
    rw [Nat.add_assoc];
    conv in y + _ => {
      apply Nat.add_comm;
    };
    rw [←Nat.add_assoc];
    have ih': x - y + y = (x - y) / y * y + (x - y) % y + y := by {
      conv => {
        lhs;
        rw [ih];
      }
    }
    rw [Nat.sub_add_cancel] at ih';
    . assumption;
    . apply prems.right;
  }
  | base x y prems => {
    rw [Nat.div_eq, Nat.mod_eq];
    simp [prems];
  };
}

theorem toPos_inv: ∀base, {h: base > 1} → ∀n, @PositionalNotation.toNat base h (toPositionalNotation n) = n := by {
  intro base h n;
  let motive := fun n => @PositionalNotation.toNat base h (toPositionalNotation n) = n;
  apply @WellFounded.induction _ _ (measure id).wf motive;
  intro x y;
  simp;
  simp at y;
  conv => {
    lhs;
    rhs;
    -- このunfoldがループする
    unfold toPositionalNotation;
  };
}

#print Nat.lt_wfRel
#check WellFounded.fix (measure id).wf
#print WellFounded.fix_eq
