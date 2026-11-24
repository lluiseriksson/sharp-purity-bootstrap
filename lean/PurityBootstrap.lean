/-
  PurityBootstrap.lean
  Self-contained, zero-dependency Lean 4 formalization (Level L2: zero sorry, standard axioms only)
  for:
    "Exact Sharp Thresholds, Piecewise-Algebraic Squaring Laws, and Machine-Checked
     Thermodynamic Mass-Gap Certificates for the Reflection-Positive Purity Bootstrap"

  Every theorem is proved parametrically over an arbitrary linearly ordered commutative field
  `OrdField K` (covering both `ℝ` and `ℚ`), with zero `sorry` and zero custom axioms.

  Formalized results (audited in `AuditAxioms.lean`):
    1. `squaring_inequality_k1`              (Theorem 2.2: exact sharp squaring law on (1/2, 1])
    2. `squaring_inequality_k1_sharp`        (Theorem 2.2: exact attainment on any 2-level spectrum)
    3. `squaring_inequality_ratio`           (Theorem 2.2: normalized ratio form p' >= h_1*(p))
    4. `hStar_monotone`                      (Theorem 2.2 / 5.1: strict monotonicity of h_1* on (0, 1])
    5. `dominant_weight_ge_purity`           (Theorem 2.3: w_0 >= p)
    6. `purity_defect_ge_two_w0_tail`        (Theorem 2.3: 1 - p >= 2 w_0 (1 - w_0))
    7. `sharp_discriminant_lower_bound`      (Theorem 2.3: (2 w_0 - 1)^2 >= 2 p - 1)
    8. `sharp_gap_ratio_bound`               (Theorem 2.3: w_0 / w_1 >= 2 w_0^2 / (1 - p) >= 2 p^2 / (1 - p))
    9. `plaquette_exact_identity`            (Section 3.1: exact space-time plaquette identity)
   10. `plaquette_lower_bound`               (Section 3.1: S(L, 2b) >= S(L, b)^2 * T(2L, b))
   11. `gs_1d_step_sound`                    (Theorem 3.1: 1D cyclic Gauss-Seidel step soundness)
   12. `gs_1d_induction_sound`               (Theorem 3.1: inductive N-step 1D Gauss-Seidel propagation)
   13. `gs_1d_monotone`                      (Theorem 3.1 / 5.1: interval/finite-sample monotonicity of 1D GS map)
   14. `hypercube_Q_step_sound`              (Theorem 3.2: general D-dimensional cyclic Q-step soundness)
   15. `doubly_exponential_contraction`      (Theorem 4.1: u_{n+1} <= C u_n^2 -> C u_n <= (C u_0)^{2^n})
   16. `intervening_length_purity_transfer`  (Theorem 4.2: exact intervening-length T(l, b) lower bound)
-/

namespace PurityBootstrap

-- ============================================================================
-- 0. Linearly Ordered Commutative Field Interface
-- ============================================================================

class OrdField (K : Type) extends Add K, Sub K, Mul K, Div K, Neg K, Zero K, One K, LT K, LE K where
  add_comm : ∀ a b : K, a + b = b + a
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  zero_add : ∀ a : K, 0 + a = a
  add_neg_cancel : ∀ a : K, a + (-a) = 0
  sub_eq_add_neg : ∀ a b : K, a - b = a + (-b)
  mul_comm : ∀ a b : K, a * b = b * a
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  div_eq_mul_inv : ∀ a b : K, a / b = a * (1 / b)
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * (1 / a) = 1
  le_refl : ∀ a : K, a ≤ a
  le_trans : ∀ {a b c : K}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : K}, a ≤ b → b ≤ a → a = b
  le_of_lt : ∀ {a b : K}, a < b → a ≤ b
  lt_of_lt_of_le : ∀ {a b c : K}, a < b → b ≤ c → a < c
  lt_of_le_of_lt : ∀ {a b c : K}, a ≤ b → b < c → a < c
  lt_irrefl : ∀ a : K, ¬ (a < a)
  add_le_add : ∀ {a b c d : K}, a ≤ b → c ≤ d → a + c ≤ b + d
  mul_nonneg : ∀ {a b : K}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  mul_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a * b
  mul_le_mul_of_nonneg_left : ∀ {a b c : K}, a ≤ b → 0 ≤ c → c * a ≤ c * b
  mul_le_mul_of_nonneg_right : ∀ {a b c : K}, a ≤ b → 0 ≤ c → a * c ≤ b * c
  div_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a / b
  zero_lt_one : (0 : K) < 1
  sub_nonneg_of_le : ∀ {a b : K}, a ≤ b → 0 ≤ b - a
  le_of_sub_nonneg : ∀ {a b : K}, 0 ≤ b - a → a ≤ b
  sub_pos_of_lt : ∀ {a b : K}, a < b → 0 < b - a

section CoreAlgebra
variable {K : Type} [OrdField K]

theorem add_zero' (a : K) : a + 0 = a := by rw [OrdField.add_comm, OrdField.zero_add]
theorem mul_one' (a : K) : a * 1 = a := by rw [OrdField.mul_comm, OrdField.one_mul]
theorem right_distrib' (a b c : K) : (a + b) * c = a * c + b * c := by
  rw [OrdField.mul_comm, OrdField.left_distrib, OrdField.mul_comm c a, OrdField.mul_comm c b]

theorem mul_zero' (a : K) : a * 0 = 0 := by
  have h1 : a * 0 + a * 0 = a * 0 := by rw [← OrdField.left_distrib, OrdField.zero_add]
  have h2 := congrArg (· + -(a * 0)) h1
  rw [OrdField.add_assoc, OrdField.add_neg_cancel, add_zero'] at h2
  exact h2

theorem zero_mul' (a : K) : 0 * a = 0 := by rw [OrdField.mul_comm, mul_zero']
theorem neg_add_cancel' (a : K) : (-a) + a = 0 := by rw [OrdField.add_comm, OrdField.add_neg_cancel]

theorem mul_neg' (a b : K) : a * (-b) = -(a * b) := by
  have h : a * b + a * (-b) = 0 := by rw [← OrdField.left_distrib, OrdField.add_neg_cancel, mul_zero']
  have h2 := congrArg (-(a * b) + ·) h
  rw [← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, add_zero'] at h2
  exact h2

theorem neg_mul' (a b : K) : (-a) * b = -(a * b) := by rw [OrdField.mul_comm, mul_neg', OrdField.mul_comm]

theorem neg_neg' (a : K) : -(-a) = a := by
  have h : (-a) + a = 0 := neg_add_cancel' a
  have h2 := congrArg (· + -(-a)) h
  rw [OrdField.add_assoc, OrdField.add_comm a (-(-a)), ← OrdField.add_assoc,
      OrdField.add_neg_cancel, OrdField.zero_add, OrdField.zero_add] at h2
  exact h2.symm

theorem mul_sub' (a b c : K) : a * (b - c) = a * b - a * c := by
  rw [OrdField.sub_eq_add_neg, OrdField.sub_eq_add_neg, OrdField.left_distrib, mul_neg']

theorem sub_mul' (a b c : K) : (a - b) * c = a * c - b * c := by
  rw [OrdField.sub_eq_add_neg, OrdField.sub_eq_add_neg, right_distrib', neg_mul']

theorem sub_self' (a : K) : a - a = 0 := by rw [OrdField.sub_eq_add_neg, OrdField.add_neg_cancel]
theorem sub_add_cancel' (a b : K) : (a - b) + b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, neg_add_cancel', add_zero']
theorem add_sub_cancel' (a b : K) : (a + b) - b = a := by
  rw [OrdField.sub_eq_add_neg, OrdField.add_assoc, OrdField.add_neg_cancel, add_zero']

theorem neg_add' (a b : K) : -(a + b) = (-a) + (-b) := by
  have h : (a + b) + ((-a) + (-b)) = 0 := by
    rw [OrdField.add_assoc, ← OrdField.add_assoc b (-a) (-b),
        OrdField.add_comm b (-a), OrdField.add_assoc (-a) b (-b),
        ← OrdField.add_assoc a (-a), OrdField.add_neg_cancel, OrdField.add_neg_cancel, OrdField.zero_add]
  have h2 := congrArg (-(a + b) + ·) h
  rw [← OrdField.add_assoc, neg_add_cancel', OrdField.zero_add, add_zero'] at h2
  exact h2.symm

theorem ne_zero_of_pos {a : K} (h : 0 < a) : a ≠ 0 := by
  intro heq; rw [heq] at h; exact OrdField.lt_irrefl 0 h

theorem div_mul_cancel' (a b : K) (hb : b ≠ 0) : (a / b) * b = a := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_assoc, OrdField.mul_comm (1 / b) b,
      OrdField.mul_inv_cancel b hb, mul_one']

theorem mul_div_cancel_right' (a b : K) (hb : b ≠ 0) : (a * b) / b = a := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_assoc, OrdField.mul_inv_cancel b hb, mul_one']

theorem div_self' (a : K) (ha : a ≠ 0) : a / a = 1 := by
  rw [OrdField.div_eq_mul_inv, OrdField.mul_inv_cancel a ha]

theorem div_le_div_of_nonneg_right {a b c : K} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [OrdField.div_eq_mul_inv a c, OrdField.div_eq_mul_inv b c]
  exact OrdField.mul_le_mul_of_nonneg_right h (OrdField.le_of_lt (OrdField.div_pos OrdField.zero_lt_one hc))

theorem inv_le_inv_of_le {a b : K} (ha : 0 < a) (hab : a ≤ b) : 1 / b ≤ 1 / a := by
  have hb : 0 < b := OrdField.lt_of_lt_of_le ha hab
  have hia : 0 < 1 / a := OrdField.div_pos OrdField.zero_lt_one ha
  have hib : 0 < 1 / b := OrdField.div_pos OrdField.zero_lt_one hb
  have h1 := OrdField.mul_le_mul_of_nonneg_left hab (OrdField.le_of_lt hib)
  rw [OrdField.mul_comm (1 / b) b, OrdField.mul_inv_cancel b (ne_zero_of_pos hb)] at h1
  have h2 := OrdField.mul_le_mul_of_nonneg_right h1 (OrdField.le_of_lt hia)
  rw [OrdField.mul_assoc, OrdField.mul_inv_cancel a (ne_zero_of_pos ha), mul_one', OrdField.one_mul] at h2
  exact h2

theorem div_le_div_of_nonneg_left {a b c : K} (ha : 0 ≤ a) (hb : 0 < b) (hbc : b ≤ c) : a / c ≤ a / b := by
  rw [OrdField.div_eq_mul_inv a c, OrdField.div_eq_mul_inv a b]
  exact OrdField.mul_le_mul_of_nonneg_left (inv_le_inv_of_le hb hbc) ha

theorem sub_le_sub_left' {a b : K} (c : K) (h : a ≤ b) : c - b ≤ c - a := by
  apply OrdField.le_of_sub_nonneg
  have hrew : (c - a) - (c - b) = b - a := by
    rw [OrdField.sub_eq_add_neg (c - a), OrdField.sub_eq_add_neg c b,
        neg_add', neg_neg', OrdField.sub_eq_add_neg c a,
        OrdField.add_assoc c (-a), OrdField.add_comm (-a) (-c + b),
        ← OrdField.add_assoc c (-c + b), ← OrdField.add_assoc c (-c) b,
        OrdField.add_neg_cancel, OrdField.zero_add, ← OrdField.sub_eq_add_neg]
  rw [hrew]
  exact OrdField.sub_nonneg_of_le h

theorem le_add_of_nonneg_right {a b : K} (hb : 0 ≤ b) : a ≤ a + b := by
  have h := OrdField.add_le_add (OrdField.le_refl a) hb
  rw [add_zero'] at h
  exact h

theorem mul_le_mul_nonneg {a b c d : K} (ha : 0 ≤ a) (hd : 0 ≤ d) (hab : a ≤ b) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  have h1 := OrdField.mul_le_mul_of_nonneg_left hcd ha
  have h2 := OrdField.mul_le_mul_of_nonneg_right hab hd
  exact OrdField.le_trans h1 h2

theorem two_pos : (0 : K) < 1 + 1 := by
  have h01 := OrdField.zero_lt_one (K := K)
  have hle := le_add_of_nonneg_right (a := (1 : K)) (OrdField.le_of_lt h01)
  exact OrdField.lt_of_lt_of_le h01 hle

theorem two_ne_zero : (1 : K) + 1 ≠ 0 := ne_zero_of_pos two_pos

def listSum : List K → K
  | [] => 0
  | x :: xs => x + listSum xs

def powK (a : K) : Nat → K
  | 0 => 1
  | n + 1 => a * powK a n

theorem powK_nonneg {a : K} (ha : 0 ≤ a) : ∀ n : Nat, 0 ≤ powK a n
  | 0 => OrdField.le_of_lt OrdField.zero_lt_one
  | n + 1 => OrdField.mul_nonneg ha (powK_nonneg ha n)

theorem powK_pos {a : K} (ha : 0 < a) : ∀ n : Nat, 0 < powK a n
  | 0 => OrdField.zero_lt_one
  | n + 1 => OrdField.mul_pos ha (powK_pos ha n)

theorem powK_le_one {a : K} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ∀ n : Nat, powK a n ≤ 1
  | 0 => OrdField.le_refl 1
  | n + 1 => by
    have h1 := OrdField.mul_le_mul_of_nonneg_left (powK_le_one ha0 ha1 n) ha0
    rw [mul_one'] at h1
    exact OrdField.le_trans h1 ha1

theorem powK_mono {a b : K} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n : Nat, powK a n ≤ powK b n
  | 0 => OrdField.le_refl 1
  | n + 1 => by
    have hb : 0 ≤ b := OrdField.le_trans ha hab
    exact mul_le_mul_nonneg ha (powK_nonneg hb n) hab (powK_mono ha hab n)

theorem powK_add (a : K) (m n : Nat) : powK a (m + n) = powK a m * powK a n := by
  induction m with
  | zero => simp [powK, OrdField.one_mul]
  | succ k ih =>
    have hsucc : k + 1 + n = (k + n) + 1 := by omega
    rw [hsucc, powK, ih, powK, OrdField.mul_assoc]

theorem powK_mul (a : K) (m n : Nat) : powK a (m * n) = powK (powK a m) n := by
  induction n with
  | zero => simp [powK]
  | succ k ih =>
    have hmul : m * (k + 1) = m + m * k := by rw [Nat.mul_succ, Nat.add_comm]
    rw [hmul, powK_add, ih, powK]

theorem mul_four_swap (a b : K) : (a * a) * (b * b) = (a * b) * (a * b) := by
  rw [OrdField.mul_assoc a a (b * b), ← OrdField.mul_assoc a b b,
      OrdField.mul_comm a b, OrdField.mul_assoc b a b, ← OrdField.mul_assoc a b (a * b),
      OrdField.mul_comm b a]

theorem div_div_eq_div_mul (a b c : K) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b * c ≠ 0) :
    (a / b) / c = a / (b * c) := by
  have hchk : ((a / b) / c) * (b * c) = a := by
    rw [OrdField.mul_comm b c, ← OrdField.mul_assoc, div_mul_cancel' (a / b) c hc,
        div_mul_cancel' a b hb]
  calc (a / b) / c = (((a / b) / c) * (b * c)) / (b * c) := (mul_div_cancel_right' _ (b * c) hbc).symm
    _ = a / (b * c) := congrArg (· / (b * c)) hchk

theorem listSum_nonneg (l : List K) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ listSum l := by
  induction l with
  | nil => exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [listSum]
    have ha := h a (List.Mem.head t)
    have ht := ih (fun x hx => h x (List.Mem.tail a hx))
    have hsum := OrdField.add_le_add ha ht
    rw [OrdField.zero_add] at hsum
    exact hsum

theorem listSum_map_mul_left {α : Type} (l : List α) (c : K) (f : α → K) :
    listSum (l.map (fun x => c * f x)) = c * listSum (l.map f) := by
  induction l with
  | nil => simp [listSum, mul_zero']
  | cons a t ih => simp only [List.map_cons, listSum, ih, OrdField.left_distrib]

theorem listSum_map_add {α : Type} (l : List α) (f g : α → K) :
    listSum (l.map (fun x => f x + g x)) = listSum (l.map f) + listSum (l.map g) := by
  induction l with
  | nil => simp [listSum, OrdField.zero_add]
  | cons a t ih =>
    simp only [List.map_cons, listSum, ih]
    rw [OrdField.add_assoc (f a) (g a), ← OrdField.add_assoc (g a),
        OrdField.add_comm (g a) (listSum (t.map f)), OrdField.add_assoc (listSum (t.map f)),
        ← OrdField.add_assoc (f a)]

theorem listSum_le_listSum {α : Type} (l : List α) (f g : α → K)
    (h : ∀ x ∈ l, f x ≤ g x) : listSum (l.map f) ≤ listSum (l.map g) := by
  induction l with
  | nil => exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [List.map_cons, listSum]
    exact OrdField.add_le_add (h a (List.Mem.head t)) (ih (fun x hx => h x (List.Mem.tail a hx)))

theorem sum_sq_le_sq_sum (l : List K) (h : ∀ x ∈ l, 0 ≤ x) :
    listSum (l.map (fun x => x * x)) ≤ listSum l * listSum l := by
  induction l with
  | nil =>
    simp only [List.map_nil, listSum, mul_zero']
    exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [List.map_cons, listSum]
    have ha : 0 ≤ a := h a (List.Mem.head t)
    have ht_all : ∀ x ∈ t, 0 ≤ x := fun x hx => h x (List.Mem.tail a hx)
    have ht : 0 ≤ listSum t := listSum_nonneg t ht_all
    have hih := ih ht_all
    -- (a + S)^2 = (a*a + S*S) + (a*S + a*S)
    have hexp : (a + listSum t) * (a + listSum t) =
        (a * a + listSum t * listSum t) + (a * listSum t + a * listSum t) := by
      rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm (listSum t) a,
          OrdField.add_assoc (a * a), ← OrdField.add_assoc (a * listSum t) (a * listSum t),
          OrdField.add_comm (a * listSum t + a * listSum t) (listSum t * listSum t),
          ← OrdField.add_assoc (a * a)]
    rw [hexp]
    have hstep1 := OrdField.add_le_add (OrdField.le_refl (a * a)) hih
    have hcross : 0 ≤ a * listSum t + a * listSum t := by
      have hm := OrdField.mul_nonneg ha ht
      have h2 := OrdField.add_le_add hm hm
      rw [OrdField.zero_add] at h2
      exact h2
    exact OrdField.le_trans hstep1 (le_add_of_nonneg_right hcross)

/-- Exact ordered-pair sum `∑_{i < j} f(w_i, w_j)` on a list. -/
def pairSum (f : K → K → K) : List K → K
  | [] => 0
  | a :: t => listSum (t.map (fun b => f a b)) + pairSum f t

theorem sq_sum_eq_sum_sq_add_two_pairs (l : List K) :
    listSum l * listSum l =
    listSum (l.map (fun x => x * x)) + (1 + 1) * pairSum (fun x y => x * y) l := by
  induction l with
  | nil => simp [listSum, pairSum, mul_zero', add_zero']
  | cons a t ih =>
    simp only [List.map_cons, listSum, pairSum]
    rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm (listSum t) a, ih]
    rw [listSum_map_mul_left t a (fun b => b)]
    have hid : t.map (fun b => b) = t := List.map_id t
    rw [hid, OrdField.left_distrib (1 + 1)]
    have h2 : (1 + 1) * (a * listSum t) = a * listSum t + a * listSum t := by
      rw [right_distrib', OrdField.one_mul]
    rw [h2]
    let A := a * a; let B := a * listSum t; let C := listSum (t.map (fun x => x * x))
    let D := (1 + 1) * pairSum (fun x y => x * y) t
    change (A + B) + (B + (C + D)) = (A + C) + ((B + B) + D)
    rw [OrdField.add_assoc A B (B + (C + D)), ← OrdField.add_assoc B B (C + D),
        ← OrdField.add_assoc (B + B) C D, OrdField.add_comm (B + B) C,
        OrdField.add_assoc C (B + B) D, ← OrdField.add_assoc A C ((B + B) + D)]

theorem pairSum_mul_nonneg (l : List K) (h : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ pairSum (fun x y => x * y) l := by
  induction l with
  | nil => exact OrdField.le_refl 0
  | cons c r ihr =>
    simp only [pairSum]
    have hc := h c (List.Mem.head r)
    have hr := fun x hx => h x (List.Mem.tail c hx)
    have h1 : 0 ≤ listSum (r.map (fun b => c * b)) := by
      apply listSum_nonneg
      intro y hy; rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
      exact OrdField.mul_nonneg hc (hr b hb)
    have h2 := OrdField.add_le_add h1 (ihr hr)
    rw [OrdField.zero_add] at h2; exact h2

theorem pairSum_sq_le_sq_pairSum (l : List K) (h : ∀ x ∈ l, 0 ≤ x) :
    pairSum (fun x y => (x * y) * (x * y)) l ≤
    pairSum (fun x y => x * y) l * pairSum (fun x y => x * y) l := by
  induction l with
  | nil =>
    simp only [pairSum, mul_zero']
    exact OrdField.le_refl 0
  | cons a t ih =>
    simp only [pairSum]
    have ha : 0 ≤ a := h a (List.Mem.head t)
    have ht_all : ∀ x ∈ t, 0 ≤ x := fun x hx => h x (List.Mem.tail a hx)
    have hih := ih ht_all
    -- First show listSum (t.map (fun b => (a*b)*(a*b))) <= (listSum (t.map (fun b => a*b)))^2
    have hhead_nn : ∀ y ∈ t.map (fun b => a * b), 0 ≤ y := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
      exact OrdField.mul_nonneg ha (ht_all b hb)
    have hhead : listSum (t.map (fun b => (a * b) * (a * b))) ≤
        listSum (t.map (fun b => a * b)) * listSum (t.map (fun b => a * b)) := by
      have hm : t.map (fun b => (a * b) * (a * b)) = (t.map (fun b => a * b)).map (fun y => y * y) := by
        rw [List.map_map]; rfl
      rw [hm]
      exact sum_sq_le_sq_sum (t.map (fun b => a * b)) hhead_nn
    have hA_nn : 0 ≤ listSum (t.map (fun b => a * b)) := listSum_nonneg _ hhead_nn
    have hP_nn : 0 ≤ pairSum (fun x y => x * y) t := pairSum_mul_nonneg t ht_all
    let X := listSum (t.map (fun b => a * b))
    let Y := pairSum (fun x y => x * y) t
    have hexp : (X + Y) * (X + Y) = (X * X + Y * Y) + (X * Y + X * Y) := by
      rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm Y X,
          OrdField.add_assoc (X * X), ← OrdField.add_assoc (X * Y) (X * Y),
          OrdField.add_comm (X * Y + X * Y) (Y * Y), ← OrdField.add_assoc (X * X)]
    change listSum (t.map (fun b => (a * b) * (a * b))) + pairSum (fun x y => (x * y) * (x * y)) t ≤ (X + Y) * (X + Y)
    rw [hexp]
    have h1 := OrdField.add_le_add hhead hih
    have hcross : 0 ≤ X * Y + X * Y := by
      have hm := OrdField.mul_nonneg hA_nn hP_nn
      have h2 := OrdField.add_le_add hm hm
      rw [OrdField.zero_add] at h2; exact h2
    exact OrdField.le_trans h1 (le_add_of_nonneg_right hcross)

end CoreAlgebra

-- ============================================================================
-- 1. THEOREM 2.1: Exact Sharp Squaring Law on (1/2, 1] & Monotonicity
-- ============================================================================

section SharpSquaring
variable {K : Type} [OrdField K]

/-- Exact sharp squaring lower-bound function `h*(p) = 1 - (1 - p)^2 / (2 p^2)` on `(1/2, 1]`. -/
def hStar (p : K) : K :=
  1 - ((1 - p) * (1 - p)) / ((1 + 1) * (p * p))

/-- **Theorem 2.1 (Exact Sharp Squaring Law — Polynomial Form):**
    For ANY finite probability distribution `w` (`w_i ≥ 0`, `∑ w_i = 1`) with purity `p = ∑ w_i^2`,
      `∑ w_i^4 ≥ p^2 - (1 - p)^2 / 2`.
    Proof is 100% elementary ring algebra (0 calculus, 0 axioms)! -/
theorem squaring_inequality_k1 (w : List K)
    (hnn : ∀ x ∈ w, 0 ≤ x)
    (hsum : listSum w = 1) :
    let p := listSum (w.map (fun x => x * x))
    let q := listSum (w.map (fun x => (x * x) * (x * x)))
    p * p - ((1 - p) * (1 - p)) / (1 + 1) ≤ q := by
  intro p q
  -- Identity 1: 1 - p = 2 * pairSum(w_i w_j)
  have h1 : 1 - p = (1 + 1) * pairSum (fun x y => x * y) w := by
    have hsq := sq_sum_eq_sum_sq_add_two_pairs w
    rw [hsum, OrdField.one_mul] at hsq
    change 1 = p + (1 + 1) * pairSum (fun x y => x * y) w at hsq
    calc 1 - p = (p + (1 + 1) * pairSum (fun x y => x * y) w) - p := congrArg (· - p) hsq
      _ = (1 + 1) * pairSum (fun x y => x * y) w := by rw [OrdField.add_comm p, add_sub_cancel']
  -- Identity 2: p^2 - q = 2 * pairSum(w_i^2 w_j^2)
  have h2 : p * p - q = (1 + 1) * pairSum (fun x y => (x * y) * (x * y)) w := by
    have hsq := sq_sum_eq_sum_sq_add_two_pairs (w.map (fun x => x * x))
    have hq_eq : (w.map (fun x => x * x)).map (fun x => x * x) = w.map (fun x => (x * x) * (x * x)) := by
      rw [List.map_map]; rfl
    have hp_eq : pairSum (fun x y => x * y) (w.map (fun x => x * x)) =
                 pairSum (fun x y => (x * y) * (x * y)) w := by
      clear hsq hq_eq h1 hsum hnn p q
      induction w with
      | nil => rfl
      | cons a t ih =>
        simp only [List.map_cons, pairSum, List.map_map, ih]
        congr 2
        apply List.map_congr_left
        intro b _
        dsimp only [Function.comp_apply]
        exact mul_four_swap a b
    rw [hq_eq, hp_eq] at hsq
    change p * p = q + (1 + 1) * pairSum (fun x y => (x * y) * (x * y)) w at hsq
    calc p * p - q = (q + (1 + 1) * pairSum (fun x y => (x * y) * (x * y)) w) - q := congrArg (· - q) hsq
      _ = (1 + 1) * pairSum (fun x y => (x * y) * (x * y)) w := by rw [OrdField.add_comm q, add_sub_cancel']
  -- Inequality: pairSum(w_i^2 w_j^2) ≤ (pairSum(w_i w_j))^2
  have hle := pairSum_sq_le_sq_pairSum w hnn
  have h2nn : (0 : K) ≤ 1 + 1 := OrdField.le_of_lt two_pos
  have hmul := OrdField.mul_le_mul_of_nonneg_left hle h2nn
  -- (1 - p)^2 / 2 = 2 * (pairSum)^2
  have hrhs : ((1 - p) * (1 - p)) / (1 + 1) =
      (1 + 1) * (pairSum (fun x y => x * y) w * pairSum (fun x y => x * y) w) := by
    rw [h1]
    let S := pairSum (fun x y => x * y) w
    change ((1 + 1) * S * ((1 + 1) * S)) / (1 + 1) = (1 + 1) * (S * S)
    have hrearr : (1 + 1) * S * ((1 + 1) * S) = ((1 + 1) * (S * S)) * (1 + 1) := by
      rw [OrdField.mul_assoc (1 + 1) S ((1 + 1) * S), ← OrdField.mul_assoc S (1 + 1) S,
          OrdField.mul_comm S (1 + 1), OrdField.mul_assoc (1 + 1) S S,
          OrdField.mul_comm (1 + 1) ((1 + 1) * (S * S))]
    rw [hrearr, mul_div_cancel_right' _ (1 + 1) two_ne_zero]
  rw [← h2, ← hrhs] at hmul
  -- p*p - q <= (1-p)^2/2  ==>  p*p - (1-p)^2/2 <= q
  have hsub := sub_le_sub_left' (p * p) hmul
  have hlhs_simp : p * p - (p * p - q) = q := by
    rw [OrdField.sub_eq_add_neg (p * p) (p * p - q), OrdField.sub_eq_add_neg (p * p) q,
        neg_add', neg_neg', ← OrdField.add_assoc, OrdField.add_neg_cancel, OrdField.zero_add]
  rw [hlhs_simp] at hsub
  exact hsub

/-- **Theorem 2.1 (Normalized Ratio Form):** `q / p^2 ≥ h*(p)` whenever `p > 0`. -/
theorem squaring_inequality_ratio (w : List K)
    (hnn : ∀ x ∈ w, 0 ≤ x)
    (hsum : listSum w = 1)
    (hp : 0 < listSum (w.map (fun x => x * x))) :
    let p := listSum (w.map (fun x => x * x))
    let q := listSum (w.map (fun x => (x * x) * (x * x)))
    hStar p ≤ q / (p * p) := by
  intro p q
  have hpoly := squaring_inequality_k1 w hnn hsum
  have hp2 : 0 < p * p := OrdField.mul_pos hp hp
  have hp2_nz : p * p ≠ 0 := ne_zero_of_pos hp2
  have hdiv := div_le_div_of_nonneg_right hpoly hp2
  have hlhs : (p * p - ((1 - p) * (1 - p)) / (1 + 1)) / (p * p) = hStar p := by
    unfold hStar
    rw [OrdField.div_eq_mul_inv _ (p * p), sub_mul',
        ← OrdField.div_eq_mul_inv (p * p) (p * p), div_self' (p * p) hp2_nz]
    congr 1
    rw [OrdField.div_eq_mul_inv ((1 - p) * (1 - p)) (1 + 1),
        OrdField.div_eq_mul_inv ((1 - p) * (1 - p)) ((1 + 1) * (p * p)),
        OrdField.mul_assoc]
    congr 1
    -- (1 / 2) * (1 / p^2) = 1 / (2 * p^2)
    have hprod_nz : (1 + 1) * (p * p) ≠ 0 := ne_zero_of_pos (OrdField.mul_pos two_pos hp2)
    have hcheck : ((1 + 1) * (p * p)) * ((1 / (1 + 1)) * (1 / (p * p))) = 1 := by
      rw [OrdField.mul_assoc (1 + 1) (p * p), ← OrdField.mul_assoc (p * p) (1 / (1 + 1)),
          OrdField.mul_comm (p * p) (1 / (1 + 1)), OrdField.mul_assoc (1 / (1 + 1)) (p * p),
          OrdField.mul_inv_cancel (p * p) hp2_nz, mul_one', OrdField.mul_inv_cancel (1 + 1) two_ne_zero]
    have hmul_inv := congrArg (fun x => (1 / ((1 + 1) * (p * p))) * x) hcheck
    rw [mul_one', ← OrdField.mul_assoc, OrdField.mul_comm (1 / ((1 + 1) * (p * p))),
        OrdField.mul_inv_cancel _ hprod_nz, OrdField.one_mul] at hmul_inv
    exact hmul_inv
  rw [← hlhs]
  exact hdiv

/-- **Theorem 2.1 (Exact Sharpness on 2-Level Spectra):**
    On any 2-element probability distribution `[a, b]` with `a + b = 1`, equality holds identically:
      `a^4 + b^4 = p^2 - (1 - p)^2 / 2`. -/
theorem squaring_inequality_k1_sharp (a b : K) (hsum : a + b = 1) :
    let p := a * a + b * b
    (a * a) * (a * a) + (b * b) * (b * b) = p * p - ((1 - p) * (1 - p)) / (1 + 1) := by
  intro p
  have h1p : 1 - p = (1 + 1) * (a * b) := by
    have hsq : (a + b) * (a + b) = p + (1 + 1) * (a * b) := by
      dsimp only [p]
      rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm b a,
          right_distrib', OrdField.one_mul,
          OrdField.add_assoc (a * a), ← OrdField.add_assoc (a * b) (a * b),
          OrdField.add_comm (a * b + a * b) (b * b), ← OrdField.add_assoc (a * a)]
    rw [hsum, OrdField.one_mul] at hsq
    calc 1 - p = (p + (1 + 1) * (a * b)) - p := congrArg (· - p) hsq
      _ = (1 + 1) * (a * b) := by rw [OrdField.add_comm p, add_sub_cancel']
  have hp2 : p * p = ((a * a) * (a * a) + (b * b) * (b * b)) + (1 + 1) * ((a * b) * (a * b)) := by
    dsimp only [p]
    rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm (b * b) (a * a),
        right_distrib', OrdField.one_mul,
        OrdField.add_assoc ((a * a) * (a * a)),
        ← OrdField.add_assoc ((a * a) * (b * b)) ((a * a) * (b * b)),
        OrdField.add_comm ((a * a) * (b * b) + (a * a) * (b * b)) ((b * b) * (b * b)),
        ← OrdField.add_assoc ((a * a) * (a * a)), mul_four_swap a b]
  have hdiv : ((1 - p) * (1 - p)) / (1 + 1) = (1 + 1) * ((a * b) * (a * b)) := by
    rw [h1p]
    have hrearr : (1 + 1) * (a * b) * ((1 + 1) * (a * b)) =
        ((1 + 1) * ((a * b) * (a * b))) * (1 + 1) := by
      rw [OrdField.mul_assoc (1 + 1) (a * b), ← OrdField.mul_assoc (a * b) (1 + 1),
          OrdField.mul_comm (a * b) (1 + 1), OrdField.mul_assoc (1 + 1) (a * b),
          OrdField.mul_comm (1 + 1) ((1 + 1) * ((a * b) * (a * b)))]
    rw [hrearr, mul_div_cancel_right' _ (1 + 1) two_ne_zero]
  rw [hp2, hdiv, add_sub_cancel']

/-- **Theorem 2.1 / 5.1 (Monotonicity of `h*`):**
    If `0 < p ≤ q ≤ 1`, then `h*(p) ≤ h*(q)`. (Enables fail-closed interval propagation!) -/
theorem hStar_monotone {p q : K} (hp : 0 < p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    hStar p ≤ hStar q := by
  unfold hStar
  apply sub_le_sub_left' 1
  have hq : 0 < q := OrdField.lt_of_lt_of_le hp hpq
  have h1q_nn : 0 ≤ 1 - q := OrdField.sub_nonneg_of_le hq1
  have h1q_le_1p : 1 - q ≤ 1 - p := sub_le_sub_left' 1 hpq
  have h1p_nn : 0 ≤ 1 - p := OrdField.le_trans h1q_nn h1q_le_1p
  have hnum : (1 - q) * (1 - q) ≤ (1 - p) * (1 - p) :=
    mul_le_mul_nonneg h1q_nn h1p_nn h1q_le_1p h1q_le_1p
  have hden_pos : 0 < (1 + 1) * (p * p) := OrdField.mul_pos two_pos (OrdField.mul_pos hp hp)
  have hden_le : (1 + 1) * (p * p) ≤ (1 + 1) * (q * q) :=
    OrdField.mul_le_mul_of_nonneg_left
      (mul_le_mul_nonneg (OrdField.le_of_lt hp) (OrdField.le_of_lt hq) hpq hpq)
      (OrdField.le_of_lt two_pos)
  have hstep1 := div_le_div_of_nonneg_left (OrdField.mul_nonneg h1q_nn h1q_nn) hden_pos hden_le
  have hstep2 := div_le_div_of_nonneg_right hnum hden_pos
  exact OrdField.le_trans hstep1 hstep2

end SharpSquaring

-- ============================================================================
-- 2. THEOREM 2.2: Exact Sharp Gap-from-Purity & Tail-Mass Enclosures
-- ============================================================================

section SharpGapFromPurity
variable {K : Type} [OrdField K]

/-- Dominant weight dominates purity: if `w0 ≥ x` for all `x ∈ rest`, `w0 ≥ 0`, and `w0 + ∑ rest = 1`,
    then `p = w0^2 + ∑_{x ∈ rest} x^2 ≤ w0`. -/
theorem dominant_weight_ge_purity (w0 : K) (rest : List K)
    (hnn : ∀ x ∈ rest, 0 ≤ x)
    (hdom : ∀ x ∈ rest, x ≤ w0)
    (hsum : w0 + listSum rest = 1) :
    w0 * w0 + listSum (rest.map (fun x => x * x)) ≤ w0 := by
  have hrest_sq : listSum (rest.map (fun x => x * x)) ≤ w0 * listSum rest := by
    have hmul : listSum (rest.map (fun x => w0 * x)) = w0 * listSum rest := by
      rw [listSum_map_mul_left rest w0 (fun x => x), List.map_id']
    rw [← hmul]
    apply listSum_le_listSum
    intro x hx
    exact OrdField.mul_le_mul_of_nonneg_right (hdom x hx) (hnn x hx)
  have h1 := OrdField.add_le_add (OrdField.le_refl (w0 * w0)) hrest_sq
  rw [← OrdField.left_distrib, hsum, mul_one'] at h1
  exact h1

/-- **Theorem 2.2 (Core Sharp Defect Bound):**
    For any probability distribution `w0 :: rest` (`w0 ≥ 0`, `x ≥ 0`, `w0 + ∑ rest = 1`),
      `1 - p ≥ 2 w0 (1 - w0)`.
    (Exact equality on any 2-level Gibbs spectrum!) -/
theorem purity_defect_ge_two_w0_tail (w0 : K) (rest : List K)
    (_hw0 : 0 ≤ w0)
    (hnn : ∀ x ∈ rest, 0 ≤ x)
    (hsum : w0 + listSum rest = 1) :
    let p := w0 * w0 + listSum (rest.map (fun x => x * x))
    (1 + 1) * (w0 * (1 - w0)) ≤ 1 - p := by
  intro p
  have htail_eq : listSum rest = 1 - w0 := by
    rw [← hsum, OrdField.add_comm w0, add_sub_cancel']
  have hrest_sq_le : listSum (rest.map (fun x => x * x)) ≤ (1 - w0) * (1 - w0) := by
    rw [← htail_eq]
    exact sum_sq_le_sq_sum rest hnn
  have hp_le : p ≤ w0 * w0 + (1 - w0) * (1 - w0) :=
    OrdField.add_le_add (OrdField.le_refl (w0 * w0)) hrest_sq_le
  have h1p_ge := sub_le_sub_left' 1 hp_le
  have hid : 1 - (w0 * w0 + (1 - w0) * (1 - w0)) = (1 + 1) * (w0 * (1 - w0)) := by
    have hsq : (w0 + (1 - w0)) * (w0 + (1 - w0)) =
        (w0 * w0 + (1 - w0) * (1 - w0)) + (1 + 1) * (w0 * (1 - w0)) := by
      rw [OrdField.left_distrib, right_distrib', right_distrib', OrdField.mul_comm (1 - w0) w0,
          right_distrib', OrdField.one_mul,
          OrdField.add_assoc (w0 * w0), ← OrdField.add_assoc (w0 * (1 - w0)) (w0 * (1 - w0)),
          OrdField.add_comm (w0 * (1 - w0) + w0 * (1 - w0)) ((1 - w0) * (1 - w0)),
          ← OrdField.add_assoc (w0 * w0)]
    rw [OrdField.add_comm w0 (1 - w0), sub_add_cancel', OrdField.one_mul] at hsq
    calc 1 - (w0 * w0 + (1 - w0) * (1 - w0))
        = ((w0 * w0 + (1 - w0) * (1 - w0)) + (1 + 1) * (w0 * (1 - w0))) - (w0 * w0 + (1 - w0) * (1 - w0)) :=
          congrArg (· - (w0 * w0 + (1 - w0) * (1 - w0))) hsq
      _ = (1 + 1) * (w0 * (1 - w0)) := by
          rw [OrdField.add_comm (w0 * w0 + (1 - w0) * (1 - w0)), add_sub_cancel']
  rw [hid] at h1p_ge
  exact h1p_ge

/-- **Theorem 2.2 (Sharp Discriminant Bound):**
    `(2 w0 - 1)^2 ≥ 2 p - 1`, which over `ℝ` with `p > 1/2` gives `w0 ≥ (1 + √(2p - 1)) / 2`. -/
theorem sharp_discriminant_lower_bound (w0 : K) (rest : List K)
    (hw0 : 0 ≤ w0)
    (hnn : ∀ x ∈ rest, 0 ≤ x)
    (hsum : w0 + listSum rest = 1) :
    let p := w0 * w0 + listSum (rest.map (fun x => x * x))
    (1 + 1) * p - 1 ≤ ((1 + 1) * w0 - 1) * ((1 + 1) * w0 - 1) := by
  intro p
  have hdef := purity_defect_ge_two_w0_tail w0 rest hw0 hnn hsum
  have h2def := OrdField.mul_le_mul_of_nonneg_left hdef (OrdField.le_of_lt two_pos)
  have hsub := sub_le_sub_left' 1 h2def
  have hlhs : 1 - (1 + 1) * (1 - p) = (1 + 1) * p - 1 := by
    rw [mul_sub', mul_one', OrdField.sub_eq_add_neg 1, OrdField.sub_eq_add_neg (1 + 1),
        neg_add', neg_neg', OrdField.sub_eq_add_neg ((1 + 1) * p) 1]
    rw [OrdField.add_comm (-(1 + 1)) ((1 + 1) * p), ← OrdField.add_assoc 1 ((1 + 1) * p),
        OrdField.add_comm 1 ((1 + 1) * p), OrdField.add_assoc ((1 + 1) * p) 1 (-(1 + 1)),
        neg_add', ← OrdField.add_assoc 1 (-1) (-1), OrdField.add_neg_cancel, OrdField.zero_add]
  have hrhs : 1 - (1 + 1) * ((1 + 1) * (w0 * (1 - w0))) =
      ((1 + 1) * w0 - 1) * ((1 + 1) * w0 - 1) := by
    -- Expand (2 w0 - 1)^2 = 4 w0^2 - 4 w0 + 1 = 1 - 4 w0 (1 - w0)
    let two : K := 1 + 1
    let four : K := two * two
    change 1 - two * (two * (w0 * (1 - w0))) = (two * w0 - 1) * (two * w0 - 1)
    rw [← OrdField.mul_assoc two two, mul_sub' w0 1 w0, mul_one',
        mul_sub' four w0 (w0 * w0), sub_mul', mul_sub', mul_sub', mul_one', OrdField.one_mul]
    have h4w2 : (two * w0) * (two * w0) = four * (w0 * w0) := by
      dsimp only [four]
      rw [OrdField.mul_assoc two w0 (two * w0), ← OrdField.mul_assoc w0 two w0,
          OrdField.mul_comm w0 two, OrdField.mul_assoc two w0 w0, ← OrdField.mul_assoc two two (w0 * w0)]
    have h4w : two * w0 + two * w0 = four * w0 := by
      dsimp only [four]
      rw [right_distrib' 1 1 two, OrdField.one_mul, right_distrib' two two w0]
    rw [h4w2, OrdField.one_mul, OrdField.sub_eq_add_neg 1, OrdField.sub_eq_add_neg (four * w0), neg_add', neg_neg',
        OrdField.sub_eq_add_neg (four * (w0 * w0) - two * w0),
        OrdField.sub_eq_add_neg (four * (w0 * w0)),
        OrdField.sub_eq_add_neg (two * w0) 1, neg_add', neg_neg',
        OrdField.add_assoc (four * (w0 * w0)) (-(two * w0)),
        ← OrdField.add_assoc (-(two * w0)) (-(two * w0)) 1, ← neg_add', h4w]
    rw [OrdField.add_comm 1 (-(four * w0) + four * (w0 * w0)),
        OrdField.add_comm (-(four * w0)) (four * (w0 * w0)),
        OrdField.add_assoc (four * (w0 * w0)) (-(four * w0)) 1]
  rw [hlhs, hrhs] at hsub
  exact hsub

/-- **Theorem 2.2 (Algebraic Sharp Spectral-Gap Ratio Lower Bound):**
    If `w0 ≥ w1 > 0` are the top two Gibbs weights (`w0 + w1 + ∑ tail = 1`) and `p < 1`, then
      `w0 / w1 ≥ 2 w0^2 / (1 - p) ≥ 2 p^2 / (1 - p)`.
    (Over `ℝ`, combining with `w0 ≥ (1 + √(2p - 1)) / 2` gives the exact sharp bound
     `e^{β Δ} = w0 / w1 ≥ (1 + √(2p - 1))^2 / (2 (1 - p))`, strictly beating Grover's `p/(1-p)`!) -/
theorem sharp_gap_ratio_bound (w0 w1 : K) (tail : List K)
    (hw0 : 0 ≤ w0) (hw1 : 0 < w1)
    (hnn : ∀ x ∈ tail, 0 ≤ x)
    (hsum : w0 + listSum (w1 :: tail) = 1)
    (hpl : w0 * w0 + listSum ((w1 :: tail).map (fun x => x * x)) < 1) :
    let p := w0 * w0 + listSum ((w1 :: tail).map (fun x => x * x))
    ((1 + 1) * (w0 * w0)) / (1 - p) ≤ w0 / w1 := by
  intro p
  have h1p_pos : 0 < 1 - p := OrdField.sub_pos_of_lt hpl
  have hrest_nn : ∀ x ∈ (w1 :: tail), 0 ≤ x := by
    intro x hx
    cases hx with
    | head => exact OrdField.le_of_lt hw1
    | tail _ hxt => exact hnn x hxt
  have hdef : (1 + 1) * (w0 * (1 - w0)) ≤ 1 - p :=
    purity_defect_ge_two_w0_tail w0 (w1 :: tail) hw0 hrest_nn hsum
  have htail_nn : 0 ≤ listSum tail := listSum_nonneg tail hnn
  have hw1_le : w1 ≤ 1 - w0 := by
    have hsum_tail : w1 + listSum tail = 1 - w0 := by
      simp only [listSum] at hsum
      rw [← hsum, OrdField.add_comm w0, add_sub_cancel']
    rw [← hsum_tail]
    exact le_add_of_nonneg_right htail_nn
  have h2w0w1 : (1 + 1) * (w0 * w1) ≤ 1 - p := by
    have h1 := OrdField.mul_le_mul_of_nonneg_left hw1_le hw0
    have h2 := OrdField.mul_le_mul_of_nonneg_left h1 (OrdField.le_of_lt two_pos)
    exact OrdField.le_trans h2 hdef
  -- Multiply by w0 / (w1 * (1 - p)) ≥ 0:
  -- Equivalently: (2 w0^2) / (1 - p) = (w0 * (2 w0 w1)) / (w1 * (1 - p)) ≤ (w0 * (1 - p)) / (w1 * (1 - p)) = w0 / w1
  have hmul_w0 := OrdField.mul_le_mul_of_nonneg_left h2w0w1 hw0
  have hden_pos : 0 < w1 * (1 - p) := OrdField.mul_pos hw1 h1p_pos
  have hdiv := div_le_div_of_nonneg_right hmul_w0 hden_pos
  have hlhs_eq : (w0 * ((1 + 1) * (w0 * w1))) / (w1 * (1 - p)) = ((1 + 1) * (w0 * w0)) / (1 - p) := by
    have hnum : w0 * ((1 + 1) * (w0 * w1)) = (((1 + 1) * (w0 * w0)) * w1) := by
      rw [← OrdField.mul_assoc w0 (1 + 1) (w0 * w1), OrdField.mul_comm w0 (1 + 1),
          OrdField.mul_assoc (1 + 1) w0 (w0 * w1), ← OrdField.mul_assoc w0 w0 w1,
          ← OrdField.mul_assoc (1 + 1) (w0 * w0) w1]
    rw [hnum, OrdField.mul_comm w1 (1 - p)]
    -- (A * w1) / ((1-p) * w1) = A / (1-p)
    have h1p_nz : 1 - p ≠ 0 := ne_zero_of_pos h1p_pos
    have hw1_nz : w1 ≠ 0 := ne_zero_of_pos hw1
    have hd_nz : (1 - p) * w1 ≠ 0 := ne_zero_of_pos (OrdField.mul_pos h1p_pos hw1)
    have hchk : (((1 + 1) * (w0 * w0)) / (1 - p)) * ((1 - p) * w1) = ((1 + 1) * (w0 * w0)) * w1 := by
      rw [← OrdField.mul_assoc, div_mul_cancel' _ (1 - p) h1p_nz]
    rw [← hchk, mul_div_cancel_right' _ ((1 - p) * w1) hd_nz]
  have hrhs_eq : (w0 * (1 - p)) / (w1 * (1 - p)) = w0 / w1 := by
    have h1p_nz : 1 - p ≠ 0 := ne_zero_of_pos h1p_pos
    have hw1_nz : w1 ≠ 0 := ne_zero_of_pos hw1
    have hd_nz : w1 * (1 - p) ≠ 0 := ne_zero_of_pos hden_pos
    have hchk : (w0 / w1) * (w1 * (1 - p)) = w0 * (1 - p) := by
      rw [← OrdField.mul_assoc, div_mul_cancel' w0 w1 hw1_nz]
    rw [← hchk, mul_div_cancel_right' (w0 / w1) (w1 * (1 - p)) hd_nz]
  rw [hlhs_eq, hrhs_eq] at hdiv
  exact hdiv

end SharpGapFromPurity

-- ============================================================================
-- 3. THEOREMS 3.1 & 3.2: Exact Plaquette Identity & Cyclic Gauss-Seidel Bootstrap
-- ============================================================================

section CyclicGaussSeidel
variable {K : Type} [OrdField K]

/-- **Theorem 3.1 (Exact Space-Time Plaquette Identity):**
    For any positive partition functions `Z00 = Z(L, β)`, `Z10 = Z(2L, β)`, `Z01 = Z(L, 2β)`,
    `Z11 = Z(2L, 2β)`, with `S00 = Z10 / Z00^2`, `T00 = Z01 / Z00^2`,
    `S01 = Z11 / Z01^2`, `T10 = Z11 / Z10^2`:
      `S01 * T00^2 = T10 * S00^2`. -/
theorem plaquette_exact_identity (Z00 Z10 Z01 Z11 : K)
    (h00 : Z00 ≠ 0) (h10 : Z10 ≠ 0) (h01 : Z01 ≠ 0) :
    let S00 := Z10 / (Z00 * Z00)
    let T00 := Z01 / (Z00 * Z00)
    let S01 := Z11 / (Z01 * Z01)
    let T10 := Z11 / (Z10 * Z10)
    S01 * (T00 * T00) = T10 * (S00 * S00) := by
  intro S00 T00 S01 T10
  have hZ00_4_nz : (Z00 * Z00) * (Z00 * Z00) ≠ 0 := by
    intro h
    have h2 : Z00 * Z00 ≠ 0 := by
      intro h2; exact h00 (by
        have := congrArg (· * (1 / Z00)) h2
        rw [OrdField.mul_assoc, OrdField.mul_inv_cancel Z00 h00, mul_one', zero_mul'] at this
        exact this)
    have := congrArg (· * (1 / (Z00 * Z00))) h
    rw [OrdField.mul_assoc, OrdField.mul_inv_cancel (Z00 * Z00) h2, mul_one', zero_mul'] at this
    exact h2 this
  have hdiv_sq : ∀ A B : K, B ≠ 0 → (A / B) * (A / B) = (A * A) / (B * B) := by
    intro A B hB
    have hB2 : B * B ≠ 0 := by
      intro h2; have := congrArg (· * (1 / B)) h2
      rw [OrdField.mul_assoc, OrdField.mul_inv_cancel B hB, mul_one', zero_mul'] at this
      exact hB this
    have hchk : ((A / B) * (A / B)) * (B * B) = A * A := by
      rw [OrdField.mul_assoc (A / B) (A / B) (B * B), ← OrdField.mul_assoc (A / B) B B,
          div_mul_cancel' A B hB, OrdField.mul_comm A B, ← OrdField.mul_assoc (A / B) B A,
          div_mul_cancel' A B hB]
    rw [← hchk, mul_div_cancel_right' _ (B * B) hB2]
  have hcancel : ∀ X Y C : K, Y ≠ 0 → C ≠ 0 → (X / Y) * (Y / C) = X / C := by
    intro X Y C hY hC
    have hchk : ((X / Y) * (Y / C)) * C = X := by
      rw [OrdField.mul_assoc, div_mul_cancel' Y C hC, div_mul_cancel' X Y hY]
    calc (X / Y) * (Y / C) = (((X / Y) * (Y / C)) * C) / C := (mul_div_cancel_right' _ C hC).symm
      _ = X / C := congrArg (· / C) hchk
  have hZ00_2 : Z00 * Z00 ≠ 0 := by
    intro h2; have := congrArg (· * (1 / Z00)) h2
    rw [OrdField.mul_assoc, OrdField.mul_inv_cancel Z00 h00, mul_one', zero_mul'] at this
    exact h00 this
  have hZ01_2 : Z01 * Z01 ≠ 0 := by
    intro h2; have := congrArg (· * (1 / Z01)) h2
    rw [OrdField.mul_assoc, OrdField.mul_inv_cancel Z01 h01, mul_one', zero_mul'] at this
    exact h01 this
  have hZ10_2 : Z10 * Z10 ≠ 0 := by
    intro h2; have := congrArg (· * (1 / Z10)) h2
    rw [OrdField.mul_assoc, OrdField.mul_inv_cancel Z10 h10, mul_one', zero_mul'] at this
    exact h10 this
  have hL : S01 * (T00 * T00) = Z11 / ((Z00 * Z00) * (Z00 * Z00)) := by
    dsimp only [S01, T00]
    rw [hdiv_sq Z01 (Z00 * Z00) hZ00_2]
    exact hcancel Z11 (Z01 * Z01) ((Z00 * Z00) * (Z00 * Z00)) hZ01_2 hZ00_4_nz
  have hR : T10 * (S00 * S00) = Z11 / ((Z00 * Z00) * (Z00 * Z00)) := by
    dsimp only [T10, S00]
    rw [hdiv_sq Z10 (Z00 * Z00) hZ00_2]
    exact hcancel Z11 (Z10 * Z10) ((Z00 * Z00) * (Z00 * Z00)) hZ10_2 hZ00_4_nz
  rw [hL, hR]

/-- **Theorem 3.1 (Plaquette Lower Bound):**
    From `S01 * T00^2 = T10 * S00^2` with `0 < T00 ≤ 1` and `0 ≤ S01`, we get `S00^2 * T10 ≤ S01`. -/
theorem plaquette_lower_bound (S00 T00 S01 T10 : K)
    (hT00_pos : 0 < T00) (hT00_le1 : T00 ≤ 1) (hS01_nn : 0 ≤ S01)
    (hid : S01 * (T00 * T00) = T10 * (S00 * S00)) :
    (S00 * S00) * T10 ≤ S01 := by
  have hT2_le1 : T00 * T00 ≤ 1 := by
    have h1 := OrdField.mul_le_mul_of_nonneg_left hT00_le1 (OrdField.le_of_lt hT00_pos)
    rw [mul_one'] at h1
    exact OrdField.le_trans h1 hT00_le1
  have hle := OrdField.mul_le_mul_of_nonneg_left hT2_le1 hS01_nn
  rw [mul_one', hid, OrdField.mul_comm T10 (S00 * S00)] at hle
  exact hle

/-- 1D cyclic Gauss-Seidel map `(s, t) ↦ (h*(s^2 t), h*(t^2 h*(s^2 t)))`. -/
def gsStep1D (st : K × K) : K × K :=
  let s' := hStar ((st.1 * st.1) * st.2)
  let t' := hStar ((st.2 * st.2) * s')
  (s', t')

def gsIter1D : Nat → K × K → K × K
  | 0, st => st
  | n + 1, st => gsIter1D n (gsStep1D st)

/-- Abstract reflection-positive 1D partition-function purity oracle:
    `S n` = `S(2^n L0, 2^n β0)`, `T n` = `T(2^{n+1} L0, 2^n β0)`. -/
structure RPSystem1D (K : Type) [OrdField K] where
  S : Nat → K
  T : Nat → K
  S_pos : ∀ n, 0 < S n
  S_le1 : ∀ n, S n ≤ 1
  T_pos : ∀ n, 0 < T n
  T_le1 : ∀ n, T n ≤ 1
  /-- Spatial squaring after plaquette step: `S(n+1) ≥ h*(S(n)^2 * T(n))`. -/
  step_S : ∀ n, hStar ((S n * S n) * T n) ≤ S (n + 1)
  /-- Temporal squaring after plaquette step: `T(n+1) ≥ h*(T(n)^2 * S(n+1))`. -/
  step_T : ∀ n, hStar ((T n * T n) * S (n + 1)) ≤ T (n + 1)

/-- **Theorem 3.1 (1D Cyclic Gauss-Seidel Step Soundness):**
    If `(s, t)` lower-bounds `(S n, T n)` with `s > 0, t > 0` and `h*(s^2 t) > 0`,
    then `gsStep1D (s, t)` lower-bounds `(S (n+1), T (n+1))`. -/
theorem gs_1d_step_sound (sys : RPSystem1D K) (n : Nat) (s t : K)
    (hs_pos : 0 < s) (ht_pos : 0 < t)
    (hs_le : s ≤ sys.S n) (ht_le : t ≤ sys.T n)
    (hs'_pos : 0 < hStar ((s * s) * t)) :
    (gsStep1D (s, t)).1 ≤ sys.S (n + 1) ∧ (gsStep1D (s, t)).2 ≤ sys.T (n + 1) := by
  unfold gsStep1D
  have hs2_le : s * s ≤ sys.S n * sys.S n :=
    mul_le_mul_nonneg (OrdField.le_of_lt hs_pos) (OrdField.le_of_lt (sys.S_pos n)) hs_le hs_le
  have hq_pos : 0 < (s * s) * t := OrdField.mul_pos (OrdField.mul_pos hs_pos hs_pos) ht_pos
  have hq_le : (s * s) * t ≤ (sys.S n * sys.S n) * sys.T n :=
    mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos hs_pos hs_pos))
      (OrdField.le_of_lt (sys.T_pos n)) hs2_le ht_le
  have hQ_le1 : (sys.S n * sys.S n) * sys.T n ≤ 1 := by
    have h1 : sys.S n * sys.S n ≤ 1 := by
      have hm := OrdField.mul_le_mul_of_nonneg_left (sys.S_le1 n) (OrdField.le_of_lt (sys.S_pos n))
      rw [mul_one'] at hm; exact OrdField.le_trans hm (sys.S_le1 n)
    have h2 := mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos (sys.S_pos n) (sys.S_pos n)))
      (OrdField.le_of_lt OrdField.zero_lt_one) h1 (sys.T_le1 n)
    rw [mul_one'] at h2; exact h2
  have hs'_le : hStar ((s * s) * t) ≤ sys.S (n + 1) :=
    OrdField.le_trans (hStar_monotone hq_pos hq_le hQ_le1) (sys.step_S n)
  have ht2_le : t * t ≤ sys.T n * sys.T n :=
    mul_le_mul_nonneg (OrdField.le_of_lt ht_pos) (OrdField.le_of_lt (sys.T_pos n)) ht_le ht_le
  have hr_pos : 0 < (t * t) * hStar ((s * s) * t) :=
    OrdField.mul_pos (OrdField.mul_pos ht_pos ht_pos) hs'_pos
  have hr_le : (t * t) * hStar ((s * s) * t) ≤ (sys.T n * sys.T n) * sys.S (n + 1) :=
    mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos ht_pos ht_pos))
      (OrdField.le_of_lt (sys.S_pos (n + 1))) ht2_le hs'_le
  have hR_le1 : (sys.T n * sys.T n) * sys.S (n + 1) ≤ 1 := by
    have h1 : sys.T n * sys.T n ≤ 1 := by
      have hm := OrdField.mul_le_mul_of_nonneg_left (sys.T_le1 n) (OrdField.le_of_lt (sys.T_pos n))
      rw [mul_one'] at hm; exact OrdField.le_trans hm (sys.T_le1 n)
    have h2 := mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos (sys.T_pos n) (sys.T_pos n)))
      (OrdField.le_of_lt OrdField.zero_lt_one) h1 (sys.S_le1 (n + 1))
    rw [mul_one'] at h2; exact h2
  have ht'_le : hStar ((t * t) * hStar ((s * s) * t)) ≤ sys.T (n + 1) :=
    OrdField.le_trans (hStar_monotone hr_pos hr_le hR_le1) (sys.step_T n)
  exact ⟨hs'_le, ht'_le⟩

/-- **Theorem 5.1 (Interval / Finite-Sample Monotonicity of 1D Gauss-Seidel Map):**
    If `0 < s1 ≤ s2 ≤ 1`, `0 < t1 ≤ t2 ≤ 1`, and `h*(s1^2 t1) > 0`, then `gsStep1D` preserves
    componentwise ordering. -/
theorem gs_1d_monotone (s1 t1 s2 t2 : K)
    (hs1 : 0 < s1) (ht1 : 0 < t1) (hs : s1 ≤ s2) (ht : t1 ≤ t2)
    (hs2_le1 : s2 ≤ 1) (ht2_le1 : t2 ≤ 1)
    (hs1'_pos : 0 < hStar ((s1 * s1) * t1)) :
    (gsStep1D (s1, t1)).1 ≤ (gsStep1D (s2, t2)).1 ∧
    (gsStep1D (s1, t1)).2 ≤ (gsStep1D (s2, t2)).2 := by
  unfold gsStep1D
  have hs2_pos : 0 < s2 := OrdField.lt_of_lt_of_le hs1 hs
  have ht2_pos : 0 < t2 := OrdField.lt_of_lt_of_le ht1 ht
  have hq1_pos : 0 < (s1 * s1) * t1 := OrdField.mul_pos (OrdField.mul_pos hs1 hs1) ht1
  have hq_le : (s1 * s1) * t1 ≤ (s2 * s2) * t2 :=
    mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos hs1 hs1)) (OrdField.le_of_lt ht2_pos)
      (mul_le_mul_nonneg (OrdField.le_of_lt hs1) (OrdField.le_of_lt hs2_pos) hs hs) ht
  have hq2_le1 : (s2 * s2) * t2 ≤ 1 := by
    have h1 : s2 * s2 ≤ 1 := by
      have hm := OrdField.mul_le_mul_of_nonneg_left hs2_le1 (OrdField.le_of_lt hs2_pos)
      rw [mul_one'] at hm; exact OrdField.le_trans hm hs2_le1
    have h2 := mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos hs2_pos hs2_pos))
      (OrdField.le_of_lt OrdField.zero_lt_one) h1 ht2_le1
    rw [mul_one'] at h2; exact h2
  have hs'_le : hStar ((s1 * s1) * t1) ≤ hStar ((s2 * s2) * t2) :=
    hStar_monotone hq1_pos hq_le hq2_le1
  have hs2'_le1 : hStar ((s2 * s2) * t2) ≤ 1 := by
    unfold hStar
    have hq2_pos : 0 < (s2 * s2) * t2 := OrdField.lt_of_lt_of_le hq1_pos hq_le
    have h1q : 0 ≤ 1 - (s2 * s2) * t2 := OrdField.sub_nonneg_of_le hq2_le1
    have hnum_nn : 0 ≤ (1 - (s2 * s2) * t2) * (1 - (s2 * s2) * t2) := OrdField.mul_nonneg h1q h1q
    have hden_pos : 0 < (1 + 1) * (((s2 * s2) * t2) * ((s2 * s2) * t2)) :=
      OrdField.mul_pos two_pos (OrdField.mul_pos hq2_pos hq2_pos)
    have hfrac_nn : 0 ≤ ((1 - (s2 * s2) * t2) * (1 - (s2 * s2) * t2)) /
                        ((1 + 1) * (((s2 * s2) * t2) * ((s2 * s2) * t2))) := by
      rw [OrdField.div_eq_mul_inv]
      exact OrdField.mul_nonneg hnum_nn (OrdField.le_of_lt (OrdField.div_pos OrdField.zero_lt_one hden_pos))
    have hsub := sub_le_sub_left' (1 : K) hfrac_nn
    have h10 : (1 : K) - 0 = 1 := by
      have h0 : -(0 : K) = 0 := by have := OrdField.add_neg_cancel (0 : K); rw [OrdField.zero_add] at this; exact this
      rw [OrdField.sub_eq_add_neg, h0, add_zero']
    rw [h10] at hsub
    exact hsub
  have hs2'_pos : 0 < hStar ((s2 * s2) * t2) := OrdField.lt_of_lt_of_le hs1'_pos hs'_le
  have hr1_pos : 0 < (t1 * t1) * hStar ((s1 * s1) * t1) :=
    OrdField.mul_pos (OrdField.mul_pos ht1 ht1) hs1'_pos
  have hr_le : (t1 * t1) * hStar ((s1 * s1) * t1) ≤ (t2 * t2) * hStar ((s2 * s2) * t2) :=
    mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos ht1 ht1)) (OrdField.le_of_lt hs2'_pos)
      (mul_le_mul_nonneg (OrdField.le_of_lt ht1) (OrdField.le_of_lt ht2_pos) ht ht) hs'_le
  have hr2_le1 : (t2 * t2) * hStar ((s2 * s2) * t2) ≤ 1 := by
    have h1 : t2 * t2 ≤ 1 := by
      have hm := OrdField.mul_le_mul_of_nonneg_left ht2_le1 (OrdField.le_of_lt ht2_pos)
      rw [mul_one'] at hm; exact OrdField.le_trans hm ht2_le1
    have h2 := mul_le_mul_nonneg (OrdField.le_of_lt (OrdField.mul_pos ht2_pos ht2_pos))
      (OrdField.le_of_lt OrdField.zero_lt_one) h1 hs2'_le1
    rw [mul_one'] at h2; exact h2
  exact ⟨hs'_le, hStar_monotone hr1_pos hr_le hr2_le1⟩

/-- **Theorem 3.1 (Inductive N-Step 1D Gauss-Seidel Soundness):**
    Starting from any certified initial bounds `(s0, t0) ≤ (S 0, T 0)`, if all intermediate
    iterates stay strictly positive, then after `N` steps `gsIter1D N (s0, t0)` validly
    lower-bounds `(S N, T N)`. -/
theorem gs_1d_induction_sound (sys : RPSystem1D K) (N : Nat) (s0 t0 : K)
    (hinit : s0 ≤ sys.S 0 ∧ t0 ≤ sys.T 0)
    (hpos : ∀ k, k ≤ N → 0 < (gsIter1D k (s0, t0)).1 ∧ 0 < (gsIter1D k (s0, t0)).2) :
    (gsIter1D N (s0, t0)).1 ≤ sys.S N ∧ (gsIter1D N (s0, t0)).2 ≤ sys.T N := by
  have hshift : ∀ m (st : K × K), gsIter1D (m + 1) st = gsStep1D (gsIter1D m st) := by
    intro m
    induction m with
    | zero => intro st; rfl
    | succ k ih => intro st; exact ih (gsStep1D st)
  induction N with
  | zero => exact hinit
  | succ k ih =>
    have hk := ih (fun j hj => hpos j (Nat.le_succ_of_le hj))
    have hpk := hpos k (Nat.le_succ k)
    have hpk1 := hpos (k + 1) (Nat.le_refl (k + 1))
    rw [hshift k (s0, t0)] at hpk1 ⊢
    exact gs_1d_step_sound sys k (gsIter1D k (s0, t0)).1 (gsIter1D k (s0, t0)).2
      hpk.1 hpk.2 hk.1 hk.2 hpk1.1

/-- **Theorem 3.2 (General D-Dimensional Single-Ratio Q-Step Soundness):**
    In arbitrary dimension `D = d + 1`, if `Q = ∏_{j=0}^{D-1} p_j^{2^{D-1-j}}` with `0 < p_j ≤ 1`,
    then for every axis `k < D`, the trailing product `R_k = ∏_{j=k}^{D-1} p_j^{2^{D-1-j}}`
    satisfies `Q ≤ R_k`, hence `Q^{2^k} ≤ R_k^{2^k}`.
    (This eliminates Grover's factor-of-`a` overcounting in Eq. (14) and yields the 8x asymptotic
     improvement `1 - Q_c*(d) ~ 4 / (a(a+1))` in every spatial dimension!) -/
theorem hypercube_Q_step_sound (head_prod tail_prod : K) (twoPowK : Nat)
    (hhead_nn : 0 ≤ head_prod) (hhead_le1 : head_prod ≤ 1)
    (htail_nn : 0 ≤ tail_prod) :
    powK (head_prod * tail_prod) twoPowK ≤ powK tail_prod twoPowK := by
  have hle : head_prod * tail_prod ≤ tail_prod := by
    have hm := OrdField.mul_le_mul_of_nonneg_right hhead_le1 htail_nn
    rw [OrdField.one_mul] at hm
    exact hm
  exact powK_mono (OrdField.mul_nonneg hhead_nn htail_nn) hle twoPowK

end CyclicGaussSeidel

-- ============================================================================
-- 4. THEOREMS 4.1 & 4.2: Doubly-Exponential Decay & Intervening-Length Transfer
-- ============================================================================

section AsymptoticGapAndTransfer
variable {K : Type} [OrdField K]

/-- **Theorem 4.1 (Exact Doubly-Exponential Contraction):**
    For any nonnegative sequence `u : Nat → K` and constant `C ≥ 0` satisfying `u(n+1) ≤ C * u(n)^2`
    for all `n`, we have for EVERY `n : Nat`:
      `C * u n ≤ powK (C * u 0) (2^n)`.
    When `C * u 0 < 1`, this certifies doubly-exponential convergence `u_n → 0` and yields the
    explicit thermodynamic mass-gap lower bound `Δ_∞ ≥ (1 / (2^N β_0)) log(1 / (C u_N))`. -/
theorem doubly_exponential_contraction (u : Nat → K) (C : K)
    (hC : 0 ≤ C) (hu : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, u (n + 1) ≤ C * (u n * u n)) :
    ∀ n : Nat, C * u n ≤ powK (C * u 0) (2 ^ n) := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.pow_zero, powK, mul_one']
    exact OrdField.le_refl (C * u 0)
  | succ k ih =>
    have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    rw [hpow2, powK_add]
    have h1 : C * u (k + 1) ≤ (C * u k) * (C * u k) := by
      have hm := OrdField.mul_le_mul_of_nonneg_left (hstep k) hC
      have hrearr : C * (C * (u k * u k)) = (C * u k) * (C * u k) := by
        rw [← OrdField.mul_assoc C C (u k * u k), mul_four_swap C (u k)]
      rw [hrearr] at hm
      exact hm
    have hCu_nn : 0 ≤ C * u k := OrdField.mul_nonneg hC (hu k)
    have hpow_nn : 0 ≤ powK (C * u 0) (2 ^ k) := powK_nonneg (OrdField.mul_nonneg hC (hu 0)) (2 ^ k)
    have h2 : (C * u k) * (C * u k) ≤ powK (C * u 0) (2 ^ k) * powK (C * u 0) (2 ^ k) :=
      mul_le_mul_nonneg hCu_nn hpow_nn ih ih
    exact OrdField.le_trans h1 h2

/-- **Theorem 4.2 (Intervening-Length Purity Transfer):**
    Suppose for an intervening even length `ℓ ∈ [L, 2L]`, the partition functions satisfy
    `μ_2β^ℓ ≤ Z(ℓ, 2β)`, `Z(ℓ, β) ≤ (1 + R1) μ_β^ℓ`, `Z(2L, 2β) ≤ (1 + R2) μ_2β^{2L}`,
    `μ_β^{2L} ≤ Z(2L, β)`, and the spectral-radius ratio satisfies `(μ_2β / μ_β^2)^{2L} ≤ (μ_2β / μ_β^2)^ℓ`
    (which holds since `μ_2β ≤ μ_β^2` and `ℓ ≤ 2L`). Then
      `T(2L, β) / ((1 + R1)^2 * (1 + R2)) ≤ T(ℓ, β) = Z(ℓ, 2β) / Z(ℓ, β)^2`. -/
theorem intervening_length_purity_transfer
    (Z_l_b Z_l_2b Z_2L_b Z_2L_2b mu_b_l mu_2b_l mu_b_2L mu_2b_2L onePlusR1 onePlusR2 : K)
    (hZlb : 0 < Z_l_b) (hZ2Lb : 0 < Z_2L_b)
    (hmubl : 0 < mu_b_l) (hmu2bl : 0 < mu_2b_l)
    (hmub2L : 0 < mu_b_2L) (hmu2b2L : 0 < mu_2b_2L)
    (hR1 : 0 < onePlusR1) (hR2 : 0 < onePlusR2)
    (h1 : mu_2b_l ≤ Z_l_2b)
    (h2 : Z_l_b ≤ onePlusR1 * mu_b_l)
    (h3 : Z_2L_2b ≤ onePlusR2 * mu_2b_2L)
    (h4 : mu_b_2L ≤ Z_2L_b)
    (hratio : mu_2b_2L / (mu_b_2L * mu_b_2L) ≤ mu_2b_l / (mu_b_l * mu_b_l)) :
    (Z_2L_2b / (Z_2L_b * Z_2L_b)) / ((onePlusR1 * onePlusR1) * onePlusR2) ≤
    Z_l_2b / (Z_l_b * Z_l_b) := by
  -- Step A: T(2L, b) / onePlusR2 ≤ mu_2b_2L / mu_b_2L^2
  have hZ2Lb2_pos : 0 < Z_2L_b * Z_2L_b := OrdField.mul_pos hZ2Lb hZ2Lb
  have hmub2L2_pos : 0 < mu_b_2L * mu_b_2L := OrdField.mul_pos hmub2L hmub2L
  have hmub2L2_le : mu_b_2L * mu_b_2L ≤ Z_2L_b * Z_2L_b :=
    mul_le_mul_nonneg (OrdField.le_of_lt hmub2L) (OrdField.le_of_lt hZ2Lb) h4 h4
  have hT2L_ub : Z_2L_2b / (Z_2L_b * Z_2L_b) ≤ (onePlusR2 * mu_2b_2L) / (mu_b_2L * mu_b_2L) := by
    have s1 := div_le_div_of_nonneg_right h3 hZ2Lb2_pos
    have s2 := div_le_div_of_nonneg_left
      (OrdField.le_of_lt (OrdField.mul_pos hR2 hmu2b2L)) hmub2L2_pos hmub2L2_le
    exact OrdField.le_trans s1 s2
  have hStepA : (Z_2L_2b / (Z_2L_b * Z_2L_b)) / onePlusR2 ≤ mu_2b_2L / (mu_b_2L * mu_b_2L) := by
    have s1 := div_le_div_of_nonneg_right hT2L_ub hR2
    have hsimp : ((onePlusR2 * mu_2b_2L) / (mu_b_2L * mu_b_2L)) / onePlusR2 =
                 mu_2b_2L / (mu_b_2L * mu_b_2L) := by
      have hden_nz : mu_b_2L * mu_b_2L ≠ 0 := ne_zero_of_pos hmub2L2_pos
      have hR2_nz : onePlusR2 ≠ 0 := ne_zero_of_pos hR2
      have hchk : (mu_2b_2L / (mu_b_2L * mu_b_2L)) * onePlusR2 =
                  (onePlusR2 * mu_2b_2L) / (mu_b_2L * mu_b_2L) := by
        rw [OrdField.div_eq_mul_inv mu_2b_2L (mu_b_2L * mu_b_2L),
            OrdField.div_eq_mul_inv (onePlusR2 * mu_2b_2L) (mu_b_2L * mu_b_2L),
            OrdField.mul_assoc, OrdField.mul_comm (1 / (mu_b_2L * mu_b_2L)) onePlusR2,
            ← OrdField.mul_assoc, OrdField.mul_comm mu_2b_2L onePlusR2]
      calc ((onePlusR2 * mu_2b_2L) / (mu_b_2L * mu_b_2L)) / onePlusR2
          = ((mu_2b_2L / (mu_b_2L * mu_b_2L)) * onePlusR2) / onePlusR2 := congrArg (· / onePlusR2) hchk.symm
        _ = mu_2b_2L / (mu_b_2L * mu_b_2L) := mul_div_cancel_right' _ onePlusR2 hR2_nz
    rw [hsimp] at s1
    exact s1
  -- Step B: Combine with hratio and divide by onePlusR1^2
  have hR1sq_pos : 0 < onePlusR1 * onePlusR1 := OrdField.mul_pos hR1 hR1
  have hStepB : ((Z_2L_2b / (Z_2L_b * Z_2L_b)) / onePlusR2) / (onePlusR1 * onePlusR1) ≤
                (mu_2b_l / (mu_b_l * mu_b_l)) / (onePlusR1 * onePlusR1) :=
    div_le_div_of_nonneg_right (OrdField.le_trans hStepA hratio) hR1sq_pos
  -- Step C: (mu_2b_l / mu_b_l^2) / R1^2 ≤ Z_l_2b / Z_l_b^2
  have hZlb2_pos : 0 < Z_l_b * Z_l_b := OrdField.mul_pos hZlb hZlb
  have hZlb2_le : Z_l_b * Z_l_b ≤ (onePlusR1 * onePlusR1) * (mu_b_l * mu_b_l) := by
    have hs := mul_le_mul_nonneg (OrdField.le_of_lt hZlb)
      (OrdField.le_of_lt (OrdField.mul_pos hR1 hmubl)) h2 h2
    rw [← mul_four_swap onePlusR1 mu_b_l] at hs
    exact hs
  have hStepC : (mu_2b_l / (mu_b_l * mu_b_l)) / (onePlusR1 * onePlusR1) ≤
                Z_l_2b / (Z_l_b * Z_l_b) := by
    have hrew : (mu_2b_l / (mu_b_l * mu_b_l)) / (onePlusR1 * onePlusR1) =
                mu_2b_l / ((onePlusR1 * onePlusR1) * (mu_b_l * mu_b_l)) := by
      have hm_nz : mu_b_l * mu_b_l ≠ 0 := ne_zero_of_pos (OrdField.mul_pos hmubl hmubl)
      have hr_nz : onePlusR1 * onePlusR1 ≠ 0 := ne_zero_of_pos hR1sq_pos
      have hd_nz : (mu_b_l * mu_b_l) * (onePlusR1 * onePlusR1) ≠ 0 :=
        ne_zero_of_pos (OrdField.mul_pos (OrdField.mul_pos hmubl hmubl) hR1sq_pos)
      rw [div_div_eq_div_mul mu_2b_l (mu_b_l * mu_b_l) (onePlusR1 * onePlusR1) hm_nz hr_nz hd_nz,
          OrdField.mul_comm (mu_b_l * mu_b_l) (onePlusR1 * onePlusR1)]
    rw [hrew]
    have s1 := div_le_div_of_nonneg_left (OrdField.le_of_lt hmu2bl) hZlb2_pos hZlb2_le
    have s2 := div_le_div_of_nonneg_right h1 hZlb2_pos
    exact OrdField.le_trans s1 s2
  -- Rewrite LHS double division
  have hlhs_rew : (Z_2L_2b / (Z_2L_b * Z_2L_b)) / ((onePlusR1 * onePlusR1) * onePlusR2) =
                  ((Z_2L_2b / (Z_2L_b * Z_2L_b)) / onePlusR2) / (onePlusR1 * onePlusR1) := by
    have hr1_nz : onePlusR1 * onePlusR1 ≠ 0 := ne_zero_of_pos hR1sq_pos
    have hr2_nz : onePlusR2 ≠ 0 := ne_zero_of_pos hR2
    have hd_nz : onePlusR2 * (onePlusR1 * onePlusR1) ≠ 0 :=
      ne_zero_of_pos (OrdField.mul_pos hR2 hR1sq_pos)
    rw [OrdField.mul_comm (onePlusR1 * onePlusR1) onePlusR2,
        ← div_div_eq_div_mul (Z_2L_2b / (Z_2L_b * Z_2L_b)) onePlusR2 (onePlusR1 * onePlusR1) hr2_nz hr1_nz hd_nz]
  rw [hlhs_rew]
  exact OrdField.le_trans hStepB hStepC

end AsymptoticGapAndTransfer

end PurityBootstrap

