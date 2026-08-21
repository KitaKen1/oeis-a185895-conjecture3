import FormalConjectures.OEIS.«185895»

/-!
# OEIS A185895: Gauss congruence

This file proves the exact `OeisA185895.conjecture3` proposition without invoking the upstream
open theorem.  It first rewrites the rational-coefficient-and-floor definition as a signed
multinomial sum, proves the prime reduction in `ZMod (p ^ k)`, and reindexes the surviving shapes.
-/

open Polynomial

namespace OeisA185895Proof

private lemma prod_monomials (s : Finset ℕ) :
    ∏ k ∈ s, (C (1 / (k.factorial : ℚ)) * X ^ k) =
      C (∏ k ∈ s, (1 / (k.factorial : ℚ))) * X ^ (∑ k ∈ s, k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk, ih]
      simp only [Finset.prod_insert hk, C_mul, pow_add]
      ring

lemma P_eq_subset_sum (n : ℕ) :
    OeisA185895.P n = ∑ s ∈ (Finset.Icc 1 n).powerset,
      C ((-1 : ℚ) ^ s.card * ∏ k ∈ s, (1 / (k.factorial : ℚ))) *
        X ^ (∑ k ∈ s, k) := by
  classical
  rw [OeisA185895.P, Finset.prod_sub]
  simp only [Finset.prod_const_one, prod_monomials]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mul_one]
  rw [show (-1 : Polynomial ℚ) = C (-1 : ℚ) by simp, ← C_pow, ← mul_assoc,
    ← C_mul]

lemma coeff_P (n N : ℕ) :
    coeff (OeisA185895.P n) N = ∑ s ∈ (Finset.Icc 1 n).powerset,
      if (∑ k ∈ s, k) = N then
        (-1 : ℚ) ^ s.card * ∏ k ∈ s, (1 / (k.factorial : ℚ))
      else 0 := by
  rw [P_eq_subset_sum]
  simp only [finset_sum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [eq_comm]

lemma cast_multinomial (s : Finset ℕ) :
    (Nat.multinomial s id : ℚ) =
      ((∑ k ∈ s, k).factorial : ℚ) *
        ∏ k ∈ s, (1 / (k.factorial : ℚ)) := by
  rw [Nat.multinomial]
  rw [Nat.cast_div (Nat.prod_factorial_dvd_factorial_sum s id)]
  push_cast
  · simp [id_eq, div_eq_mul_inv, Finset.prod_inv_distrib]
  · positivity

/-- The signed count of set partitions whose block sizes are pairwise distinct. -/
def explicit (N : ℕ) : ℤ :=
  ∑ s ∈ (Finset.Icc 1 N).powerset,
    if (∑ k ∈ s, k) = N then
      (-1 : ℤ) ^ s.card * (Nat.multinomial s id : ℤ)
    else 0

lemma coeff_mul_factorial_eq_cast_explicit (N : ℕ) :
    coeff (OeisA185895.P N) N * (N.factorial : ℚ) = (explicit N : ℚ) := by
  rw [coeff_P]
  rw [Finset.sum_mul]
  simp only [explicit, Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_zero]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with h
  · rw [← h]
    calc
      ((-1 : ℚ) ^ s.card * ∏ k ∈ s, (1 / (k.factorial : ℚ))) *
          (((∑ k ∈ s, k).factorial : ℕ) : ℚ) =
        (-1 : ℚ) ^ s.card *
          (((∑ k ∈ s, k).factorial : ℚ) *
            ∏ k ∈ s, (1 / (k.factorial : ℚ))) := by ring
      _ = (-1 : ℚ) ^ s.card * (Nat.multinomial s id : ℚ) := by
        rw [← cast_multinomial]
  · ring

theorem a_eq_explicit {N : ℕ} (hN : N ≠ 0) :
    OeisA185895.a N = explicit N := by
  rw [OeisA185895.a, if_neg hN, coeff_mul_factorial_eq_cast_explicit]
  simp

#print axioms a_eq_explicit

end OeisA185895Proof

open scoped BigOperators

namespace OeisA185895Proof

lemma pow_dvd_pow_mul_choose_of_dvd_mul
    {p k m j : ℕ} (hp : p.Prime) (hj : 0 < j) (hpm : p ^ k ∣ p * m) :
    p ^ k ∣ p ^ j * m.choose j := by
  by_cases hjm : j ≤ m
  · have hm : m ≠ 0 := ne_of_gt (hj.trans_le hjm)
    have hc : m.choose j ≠ 0 := Nat.choose_ne_zero hjm
    have hpow : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hpow hc)]
    have hk : k ≤ (p * m).factorization p :=
      (hp.pow_dvd_iff_le_factorization (mul_ne_zero hp.ne_zero hm)).mp hpm
    have hjm' : j - 1 ≤ m - 1 := Nat.sub_le_sub_right hjm 1
    have hc' : (m - 1).choose (j - 1) ≠ 0 := Nat.choose_ne_zero hjm'
    have hchoose :
        m * (m - 1).choose (j - 1) = m.choose j * j := by
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm),
        Nat.sub_add_cancel hj] using Nat.add_one_mul_choose_eq (m - 1) (j - 1)
    have hfac := congrArg (fun x : ℕ ↦ x.factorization p) hchoose
    change (m * (m - 1).choose (j - 1)).factorization p =
      (m.choose j * j).factorization p at hfac
    rw [Nat.factorization_mul hm hc', Nat.factorization_mul hc hj.ne'] at hfac
    have hvj : j.factorization p < j := Nat.factorization_lt p hj.ne'
    rw [Nat.factorization_mul hp.ne_zero hm] at hk
    simp only [Finsupp.add_apply, hp.factorization_self] at hk
    rw [Nat.factorization_mul hpow hc, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      hp.factorization_self, mul_one] at hk hfac ⊢
    omega
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hjm), mul_zero]
    exact dvd_zero _

lemma add_p_mul_pow_eq_left_char
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    {R : Type*} [CommSemiring R] [CharP R (p ^ k)] (A Q : R) :
    (A + (p : R) * Q) ^ m = A ^ m := by
  rw [add_comm, add_pow]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have hdvd : p ^ k ∣ p ^ i * m.choose i :=
      pow_dvd_pow_mul_choose_of_dvd_mul hp hi_pos hpm
    have hz : ((p ^ i * m.choose i : ℕ) : R) = 0 :=
      (CharP.cast_eq_zero_iff R (p ^ k) (p ^ i * m.choose i)).2 hdvd
    rw [mul_pow]
    push_cast at hz
    calc
      (p : R) ^ i * Q ^ i * A ^ (m - i) * (m.choose i : R) =
          ((p : R) ^ i * (m.choose i : R)) *
            (Q ^ i * A ^ (m - i)) := by ring
      _ = 0 := by rw [hz, zero_mul]
  · intro h
    simp at h

lemma add_p_mul_pow_eq_left
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    (A Q : ZMod (p ^ k)) :
    (A + (p : ZMod (p ^ k)) * Q) ^ m = A ^ m :=
  add_p_mul_pow_eq_left_char hp hpm A Q

lemma exists_finset_sum_pow_prime_eq
    {p : ℕ} (hp : p.Prime) {R α : Type*} [CommSemiring R]
    (s : Finset α) (f : α → R) :
    ∃ Q : R, (∑ i ∈ s, f i) ^ p = (∑ i ∈ s, (f i) ^ p) + (p : R) * Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp [hp.ne_zero]
  | @insert a s ha ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨T, hT⟩ := exists_add_pow_prime_eq hp (f a) (∑ i ∈ s, f i)
      refine ⟨Q + f a * (∑ i ∈ s, f i) * T, ?_⟩
      simp only [Finset.sum_insert ha]
      rw [hT, hQ]
      ring

lemma finset_sum_pow_prime_mul_eq
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    {α : Type*} (s : Finset α) (f : α → ZMod (p ^ k)) :
    (∑ i ∈ s, f i) ^ (p * m) = (∑ i ∈ s, (f i) ^ p) ^ m := by
  obtain ⟨Q, hQ⟩ := exists_finset_sum_pow_prime_eq hp s f
  rw [pow_mul, hQ, add_p_mul_pow_eq_left hp hpm]

lemma finset_sum_pow_prime_mul_eq_char
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    {R α : Type*} [CommSemiring R] [CharP R (p ^ k)]
    (s : Finset α) (f : α → R) :
    (∑ i ∈ s, f i) ^ (p * m) = (∑ i ∈ s, (f i) ^ p) ^ m := by
  obtain ⟨Q, hQ⟩ := exists_finset_sum_pow_prime_eq hp s f
  rw [pow_mul, hQ, add_p_mul_pow_eq_left_char hp hpm]

end OeisA185895Proof

namespace OeisA185895Proof

open MvPolynomial

variable {R α : Type*} [CommSemiring R] [Fintype α]

noncomputable def exponent (f : α → ℕ) : α →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm f

lemma exponent_apply (f : α → ℕ) (i : α) : exponent f i = f i := by
  simp [exponent]

lemma exponent_support_subset_univ (f : α → ℕ) :
    (exponent f).support ⊆ (Finset.univ : Finset α) := by
  exact Finset.subset_univ _

lemma prod_univ_X_pow_eq_monomial (f : α → ℕ) :
    (∏ i : α, (X i : MvPolynomial α R) ^ f i) = monomial (exponent f) 1 := by
  rw [← prod_X_pow_eq_monomial]
  rw [Finset.prod_subset (exponent_support_subset_univ f)]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [exponent_apply]
  · intro i hi hnot
    have hz : exponent f i = 0 := by simpa [Finsupp.mem_support_iff] using hnot
    rw [hz, pow_zero]

lemma exponent_injective : Function.Injective (exponent : (α → ℕ) → (α →₀ ℕ)) := by
  exact Finsupp.equivFunOnFinite.symm.injective

lemma coeff_sum_X_pow (f : α → ℕ) (N : ℕ) :
    coeff (exponent f) ((∑ i : α, X i) ^ N : MvPolynomial α R) =
      if (∑ i : α, f i) = N then (Nat.multinomial Finset.univ f : R) else 0 := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  simp_rw [← MvPolynomial.C_eq_coe_nat]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    prod_univ_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases hsum : (∑ i : α, f i) = N
  · rw [if_pos hsum]
    rw [Finset.sum_eq_single f]
    · simp
    · intro g hg hgf
      have heg : exponent g ≠ exponent f := fun h ↦ hgf (exponent_injective h)
      simp [heg]
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_piAntidiag.mpr ⟨by simpa using hsum, fun _ _ ↦ Finset.mem_univ _⟩
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro g hg
    have hgf : exponent g ≠ exponent f := by
      intro h
      have : g = f := exponent_injective h
      subst g
      have hsum' := (Finset.mem_piAntidiag.mp hg).1
      apply hsum
      simpa using hsum'
    simp [hgf]

lemma multinomial_prime_scaling_zmod
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    (f : α → ℕ) (hsum : (∑ i : α, f i) = p * m) :
    (Nat.multinomial Finset.univ f : ZMod (p ^ k)) =
      if _h : ∀ i, p ∣ f i then
        (Nat.multinomial Finset.univ (fun i ↦ f i / p) : ZMod (p ^ k))
      else 0 := by
  classical
  let S : MvPolynomial α (ZMod (p ^ k)) := ∑ i : α, X i
  have hpoly : S ^ (p * m) = expand p (S ^ m) := by
    calc
      S ^ (p * m) = (∑ i : α, (X i : MvPolynomial α (ZMod (p ^ k))) ^ p) ^ m := by
        simpa [S] using finset_sum_pow_prime_mul_eq_char hp hpm
          (Finset.univ : Finset α) (fun i ↦ (X i : MvPolynomial α (ZMod (p ^ k))))
      _ = expand p (S ^ m) := by simp [S]
  have hcoeff := congrArg (MvPolynomial.coeff (exponent f)) hpoly
  rw [coeff_sum_X_pow f (p * m), if_pos hsum] at hcoeff
  by_cases hdiv : ∀ i, p ∣ f i
  · rw [dif_pos hdiv]
    let g : α → ℕ := fun i ↦ f i / p
    have hfg : exponent f = p • exponent g := by
      ext i
      simp only [exponent_apply, Finsupp.smul_apply, smul_eq_mul, g]
      exact (Nat.mul_div_cancel' (hdiv i)).symm
    have hsumg : (∑ i : α, g i) = m := by
      have hp_sum : p * (∑ i : α, g i) = p * m := by
        calc
          p * (∑ i : α, g i) = ∑ i : α, p * g i := by
            rw [Finset.mul_sum]
          _ = ∑ i : α, f i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Nat.mul_div_cancel' (hdiv i)
          _ = p * m := hsum
      exact Nat.eq_of_mul_eq_mul_left hp.pos hp_sum
    rw [hfg, MvPolynomial.coeff_expand_smul p hp.ne_zero,
      coeff_sum_X_pow g m, if_pos hsumg] at hcoeff
    simpa [g] using hcoeff
  · rw [dif_neg hdiv]
    push_neg at hdiv
    obtain ⟨i, hi⟩ := hdiv
    have hz : (expand p (S ^ m)).coeff (exponent f) = 0 :=
      MvPolynomial.coeff_expand_of_not_dvd (S ^ m) (by simpa [exponent_apply] using hi)
    exact hcoeff.trans hz

lemma multinomial_subtype (s : Finset ℕ) (f : ℕ → ℕ) :
    Nat.multinomial (Finset.univ : Finset s) (fun x : s ↦ f x) =
      Nat.multinomial s f := by
  unfold Nat.multinomial
  rw [Finset.univ_eq_attach, Finset.sum_attach]
  congr 1
  exact Finset.prod_attach s (fun x ↦ (f x).factorial)

lemma multinomial_finset_prime_reduction_zmod
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    (s : Finset ℕ) (hsum : ∑ x ∈ s, x = p * m) :
    (Nat.multinomial s id : ZMod (p ^ k)) =
      if _h : ∀ x ∈ s, p ∣ x then
        (Nat.multinomial (s.image (· / p)) id : ZMod (p ^ k))
      else 0 := by
  classical
  have hsum' : ∑ x : s, (x : ℕ) = p * m := by
    calc
      ∑ x : s, (x : ℕ) = ∑ x ∈ s, x := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach s id
      _ = p * m := hsum
  have h := multinomial_prime_scaling_zmod hp hpm
    (fun x : s ↦ (x : ℕ)) hsum'
  have hsub_id :
      Nat.multinomial (Finset.univ : Finset s) (fun x : s ↦ (x : ℕ)) =
        Nat.multinomial s id := by
    simpa only [id_eq] using multinomial_subtype s id
  rw [hsub_id] at h
  by_cases hd : ∀ x ∈ s, p ∣ x
  · rw [dif_pos hd]
    rw [dif_pos (fun x : s ↦ hd x x.property)] at h
    have hinj : Set.InjOn (· / p) s := by
      intro x hx y hy hxy
      calc
        x = p * (x / p) := (Nat.mul_div_cancel' (hd x hx)).symm
        _ = p * (y / p) := congrArg (p * ·) hxy
        _ = y := Nat.mul_div_cancel' (hd y hy)
    have hsub_div :
        Nat.multinomial (Finset.univ : Finset s) (fun x : s ↦ (x : ℕ) / p) =
          Nat.multinomial s (fun x ↦ x / p) :=
      multinomial_subtype s (fun x ↦ x / p)
    rw [hsub_div] at h
    have himage :
        Nat.multinomial (s.image (· / p)) id =
          Nat.multinomial s (fun x ↦ x / p) := by
      unfold Nat.multinomial
      rw [Finset.sum_image hinj, Finset.prod_image hinj]
      simp only [id_eq]
    rw [← himage] at h
    exact h
  · rw [dif_neg hd]
    have hd' : ¬ ∀ x : s, p ∣ (x : ℕ) := by
      intro hd'
      apply hd
      intro x hx
      exact hd' ⟨x, hx⟩
    rw [dif_neg hd'] at h
    exact h

/- The finite-set reindexing used in the global congruence. -/

def scale (p : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (p * ·)

lemma mul_left_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (p * · : ℕ → ℕ) := by
  intro a b h
  exact Nat.mul_left_cancel hp h

@[simp] lemma card_scale {p : ℕ} (hp : 0 < p) (s : Finset ℕ) :
    (scale p s).card = s.card :=
  Finset.card_image_of_injective s (mul_left_injective hp)

lemma mem_scale_iff {p x : ℕ} {s : Finset ℕ} :
    x ∈ scale p s ↔ ∃ y ∈ s, p * y = x := by
  simp [scale, eq_comm]

lemma scale_subset_Icc {p M : ℕ} (hp : 0 < p) {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 M) :
    scale p s ⊆ Finset.Icc 1 (p * M) := by
  intro x hx
  rw [mem_scale_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyI := hs hy
  simp only [Finset.mem_Icc] at hyI ⊢
  constructor <;> nlinarith

lemma scale_image_div {p : ℕ} (_hp : 0 < p) (s : Finset ℕ)
    (hdiv : ∀ x ∈ s, p ∣ x) :
    scale p (s.image (· / p)) = s := by
  ext x
  constructor
  · intro hx
    rw [mem_scale_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa [Nat.mul_div_cancel' (hdiv z hz)] using hz
  · intro hx
    rw [mem_scale_iff]
    refine ⟨x / p, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    exact Nat.mul_div_cancel' (hdiv x hx)

lemma div_injective_on_of_dvd {p : ℕ} (s : Finset ℕ)
    (hdiv : ∀ x ∈ s, p ∣ x) : Set.InjOn (· / p) s := by
  intro x hx y hy hxy
  calc
    x = p * (x / p) := (Nat.mul_div_cancel' (hdiv x hx)).symm
    _ = p * (y / p) := congrArg (p * ·) hxy
    _ = y := Nat.mul_div_cancel' (hdiv y hy)

lemma image_div_subset_Icc {p M : ℕ} (hp : 0 < p) {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 (p * M)) (hdiv : ∀ x ∈ s, p ∣ x) :
    s.image (· / p) ⊆ Finset.Icc 1 M := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzI := hs hz
  simp only [Finset.mem_Icc] at hzI ⊢
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hzI.1 (hdiv z hz)) hp))
  · exact Nat.div_le_of_le_mul hzI.2

lemma sum_image_div {p M : ℕ} (hp : 0 < p) {s : Finset ℕ}
    (hsum : ∑ x ∈ s, x = p * M) (hdiv : ∀ x ∈ s, p ∣ x) :
    ∑ x ∈ s.image (· / p), x = M := by
  rw [Finset.sum_image (div_injective_on_of_dvd s hdiv)]
  rw [← Nat.sum_div hdiv, hsum]
  simp [hp.ne']

lemma div_image_scale {p : ℕ} (hp : 0 < p) (s : Finset ℕ) :
    (scale p s).image (· / p) = s := by
  ext x
  simp [scale, hp.ne']

def shapes (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (fun s ↦ ∑ x ∈ s, x = N)

lemma mem_shapes {N : ℕ} {s : Finset ℕ} :
    s ∈ shapes N ↔ s ⊆ Finset.Icc 1 N ∧ ∑ x ∈ s, x = N := by
  simp [shapes]

lemma scale_mem_shapes {p M : ℕ} (hp : 0 < p) {s : Finset ℕ}
    (hs : s ∈ shapes M) : scale p s ∈ shapes (p * M) := by
  rw [mem_shapes] at hs ⊢
  exact ⟨scale_subset_Icc hp hs.1, by
    rw [show ∑ x ∈ scale p s, x = p * ∑ x ∈ s, x by
      rw [scale, Finset.sum_image]
      · simp [Finset.mul_sum]
      · exact fun _ _ _ _ h ↦ mul_left_injective hp h]
    rw [hs.2]⟩

lemma image_div_mem_shapes {p M : ℕ} (hp : 0 < p) {s : Finset ℕ}
    (hs : s ∈ shapes (p * M)) (hdiv : ∀ x ∈ s, p ∣ x) :
    s.image (· / p) ∈ shapes M := by
  rw [mem_shapes] at hs ⊢
  exact ⟨image_div_subset_Icc hp hs.1 hdiv, sum_image_div hp hs.2 hdiv⟩

lemma dvd_of_mem_scale {p : ℕ} {s : Finset ℕ} {x : ℕ}
    (hx : x ∈ scale p s) : p ∣ x := by
  rw [mem_scale_iff] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact dvd_mul_right p y

def Divisible (p : ℕ) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, p ∣ x

noncomputable instance divisibleDecidable (p : ℕ) (s : Finset ℕ) :
    Decidable (Divisible p s) :=
  Classical.propDecidable _

def shapeTerm (q : ℕ) (s : Finset ℕ) : ZMod q :=
  (-1 : ZMod q) ^ s.card * (Nat.multinomial s id : ZMod q)

def dividedTerm (p q : ℕ) (s : Finset ℕ) : ZMod q :=
  (-1 : ZMod q) ^ s.card *
    (Nat.multinomial (s.image (· / p)) id : ZMod q)

lemma shapeTerm_prime_reduction
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m)
    {s : Finset ℕ} (hs : s ∈ shapes (p * m)) :
    shapeTerm (p ^ k) s =
      if Divisible p s then dividedTerm p (p ^ k) s else 0 := by
  classical
  rw [shapeTerm, dividedTerm]
  have hsum : ∑ x ∈ s, x = p * m := (mem_shapes.mp hs).2
  rw [multinomial_finset_prime_reduction_zmod hp hpm s hsum]
  by_cases hd : Divisible p s
  · have hd' : ∀ x ∈ s, p ∣ x := by simpa [Divisible] using hd
    rw [dif_pos hd', if_pos hd]
  · have hd' : ¬ ∀ x ∈ s, p ∣ x := by simpa [Divisible] using hd
    rw [dif_neg hd', if_neg hd, mul_zero]

theorem shapeSum_prime_reduction_zmod
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m) :
    ∑ s ∈ shapes (p * m), shapeTerm (p ^ k) s =
      ∑ s ∈ shapes m, shapeTerm (p ^ k) s := by
  classical
  calc
    ∑ s ∈ shapes (p * m), shapeTerm (p ^ k) s =
        ∑ s ∈ shapes (p * m),
          if Divisible p s then dividedTerm p (p ^ k) s else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact shapeTerm_prime_reduction hp hpm hs
    _ = ∑ s ∈ (shapes (p * m)).filter (Divisible p),
          dividedTerm p (p ^ k) s := by
      rw [Finset.sum_filter]
    _ = ∑ s ∈ shapes m, shapeTerm (p ^ k) s := by
      symm
      apply Finset.sum_nbij' (scale p) (fun s ↦ s.image (· / p))
      · intro s hs
        rw [Finset.mem_filter]
        refine ⟨scale_mem_shapes hp.pos hs, ?_⟩
        intro x hx
        exact dvd_of_mem_scale hx
      · intro s hs
        rw [Finset.mem_filter] at hs
        exact image_div_mem_shapes hp.pos hs.1 hs.2
      · intro s hs
        exact div_image_scale hp.pos s
      · intro s hs
        rw [Finset.mem_filter] at hs
        exact scale_image_div hp.pos s hs.2
      · intro s hs
        simp [shapeTerm, dividedTerm, div_image_scale hp.pos, card_scale hp.pos]

def signedShapeSum (N : ℕ) : ℤ :=
  ∑ s ∈ shapes N,
    (-1 : ℤ) ^ s.card * (Nat.multinomial s id : ℤ)

lemma intCast_signedShapeSum (q N : ℕ) :
    (signedShapeSum N : ZMod q) =
      ∑ s ∈ shapes N, shapeTerm q s := by
  classical
  simp [signedShapeSum, shapeTerm]

theorem signedShapeSum_prime_reduction_modEq
    {p k m : ℕ} (hp : p.Prime) (hpm : p ^ k ∣ p * m) :
    Int.ModEq ((p : ℤ) ^ k) (signedShapeSum (p * m)) (signedShapeSum m) := by
  have hz := shapeSum_prime_reduction_zmod hp hpm
  rw [← intCast_signedShapeSum (p ^ k) (p * m),
    ← intCast_signedShapeSum (p ^ k) m] at hz
  have hm := (ZMod.intCast_eq_intCast_iff
    (signedShapeSum (p * m)) (signedShapeSum m) (p ^ k)).mp hz
  simpa only [Int.natCast_pow] using hm

theorem signedShapeSum_gauss_modEq
    {p n k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    Int.ModEq ((p : ℤ) ^ k)
      (signedShapeSum (n * p ^ k))
      (signedShapeSum (n * p ^ (k - 1))) := by
  let m := n * p ^ (k - 1)
  have hindex : p * m = n * p ^ k := by
    calc
      p * m = n * (p ^ (k - 1) * p) := by simp [m, mul_comm, mul_left_comm]
      _ = n * p ^ ((k - 1) + 1) := by rw [pow_succ]
      _ = n * p ^ k := by rw [Nat.sub_add_cancel hk]
  have hpm : p ^ k ∣ p * m := by
    rw [hindex]
    exact dvd_mul_left (p ^ k) n
  simpa only [hindex, m] using signedShapeSum_prime_reduction_modEq hp hpm

#print axioms shapeSum_prime_reduction_zmod
#print axioms signedShapeSum_gauss_modEq

#print axioms multinomial_prime_scaling_zmod

end OeisA185895Proof

namespace OeisA185895Proof

lemma explicit_eq_signedShapeSum (N : ℕ) :
    explicit N = signedShapeSum N := by
  classical
  rw [explicit, signedShapeSum, shapes, Finset.sum_filter]

/-- The exact theorem currently stated as `OeisA185895.conjecture3` in Formal Conjectures. -/
theorem conjecture3_solved (p : ℕ) (hp : p.Prime) (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) :
    OeisA185895.a (n * p ^ k) ≡
      OeisA185895.a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k] := by
  have hleft : n * p ^ k ≠ 0 :=
    mul_ne_zero (Nat.ne_of_gt hn) (pow_ne_zero _ hp.ne_zero)
  have hright : n * p ^ (k - 1) ≠ 0 :=
    mul_ne_zero (Nat.ne_of_gt hn) (pow_ne_zero _ hp.ne_zero)
  rw [a_eq_explicit hleft, a_eq_explicit hright,
    explicit_eq_signedShapeSum, explicit_eq_signedShapeSum]
  exact signedShapeSum_gauss_modEq hp hk

#print axioms conjecture3_solved

end OeisA185895Proof
