import Mathlib

/-!
Complete formalization of proof.tex.
Main theorem: SquareResidue.closed_formula.
Checked in AXLE's lean-4.34.0 Mathlib environment.

The Fourier reduction, signed Gauss evaluation, zero count, and divisor reindexing
are proved. The Gauss sign follows from Gaussian Poisson summation and a proved
rational-boundary limit. The fundamental Dirichlet class-number formula follows
from explicit ideal counts, Dedekind zeta factorization, and a dominated limit at one,
using Mathlib's analytic class-number formula.

For every negative discriminant, proper primitive form classes are identified with
invertible ideal classes. The conductor sequence is constructed through Picard groups;
its kernel is counted using quadratic residue algebras, and surjectivity is proved
using forms with leading coefficient coprime to the conductor. This proves the order
class-number formula with the exceptional unit counts included.
-/

open scoped BigOperators
open Finset AddChar

namespace SquareResidue

noncomputable section

/-- The sum in the original question, with least nonnegative remainders. -/
def residueSum (n : ℕ) : ℕ := ∑ x ∈ range n, x ^ 2 % n

/-- An algebraic version of the differentiated geometric-series identity. -/
theorem weighted_geom_mul (n : ℕ) (z : ℂ) :
    (∑ a ∈ range n, (a : ℂ) * z ^ a) * (z - 1) =
      (n : ℂ) * z ^ n - z * ∑ a ∈ range n, z ^ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, add_mul, ih, pow_succ]
    push_cast
    ring

/-- The geometric-sum lemma in §3.2 of the source. -/
theorem weighted_geom (n : ℕ) (z : ℂ) (hn : z ^ n = 1) (hz : z ≠ 1) :
    ∑ a ∈ range n, (a : ℂ) * z ^ a = (n : ℂ) / (z - 1) := by
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hg : ∑ a ∈ range n, z ^ a = 0 := by
    have h := geom_sum_mul z n
    rw [hn, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hz'
  apply (eq_div_iff hz').mpr
  rw [weighted_geom_mul, hn, hg]
  ring

variable {n : ℕ} [NeZero n]

/-- Least nonnegative representative, regarded as a complex number. -/
def residue (a : ZMod n) : ℂ := a.val

/-- Quadratic additive Gauss sum. -/
def quadraticGauss (t : ZMod n) : ℂ :=
  ∑ x : ZMod n, ZMod.stdAddChar (t * x ^ 2)

/-- Number of square roots of zero in `ZMod n`. -/
def zeroCount (n : ℕ) [NeZero n] : ℕ :=
  #{x : ZMod n | x ^ 2 = 0}

/-- Exchange modular elements and their least representatives in a finite sum. -/
theorem sum_zmod_eq_range {A : Type*} [AddCommMonoid A] (f : ZMod n → A) :
    ∑ a : ZMod n, f a = ∑ a ∈ range n, f (a : ZMod n) := by
  classical
  symm
  refine sum_bij (fun a _ => (a : ZMod n)) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro a ha b hb hab
    simpa [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
  · intro a _
    exact ⟨a.val, mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩

theorem sum_residue : ∑ a : ZMod n, residue a = (n : ℂ) * (n - 1) / 2 := by
  rw [sum_zmod_eq_range]
  have hs := sum_range_id_mul_two n
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hs' : (∑ a ∈ range n, (a : ℂ)) * 2 = (n : ℂ) * (↑(n - 1) : ℂ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ℂ)) hs
  rw [Nat.cast_sub hn, Nat.cast_one] at hs'
  have hv : ∑ a ∈ range n, residue (a : ZMod n) = ∑ a ∈ range n, (a : ℂ) := by
    apply sum_congr rfl
    intro a ha
    simp [residue, ZMod.val_natCast_of_lt (mem_range.mp ha)]
  rw [hv]
  linear_combination hs' / 2

theorem char_neg_pow (t : ZMod n) (a : ℕ) :
    ZMod.stdAddChar (-((a : ZMod n) * t)) = ZMod.stdAddChar (-t) ^ a := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [nsmul_eq_mul]

theorem char_pow_modulus (t : ZMod n) : ZMod.stdAddChar t ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem char_ne_one {t : ZMod n} (ht : t ≠ 0) : ZMod.stdAddChar t ≠ 1 := by
  intro h
  apply ht
  exact ZMod.injective_stdAddChar (h.trans (map_zero_eq_one _).symm)

/-- The nonconstant Fourier coefficients of the residue function. -/
theorem dft_residue_nonzero {t : ZMod n} (ht : t ≠ 0) :
    ZMod.dft residue t = (n : ℂ) / (ZMod.stdAddChar (-t) - 1) := by
  rw [ZMod.dft_apply, sum_zmod_eq_range]
  simp only [smul_eq_mul]
  have hv : ∀ a ∈ range n, residue (a : ZMod n) = (a : ℂ) := by
    intro a ha
    simp [residue, ZMod.val_natCast_of_lt (mem_range.mp ha)]
  calc
    _ = ∑ a ∈ range n, (a : ℂ) * ZMod.stdAddChar (-t) ^ a := by
      apply sum_congr rfl
      intro a ha
      rw [char_neg_pow, hv a ha, mul_comm]
    _ = _ := weighted_geom n _ (char_pow_modulus _) (char_ne_one (neg_ne_zero.mpr ht))

/-- The residue Fourier expansion, using Mathlib's Fourier inversion theorem. -/
theorem residue_fourier (a : ZMod n) :
    residue a = ((n : ℂ) - 1) / 2 +
      ∑ t ∈ (univ : Finset (ZMod n)).erase 0,
        ZMod.stdAddChar (t * a) / (ZMod.stdAddChar (-t) - 1) := by
  classical
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := congrFun (ZMod.dft.symm_apply_apply (residue (n := n))) a
  rw [ZMod.invDFT_apply] at h
  simp only [smul_eq_mul] at h
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))] at h
  simp only [zero_mul, map_zero_eq_one, one_mul, ZMod.dft_apply_zero,
    sum_residue] at h
  rw [mul_add, mul_sum] at h
  have h0 : (n : ℂ)⁻¹ * ((n : ℂ) * (n - 1) / 2) = ((n : ℂ) - 1) / 2 := by
    field_simp
  have h1 : ∀ t ∈ (univ : Finset (ZMod n)).erase 0,
      (n : ℂ)⁻¹ * (ZMod.stdAddChar (t * a) * ZMod.dft residue t) =
        ZMod.stdAddChar (t * a) / (ZMod.stdAddChar (-t) - 1) := by
    intro t ht
    rw [dft_residue_nonzero (mem_erase.mp ht).1]
    field_simp
  rw [h0, sum_congr rfl h1, add_comm] at h
  exact h.symm

/-- Identification of the modular sum with the sum in the question. -/
theorem residueSum_eq : (residueSum n : ℂ) = ∑ x : ZMod n, residue (x ^ 2) := by
  rw [sum_zmod_eq_range]
  rw [residueSum, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  change ((x ^ 2 % n : ℕ) : ℂ) = (((x : ZMod n) ^ 2).val : ℂ)
  rw [← Nat.cast_pow, ZMod.val_natCast]

/-- §3.4: summing the Fourier expansion creates quadratic Gauss sums. -/
theorem residueSum_gauss :
    (residueSum n : ℂ) = (n : ℂ) * (n - 1) / 2 +
      ∑ t ∈ (univ : Finset (ZMod n)).erase 0,
        quadraticGauss t / (ZMod.stdAddChar (-t) - 1) := by
  classical
  rw [residueSum_eq]
  simp_rw [residue_fourier, sum_add_distrib]
  rw [sum_comm]
  simp [quadraticGauss, sum_div, ZMod.card, mul_div_assoc]

/-- Orthogonality of the standard additive characters, reused from Mathlib. -/
theorem character_orthogonality (a : ZMod n) :
    ∑ t : ZMod n, ZMod.stdAddChar (a * t) = if a = 0 then (n : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

theorem quadraticGauss_zero : quadraticGauss (0 : ZMod n) = n := by
  simp [quadraticGauss, ZMod.card]

/-- The constant Gauss-sum contribution before evaluating the root count. -/
theorem sum_quadraticGauss :
    ∑ t : ZMod n, quadraticGauss t = (n : ℂ) * zeroCount n := by
  classical
  unfold quadraticGauss zeroCount
  rw [sum_comm]
  simp_rw [mul_comm _ (_ ^ 2), character_orthogonality]
  simp [sum_ite, mul_comm]

/-- A finite partial-fraction identity underlying cotangent distribution. -/
theorem reciprocal_roots_sum (z : ℂ) (hz : z ^ n ≠ 1) :
    ∑ t : ZMod n, (z * ZMod.stdAddChar t - 1)⁻¹ = (n : ℂ) / (z ^ n - 1) := by
  classical
  have hzden : z ^ n - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hp (t : ZMod n) : (z * ZMod.stdAddChar t) ^ n = z ^ n := by
    rw [mul_pow, char_pow_modulus, mul_one]
  have htden (t : ZMod n) : z * ZMod.stdAddChar t - 1 ≠ 0 := by
    intro h
    have h1 : z * ZMod.stdAddChar t = 1 := sub_eq_zero.mp h
    have h2 := hp t
    rw [h1, one_pow] at h2
    exact hz h2.symm
  have hgeom (t : ZMod n) : (z * ZMod.stdAddChar t - 1)⁻¹ =
      (∑ a ∈ range n, (z * ZMod.stdAddChar t) ^ a) / (z ^ n - 1) := by
    apply (eq_div_iff hzden).mpr
    rw [← hp t, ← geom_sum_mul]
    simp [htden t, mul_comm]
  have hchar (a : ℕ) : ∑ t : ZMod n, ZMod.stdAddChar t ^ a =
      if (a : ZMod n) = 0 then (n : ℂ) else 0 := by
    simp_rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    exact character_orthogonality (a : ZMod n)
  have ha0 (a : ℕ) (ha : a ∈ range n) : (a : ZMod n) = 0 ↔ a = 0 := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa [ZMod.val_natCast_of_lt (mem_range.mp ha)] using hv
    · rintro rfl
      simp
  simp_rw [hgeom]
  rw [← sum_div, sum_comm]
  have hn : 0 ∈ range n := mem_range.mpr (NeZero.pos n)
  have hsum : ∑ a ∈ range n, ∑ t : ZMod n, (z * ZMod.stdAddChar t) ^ a = n := by
    simp_rw [mul_pow, ← mul_sum, hchar]
    calc
      _ = ∑ a ∈ range n, z ^ a * (if a = 0 then (n : ℂ) else 0) := by
        apply sum_congr rfl
        intro a ha
        simp only [ha0 a ha]
      _ = _ := by simp [mul_ite, hn]
  rw [hsum]

/-- The prefactor identity of §3.5, proved using the double-angle formulas. -/
theorem exp_cot_prefactor (θ : ℝ) (hs : Real.sin θ ≠ 0) :
    (Complex.exp ((-2 * θ : ℝ) * Complex.I) - 1)⁻¹ =
      -1 / 2 + Complex.I / 2 * (Real.cot θ : ℂ) := by
  apply inv_eq_of_mul_eq_one_right
  rw [Complex.exp_ofReal_mul_I]
  simp only [show (-2 : ℝ) * θ = -(2 * θ) by ring,
    Real.cos_neg, Real.sin_neg, Real.cos_two_mul, Real.sin_two_mul,
    Real.cot_eq_cos_div_sin]
  have hs' : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hp : (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  push_cast
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  linear_combination (2 * Complex.I * (Real.cos θ : ℂ)) * hp

/-- Cotangent at a nonzero modular angle, extended by zero at the origin. -/
def cotWeight (t : ZMod n) : ℝ := Real.cot (Real.pi * t.val / n)

theorem char_neg_exp (t : ZMod n) : ZMod.stdAddChar (-t) =
    Complex.exp ((-2 * (Real.pi * t.val / n) : ℝ) * Complex.I) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast, ← Int.cast_neg,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem exp_neg_two_ne_one (θ : ℝ) (hs : Real.sin θ ≠ 0) :
    Complex.exp ((-2 * θ : ℝ) * Complex.I) ≠ 1 := by
  intro he
  have h := congrArg Complex.re (exp_cot_prefactor θ hs)
  rw [he] at h
  have hr : (-1 / 2 + Complex.I / 2 * (Real.cot θ : ℂ)).re = -(1 / 2 : ℝ) := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.div_ofNat_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
  rw [hr] at h
  norm_num at h

/-- The finite cotangent distribution law, derived from finite character orthogonality. -/
theorem cot_distribution (θ : ℝ) (hθ : 0 < θ) (hnθ : (n : ℝ) * θ < Real.pi) :
    ∑ k ∈ range n, Real.cot (θ + Real.pi * k / n) =
      (n : ℝ) * Real.cot ((n : ℝ) * θ) := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  let z : ℂ := Complex.exp ((-2 * θ : ℝ) * Complex.I)
  have hzpow : z ^ n = Complex.exp ((-2 * ((n : ℝ) * θ) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnSin : Real.sin ((n : ℝ) * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos hn hθ) hnθ).ne'
  have hz : z ^ n ≠ 1 := by rw [hzpow]; exact exp_neg_two_ne_one _ hnSin
  have hneg : ∑ t : ZMod n, (z * ZMod.stdAddChar (-t) - 1)⁻¹ =
      (n : ℂ) / (z ^ n - 1) := by
    calc
      _ = ∑ t : ZMod n, (z * ZMod.stdAddChar t - 1)⁻¹ :=
        Fintype.sum_equiv (Equiv.neg _) _ _ (fun t => rfl)
      _ = _ := reciprocal_roots_sum z hz
  have hangle (t : ZMod n) : 0 < θ + Real.pi * t.val / n ∧
      θ + Real.pi * t.val / n < Real.pi := by
    have ht : (t.val : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr t.val_lt)
    have htpi := mul_le_mul_of_nonneg_left ht Real.pi_nonneg
    have heq : θ + Real.pi * t.val / n = (n * θ + Real.pi * t.val) / n := by
      field_simp
    constructor
    · positivity
    · rw [heq]
      apply (div_lt_iff₀ hn).mpr
      nlinarith
  have he (t : ZMod n) : (z * ZMod.stdAddChar (-t) - 1)⁻¹ =
      -1 / 2 + Complex.I / 2 * (Real.cot (θ + Real.pi * t.val / n) : ℂ) := by
    rw [char_neg_exp, ← Complex.exp_add]
    have heq : (-2 * θ : ℝ) * Complex.I +
        (-2 * (Real.pi * t.val / n) : ℝ) * Complex.I =
          (-2 * (θ + Real.pi * t.val / n) : ℝ) * Complex.I := by push_cast; ring
    rw [heq]
    exact exp_cot_prefactor _ (Real.sin_pos_of_pos_of_lt_pi (hangle t).1 (hangle t).2).ne'
  rw [sum_congr rfl (fun t _ => he t)] at hneg
  conv_rhs at hneg => rw [div_eq_mul_inv, hzpow, exp_cot_prefactor _ hnSin]
  have hi := congrArg Complex.im hneg
  simp only [Complex.im_sum, Complex.add_im, Complex.div_ofNat_im, Complex.neg_im,
    Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, zero_div, one_div, zero_add, add_zero, neg_zero] at hi
  rw [← mul_sum] at hi
  have hsum : ∑ t : ZMod n, Real.cot (θ + Real.pi * t.val / n) =
      (n : ℝ) * Real.cot ((n : ℝ) * θ) := by
    linear_combination 2 * hi
  rw [sum_zmod_eq_range] at hsum
  have hv : ∀ k ∈ range n, Real.cot (θ + Real.pi * (k : ZMod n).val / n) =
      Real.cot (θ + Real.pi * k / n) := by
    intro k hk
    rw [ZMod.val_natCast_of_lt (mem_range.mp hk)]
  rw [sum_congr rfl hv] at hsum
  exact hsum

theorem modular_cot_prefactor {t : ZMod n} (ht : t ≠ 0) :
    (ZMod.stdAddChar (-t) - 1)⁻¹ =
      -1 / 2 + Complex.I / 2 * (cotWeight t : ℂ) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have htpos : (0 : ℝ) < t.val := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero ((ZMod.val_eq_zero t).not.mpr ht))
  have htlt : (t.val : ℝ) < n := Nat.cast_lt.mpr t.val_lt
  have hθpos : 0 < Real.pi * t.val / n := div_pos (mul_pos Real.pi_pos htpos) hn
  have hθlt : Real.pi * t.val / n < Real.pi := by
    apply (div_lt_iff₀ hn).mpr
    exact mul_lt_mul_of_pos_left htlt Real.pi_pos
  rw [char_neg_exp]
  exact exp_cot_prefactor _ (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt).ne'

/-- Real part of a single Fourier/Gauss summand. -/
theorem gauss_term_real {t : ZMod n} (ht : t ≠ 0) :
    (quadraticGauss t / (ZMod.stdAddChar (-t) - 1)).re =
      -(quadraticGauss t).re / 2 - (quadraticGauss t).im * cotWeight t / 2 := by
  rw [div_eq_mul_inv, modular_cot_prefactor ht]
  simp [Complex.mul_re]
  ring

theorem sum_quadraticGauss_nonzero :
    ∑ t ∈ (univ : Finset (ZMod n)).erase 0, quadraticGauss t =
      (n : ℂ) * (zeroCount n - 1) := by
  classical
  have h := sum_erase_add (univ : Finset (ZMod n)) quadraticGauss (mem_univ 0)
  rw [sum_quadraticGauss, quadraticGauss_zero] at h
  linear_combination h

/-- The master decomposition of §3.9, with no arithmetic assumptions. -/
theorem master_decomposition :
    (residueSum n : ℝ) = (n : ℝ) * (n - zeroCount n) / 2 -
      (∑ t ∈ (univ : Finset (ZMod n)).erase 0,
        (quadraticGauss t).im * cotWeight t) / 2 := by
  classical
  have h := congrArg Complex.re (residueSum_gauss (n := n))
  have hc := congrArg Complex.re (sum_quadraticGauss_nonzero (n := n))
  simp only [Complex.add_re, Complex.re_sum, Complex.natCast_re, Complex.div_ofNat_re,
    Complex.mul_re, Complex.sub_re, Complex.natCast_im, Complex.sub_im,
    Complex.one_re, Complex.one_im, mul_zero, sub_zero] at h hc
  have ht : ∀ t ∈ (univ : Finset (ZMod n)).erase 0,
      (quadraticGauss t / (ZMod.stdAddChar (-t) - 1)).re =
        -(quadraticGauss t).re / 2 - (quadraticGauss t).im * cotWeight t / 2 :=
    fun t ht => gauss_term_real (mem_erase.mp ht).1
  rw [sum_congr rfl ht, sum_sub_distrib, ← sum_div, ← sum_div, sum_neg_distrib] at h
  linear_combination h - hc / 2

/-- The square root of the largest square divisor, called `m` in the source. -/
def squarePart (n : ℕ) : ℕ := Nat.floorRoot 2 n

/-- Floor and ceiling divisibility square roots multiply to the modulus. -/
theorem floorRoot_mul_ceilRoot (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n * Nat.ceilRoot 2 n = n := by
  have hf : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  have hc : Nat.ceilRoot 2 n ≠ 0 := Nat.ceilRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  apply Nat.factorization_inj (mul_ne_zero hf hc) hn
  rw [Nat.factorization_mul hf hc, Nat.factorization_floorRoot, Nat.factorization_ceilRoot]
  ext p
  simp only [Finsupp.add_apply, Finsupp.floorDiv_apply, Finsupp.ceilDiv_apply,
    Nat.floorDiv_eq_div, Nat.ceilDiv_eq_add_pred_div]
  omega

/-- §4: exactly `m` residue classes square to zero. -/
theorem zeroCount_eq_squarePart : zeroCount n = squarePart n := by
  classical
  let r := Nat.ceilRoot 2 n
  let m := Nat.floorRoot 2 n
  have hr : 0 < r := Nat.pos_of_ne_zero (Nat.ceilRoot_ne_zero.mpr ⟨by norm_num, NeZero.ne n⟩)
  have hm : m * r = n := floorRoot_mul_ceilRoot n (NeZero.ne n)
  have hrm : r * m = n := by simpa [mul_comm] using hm
  have hlt (k : ℕ) (hk : k < m) : r * k < n := by
    rw [← hrm]
    exact Nat.mul_lt_mul_of_pos_left hk hr
  have hz (x : ZMod n) : x ^ 2 = 0 ↔ r ∣ x.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff,
      Nat.dvd_pow_iff_ceilRoot_dvd (by norm_num : (2 : ℕ) ≠ 0)]
  change #{x : ZMod n | x ^ 2 = 0} = m
  rw [← card_range m]
  symm
  refine card_bij (fun k _ => ((r * k : ℕ) : ZMod n)) ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and]
    apply (hz _).mpr
    rw [ZMod.val_natCast_of_lt (hlt k (mem_range.mp hk))]
    exact dvd_mul_right r k
  · intro a ha b hb hab
    have hv := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (hlt a (mem_range.mp ha)),
      ZMod.val_natCast_of_lt (hlt b (mem_range.mp hb))] at hv
    exact Nat.eq_of_mul_eq_mul_left hr hv
  · intro x hx
    have hdiv : r ∣ x.val := (hz x).mp (mem_filter.mp hx).2
    obtain ⟨k, hk⟩ := hdiv
    have hklt : k < m := by
      apply (Nat.mul_lt_mul_left hr).mp
      rw [← hk, hrm]
      exact x.val_lt
    refine ⟨k, mem_range.mpr hklt, ?_⟩
    rw [← hk, ZMod.natCast_zmod_val]

/-- The master decomposition with the elementary squareful correction evaluated. -/
theorem master_decomposition_squarePart :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      (∑ t ∈ (univ : Finset (ZMod n)).erase 0,
        (quadraticGauss t).im * cotWeight t) / 2 := by
  rw [master_decomposition, zeroCount_eq_squarePart]

/-- A periodic sum over `g` complete periods. -/
theorem sum_periodic_mul (M g : ℕ) (f : ℕ → ℂ) (hf : Function.Periodic f M) :
    ∑ k ∈ range (g * M), f k = (g : ℂ) * ∑ k ∈ range M, f k := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have hblock : ∑ k ∈ range M, f (g * M + k) = ∑ k ∈ range M, f k := by
      apply sum_congr rfl
      intro k _
      simpa [add_comm] using hf.nat_mul g k
    rw [hblock]
    push_cast
    ring

/-- Range-indexed Gauss sums permit a uniform statement as the modulus varies. -/
def gaussNat (M c : ℕ) : ℂ :=
  ∑ k ∈ range M, Complex.exp (2 * Real.pi * Complex.I * ((c * k ^ 2 : ℕ) : ℂ) / M)

theorem gaussNat_eq (c : ℕ) : gaussNat n c = quadraticGauss (c : ZMod n) := by
  unfold gaussNat quadraticGauss
  rw [sum_zmod_eq_range]
  apply sum_congr rfl
  intro k _
  have h := ZMod.stdAddChar_coe (N := n) (c * k ^ 2 : ℕ)
  simpa only [Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_pow] using h.symm

/-- §5.1: repeated residues reduce a Gauss sum to its smaller modulus. -/
theorem gaussNat_scale (g M c : ℕ) (hg : g ≠ 0) (hM : M ≠ 0) :
    gaussNat (g * M) (g * c) = (g : ℂ) * gaussNat M c := by
  let _ : NeZero M := ⟨hM⟩
  let f : ℕ → ℂ := fun k => ZMod.stdAddChar ((c : ZMod M) * (k : ZMod M) ^ 2)
  have hf : Function.Periodic f M := by
    intro k
    simp [f, Nat.cast_add]
  have he (k : ℕ) :
      Complex.exp (2 * Real.pi * Complex.I * (((g * c) * k ^ 2 : ℕ) : ℂ) /
        ((g * M : ℕ) : ℂ)) = f k := by
    dsimp [f]
    rw [show (c : ZMod M) * (k : ZMod M) ^ 2 = ((c * k ^ 2 : ℕ) : ZMod M) by push_cast; rfl]
    conv_rhs => rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg
    field_simp
  unfold gaussNat
  rw [sum_congr rfl (fun k _ => he k), sum_periodic_mul M g f hf]
  congr 1
  apply sum_congr rfl
  intro k _
  have h := ZMod.stdAddChar_coe (N := M) (c * k ^ 2 : ℕ)
  simpa only [f, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_pow] using h

/-- The primitive nonzero residues at modulus `M`. -/
def primitiveResidues (M : ℕ) : Finset ℕ :=
  {c ∈ range M | c ≠ 0 ∧ c.Coprime M}

theorem mem_primitiveResidues {M c : ℕ} :
    c ∈ primitiveResidues M ↔ c < M ∧ c ≠ 0 ∧ c.Coprime M := by
  simp [primitiveResidues]

omit [NeZero n] in
/-- The gcd of a residue in the block of denominator `M`. -/
theorem block_gcd {M c : ℕ} (hM : M ∣ n) (hc : c.Coprime M) :
    ((n / M) * c).gcd n = n / M := by
  conv_lhs => arg 2; rw [← Nat.div_mul_cancel hM]
  rw [Nat.gcd_mul_left, hc.gcd_eq_one, mul_one]

/-- The original residue is inside the interval when formed from a primitive block. -/
theorem block_lt {M c : ℕ} (hM : M ∣ n) (hc : c < M) :
    n / M * c < n := by
  have hMp : 0 < M := Nat.pos_of_dvd_of_pos hM (NeZero.pos n)
  have hgp : 0 < n / M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hM) hMp
  conv_rhs => rw [← Nat.div_mul_cancel hM]
  exact Nat.mul_lt_mul_of_pos_left hc hgp

/-- Uniqueness of the denominator-and-primitive-residue representation. -/
theorem block_injective {M c M' c' : ℕ} (hM : M ∣ n) (hM' : M' ∣ n)
    (hc : c.Coprime M) (hc' : c'.Coprime M')
    (h : n / M * c = n / M' * c') : M = M' ∧ c = c' := by
  have hg : n / M = n / M' := by
    have h' := congrArg (fun t => t.gcd n) h
    simpa only [block_gcd hM hc, block_gcd hM' hc'] using h'
  have hgp : 0 < n / M := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hM)
    (Nat.pos_of_dvd_of_pos hM (NeZero.pos n))
  have hMM' : M = M' := by
    apply Nat.eq_of_mul_eq_mul_left hgp
    rw [Nat.div_mul_cancel hM, hg, Nat.div_mul_cancel hM']
  refine ⟨hMM', ?_⟩
  rw [← hg] at h
  exact Nat.eq_of_mul_eq_mul_left hgp h

/-- Every nonzero residue has a primitive denominator-and-residue representation. -/
theorem block_surjective {t : ℕ} (ht : t ∈ (range n).erase 0) :
    ∃ M ∈ n.divisors, ∃ c ∈ primitiveResidues M, n / M * c = t := by
  have ht0 : t ≠ 0 := (mem_erase.mp ht).1
  have htlt : t < n := mem_range.mp (mem_erase.mp ht).2
  let g := t.gcd n
  let M := n / g
  let c := t / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right t (NeZero.pos n)
  have hgn : g ∣ n := Nat.gcd_dvd_right t n
  have hgt : g ∣ t := Nat.gcd_dvd_left t n
  have hMpos : 0 < M := Nat.div_pos (Nat.gcd_le_right t (NeZero.pos n)) hgpos
  have hMg : M * g = n := Nat.div_mul_cancel hgn
  have hcpos : 0 < c := Nat.div_pos (Nat.gcd_le_left n (Nat.pos_of_ne_zero ht0)) hgpos
  have hclt : c < M := (Nat.div_lt_div_right hgpos.ne' hgn).mpr htlt
  have hcM : c.Coprime M := Nat.coprime_div_gcd_div_gcd hgpos
  have hnM : n / M = g := Nat.div_eq_of_eq_mul_right hMpos hMg.symm
  refine ⟨M, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hgn, NeZero.ne n⟩,
    c, mem_primitiveResidues.mpr ⟨hclt, hcpos.ne', hcM⟩, ?_⟩
  rw [hnM, mul_comm, Nat.div_mul_cancel hgt]

/-- §5.4: reindex all nonzero residues by primitive denominator blocks. -/
theorem sum_gcd_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ t ∈ (range n).erase 0, f t =
      ∑ M ∈ n.divisors, ∑ c ∈ primitiveResidues M, f (n / M * c) := by
  classical
  rw [← sum_sigma n.divisors primitiveResidues (fun p : Σ _ : ℕ, ℕ => f (n / p.1 * p.2))]
  symm
  refine sum_bij (fun p _ => n / p.1 * p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    rcases mem_sigma.mp hp with ⟨hM, hc⟩
    rcases mem_primitiveResidues.mp hc with ⟨hclt, hc0, hcM⟩
    have hMdvd := (Nat.mem_divisors.mp hM).1
    have hgp : 0 < n / p.1 := Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos n) hMdvd)
      (Nat.pos_of_dvd_of_pos hMdvd (NeZero.pos n))
    exact mem_erase.mpr ⟨mul_ne_zero hgp.ne' hc0, mem_range.mpr (block_lt hMdvd hclt)⟩
  · intro p hp q hq hpq
    rcases mem_sigma.mp hp with ⟨hpM, hpc⟩
    rcases mem_sigma.mp hq with ⟨hqM, hqc⟩
    have h := block_injective (Nat.mem_divisors.mp hpM).1 (Nat.mem_divisors.mp hqM).1
      (mem_primitiveResidues.mp hpc).2.2 (mem_primitiveResidues.mp hqc).2.2 hpq
    cases p
    cases q
    simp_all
  · intro t ht
    obtain ⟨M, hM, c, hc, h⟩ := block_surjective ht
    exact ⟨⟨M, c⟩, mem_sigma.mpr ⟨hM, hc⟩, h⟩

/-- Convert a nonzero modular sum to the range of natural representatives. -/
theorem sum_nonzero_zmod_eq_range {A : Type*} [AddCancelCommMonoid A] (f : ZMod n → A) :
    ∑ t ∈ (univ : Finset (ZMod n)).erase 0, f t =
      ∑ t ∈ (range n).erase 0, f (t : ZMod n) := by
  classical
  have h := sum_zmod_eq_range f
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n)),
    ← sum_erase_add _ _ (mem_range.mpr (NeZero.pos n))] at h
  simp only [Nat.cast_zero] at h
  exact add_right_cancel h

/-- Natural-number version of the cotangent angle. -/
def cotNat (M c : ℕ) : ℝ := Real.cot (Real.pi * c / M)

/-- Split an interval into residue classes without any divisibility assumptions on the summand. -/
theorem sum_range_blocks {A : Type*} [AddCommMonoid A] (d g : ℕ) (hd : 0 < d) (f : ℕ → A) :
    ∑ c ∈ range (g * d), f c = ∑ a ∈ range d, ∑ k ∈ range g, f (a + d * k) := by
  classical
  rw [← sum_product (range d) (range g) (fun p : ℕ × ℕ => f (p.1 + d * p.2))]
  symm
  refine sum_bij (fun p _ => p.1 + d * p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨ha, hk⟩ := mem_product.mp hp
    have ha' := mem_range.mp ha
    have hk' : p.2 + 1 ≤ g := Nat.succ_le_iff.mpr (mem_range.mp hk)
    have hmul := Nat.mul_le_mul_left d hk'
    apply mem_range.mpr
    nlinarith
  · intro p hp q hq hpq
    obtain ⟨hpa, hpk⟩ := mem_product.mp hp
    obtain ⟨hqa, hqk⟩ := mem_product.mp hq
    have ha := congrArg (fun c => c % d) hpq
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hpa),
      Nat.mod_eq_of_lt (mem_range.mp hqa)] at ha
    have hk : p.2 = q.2 := by
      apply Nat.eq_of_mul_eq_mul_left hd
      omega
    exact Prod.ext ha hk
  · intro c hc
    have hclt := mem_range.mp hc
    have hq : c / d < g := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa [mul_comm] using hclt
    exact ⟨(c % d, c / d), mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt c hd),
      mem_range.mpr hq⟩, Nat.mod_add_div c d⟩

/-- Unrestricted lifting of a periodic weighted cotangent sum, the distribution step
before imposing coprimality and Euler factors. -/
theorem periodic_cotangent_lift (d g : ℕ) (hd : 0 < d) (hg : 0 < g)
    (f : ℕ → ℝ) (hf : Function.Periodic f d) (hf0 : f 0 = 0) :
    ∑ c ∈ range (g * d), f c * cotNat (g * d) c =
      (g : ℝ) * ∑ a ∈ range d, f a * cotNat d a := by
  classical
  let _ : NeZero g := ⟨hg.ne'⟩
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  rw [sum_range_blocks d g hd, mul_sum]
  apply sum_congr rfl
  intro a ha
  have hap := mem_range.mp ha
  have hfa (k : ℕ) : f (a + d * k) = f a := by
    simpa [mul_comm] using hf.nat_mul k a
  simp_rw [hfa]
  by_cases ha0 : a = 0
  · simp [ha0, hf0]
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha0)
  let θ : ℝ := Real.pi * a / (g * d)
  have hθ : 0 < θ := div_pos (mul_pos Real.pi_pos ha') (mul_pos hg' hd')
  have hgθ : (g : ℝ) * θ = Real.pi * a / d := by
    dsimp [θ]
    field_simp
  have hθlt : (g : ℝ) * θ < Real.pi := by
    rw [hgθ]
    apply (div_lt_iff₀ hd').mpr
    exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hap) Real.pi_pos
  have hcot (k : ℕ) : cotNat (g * d) (a + d * k) = Real.cot (θ + Real.pi * k / g) := by
    unfold cotNat
    congr 1
    dsimp [θ]
    push_cast
    field_simp
  simp_rw [hcot]
  rw [← mul_sum, cot_distribution θ hθ hθlt, hgθ]
  unfold cotNat
  ring

omit [NeZero n] in
theorem cotWeight_natCast {t : ℕ} (ht : t < n) :
    cotWeight (t : ZMod n) = cotNat n t := by
  simp [cotWeight, cotNat, ZMod.val_natCast_of_lt ht]

omit [NeZero n] in
theorem cotNat_scale (g M c : ℕ) (hg : g ≠ 0) :
    cotNat (g * M) (g * c) = cotNat M c := by
  unfold cotNat
  congr 1
  push_cast
  have hg' : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  field_simp

/-- The modulus-`M` primitive cotangent/Gauss block. -/
def primitiveBlock (M : ℕ) : ℝ :=
  ∑ c ∈ primitiveResidues M, (gaussNat M c).im * cotNat M c

/-- The regrouping of §5.4 before any Gauss-sum or class-number evaluations. -/
theorem cotangent_gcd_blocks :
    ∑ t ∈ (univ : Finset (ZMod n)).erase 0, (quadraticGauss t).im * cotWeight t =
      ∑ M ∈ n.divisors, (n / M : ℕ) * primitiveBlock M := by
  classical
  rw [sum_nonzero_zmod_eq_range]
  have hv : ∀ t ∈ (range n).erase 0,
      (quadraticGauss (t : ZMod n)).im * cotWeight (t : ZMod n) =
        (gaussNat n t).im * cotNat n t := by
    intro t ht
    rw [← gaussNat_eq, cotWeight_natCast (mem_range.mp (mem_erase.mp ht).2)]
  rw [sum_congr rfl hv, sum_gcd_blocks]
  apply sum_congr rfl
  intro M hM
  have hMdvd := (Nat.mem_divisors.mp hM).1
  have hMp : 0 < M := Nat.pos_of_dvd_of_pos hMdvd (NeZero.pos n)
  have hg : n / M ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hMdvd) hMp).ne'
  unfold primitiveBlock
  rw [mul_sum]
  apply sum_congr rfl
  intro c hc
  have hnm : n = (n / M) * M := (Nat.div_mul_cancel hMdvd).symm
  have hG : gaussNat n (n / M * c) = (n / M : ℕ) * gaussNat M c := by
    conv_lhs => arg 1; rw [hnm]
    exact gaussNat_scale _ _ _ hg hMp.ne'
  have hcot : cotNat n (n / M * c) = cotNat M c := by
    conv_lhs => arg 1; rw [hnm]
    exact cotNat_scale _ _ _ hg
  rw [hG, hcot]
  simp [Complex.mul_im, mul_assoc]

/-- Discriminants `-M` are exactly the positive `M` congruent to zero or three mod four. -/
def isNegativeDiscriminantAbs (M : ℕ) : Prop := 0 < M ∧ (M % 4 = 0 ∨ M % 4 = 3)

instance : DecidablePred isNegativeDiscriminantAbs := fun M =>
  inferInstanceAs (Decidable (0 < M ∧ (M % 4 = 0 ∨ M % 4 = 3)))

/-- Translate the unsigned divisor convention to the usual negative discriminants. -/
theorem negativeDiscriminantAbs_iff (M : ℕ) :
    isNegativeDiscriminantAbs M ↔
      (-(M : ℤ) < 0 ∧ ((-(M : ℤ)) % 4 = 0 ∨ (-(M : ℤ)) % 4 = 1)) := by
  have hmod : ((M % 4 : ℕ) : ℤ) = (M : ℤ) % 4 := by norm_cast
  unfold isNegativeDiscriminantAbs
  omega

/-- §5.3: every negative discriminant is a square multiple of a negative fundamental one. -/
theorem exists_fundamental_factor (M : ℕ) (hM : isNegativeDiscriminantAbs M) :
    ∃ d s : ℕ, 0 < d ∧ 0 < s ∧ Int.IsFundamentalDiscr (-(d : ℤ)) ∧ d * s ^ 2 = M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hf : Int.IsFundamentalDiscr (-(M : ℤ))
    · exact ⟨M, 1, hM.1, by norm_num, hf, by simp⟩
    · have hD := (negativeDiscriminantAbs_iff M).mp hM
      have hp : ∃ p : ℕ, p.Prime ∧ ∃ e : ℤ,
          -(M : ℤ) = (p : ℤ) ^ 2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
        simpa only [Int.isFundamentalDiscr_iff_forall_prime, hD.2, true_and,
          not_forall, not_not, exists_prop] using hf
      obtain ⟨p, hp, e, he, hemod⟩ := hp
      have heNeg : e < 0 := by
        have hpp : (0 : ℤ) < (p : ℤ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hp.pos)
        nlinarith
      have heabs : e = -(e.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_neg heNeg]
        ring
      have hd : 0 < e.natAbs := Int.natAbs_pos.mpr (ne_of_lt heNeg)
      have hfac : p ^ 2 * e.natAbs = M := by
        rw [heabs] at he
        have h : (p : ℤ) ^ 2 * (e.natAbs : ℤ) = M := by nlinarith [he]
        exact_mod_cast h
      have hlt : e.natAbs < M := by
        rw [← hfac]
        have hp2 : 1 < p ^ 2 := by nlinarith [hp.two_le]
        simpa using Nat.mul_lt_mul_of_pos_right hp2 hd
      have hdDisc : isNegativeDiscriminantAbs e.natAbs := by
        apply (negativeDiscriminantAbs_iff _).mpr
        rw [← heabs]
        exact ⟨heNeg, hemod⟩
      obtain ⟨d, s, hdp, hsp, hdf, hds⟩ := ih e.natAbs hlt hdDisc
      refine ⟨d, p * s, hdp, mul_pos hp.pos hsp, hdf, ?_⟩
      rw [mul_pow]
      calc
        _ = p ^ 2 * (d * s ^ 2) := by ring
        _ = M := by rw [hds, hfac]

theorem discriminant_square_mul (D : ℤ) (s : ℕ) (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (D * (s : ℤ) ^ 2) % 4 = 0 ∨ (D * (s : ℤ) ^ 2) % 4 = 1 := by
  rw [Int.mul_emod, Int.sq_emod_four]
  rcases hD with hD | hD
  · simp [hD]
  · simp only [hD, one_mul]
    omega

/-- Fundamental discriminants admit no further discriminant square factor. -/
theorem fundamental_square_factor_eq_one {D E : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hE : E % 4 = 0 ∨ E % 4 = 1) (s : ℕ) (h : D = E * (s : ℤ) ^ 2) : s = 1 := by
  by_contra hs
  obtain ⟨p, hp, k, hk⟩ := Nat.exists_prime_and_dvd hs
  have hfor := (Int.isFundamentalDiscr_iff_forall_prime.mp hD).2 p hp
  apply hfor
  refine ⟨E * (k : ℤ) ^ 2, ?_, discriminant_square_mul E k hE⟩
  rw [h, hk]
  push_cast
  ring

theorem discriminant_of_odd_square_mul (E : ℤ) (s : ℕ) (hs : s % 2 = 1)
    (hE : (E * (s : ℤ) ^ 2) % 4 = 0 ∨ (E * (s : ℤ) ^ 2) % 4 = 1) :
    E % 4 = 0 ∨ E % 4 = 1 := by
  have hs' : (s : ℤ) % 2 = 1 := by exact_mod_cast hs
  rw [Int.mul_emod, Int.sq_emod_four] at hE
  simpa [hs'] using hE

/-- The discriminant/conductor factorization used to collapse the double sum is unique. -/
theorem fundamental_factor_unique {d d' s s' : ℕ}
    (hs : 0 < s) (hs' : 0 < s')
    (hdf : Int.IsFundamentalDiscr (-(d : ℤ)))
    (hd'f : Int.IsFundamentalDiscr (-(d' : ℤ)))
    (h : d * s ^ 2 = d' * s' ^ 2) : d = d' ∧ s = s' := by
  let g := s.gcd s'
  let u := s / g
  let v := s' / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s' hs
  have hsu : s = g * u := by simpa [g, u, mul_comm] using (Nat.div_mul_cancel (Nat.gcd_dvd_left s s')).symm
  have hsv : s' = g * v := by simpa [g, v, mul_comm] using (Nat.div_mul_cancel (Nat.gcd_dvd_right s s')).symm
  have hu : 0 < u := Nat.div_pos (Nat.gcd_le_left s' hs) hg
  have hv : 0 < v := Nat.div_pos (Nat.gcd_le_right s hs') hg
  have huv : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have heq : d * u ^ 2 = d' * v ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hg : 0 < g ^ 2)
    calc
      _ = d * s ^ 2 := by rw [hsu]; ring
      _ = d' * s' ^ 2 := h
      _ = _ := by rw [hsv]; ring
  have hdiv : v ^ 2 ∣ d := (huv.symm.pow 2 2).dvd_of_dvd_mul_right (by
    rw [heq]
    exact dvd_mul_left _ _)
  obtain ⟨e, hde⟩ := hdiv
  have hd'e : d' = u ^ 2 * e := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hv : 0 < v ^ 2)
    rw [← heq, hde]
    ring
  have hodd : u % 2 = 1 ∨ v % 2 = 1 := by
    by_contra hn
    have hu2 : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
    have hv2 : 2 ∣ v := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.eq_one_of_dvd_coprimes huv hu2 hv2
    omega
  have hdint : -(d : ℤ) = -(e : ℤ) * (v : ℤ) ^ 2 := by rw [hde]; push_cast; ring
  have hd'int : -(d' : ℤ) = -(e : ℤ) * (u : ℤ) ^ 2 := by rw [hd'e]; push_cast; ring
  have heDisc : (-(e : ℤ)) % 4 = 0 ∨ (-(e : ℤ)) % 4 = 1 := by
    rcases hodd with huodd | hvodd
    · apply discriminant_of_odd_square_mul (-(e : ℤ)) u huodd
      rw [← hd'int]
      exact hd'f.1
    · apply discriminant_of_odd_square_mul (-(e : ℤ)) v hvodd
      rw [← hdint]
      exact hdf.1
  have hu1 := fundamental_square_factor_eq_one hd'f heDisc u hd'int
  have hv1 := fundamental_square_factor_eq_one hdf heDisc v hdint
  constructor
  · calc
      d = e := by simpa [hv1] using hde
      _ = d' := by simpa [hu1] using hd'e.symm
  · rw [hsu, hsv, hu1, hv1]

/-- The actual finite divisor set in the requested closed formula. -/
def discriminantDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter isNegativeDiscriminantAbs

def fundamentalDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact n.divisors.filter (fun d => Int.IsFundamentalDiscr (-(d : ℤ)))

def conductors (n d : ℕ) : Finset ℕ :=
  {s ∈ range (n + 1) | 0 < s ∧ d * s ^ 2 ∣ n}

theorem mem_conductors {n d s : ℕ} (hn : 0 < n) (hd : 0 < d) :
    s ∈ conductors n d ↔ 0 < s ∧ d * s ^ 2 ∣ n := by
  simp only [conductors, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hle : d * s ^ 2 ≤ n := Nat.le_of_dvd hn h.2
    have hs2 : s ≤ s ^ 2 := by nlinarith
    have hd2 : s ^ 2 ≤ d * s ^ 2 := Nat.le_mul_of_pos_left _ hd
    exact ⟨by omega, h⟩

theorem negativeDiscriminantAbs_square_mul {d s : ℕ}
    (hd : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    isNegativeDiscriminantAbs (d * s ^ 2) := by
  apply (negativeDiscriminantAbs_iff _).mpr
  have hpos : 0 < d * s ^ 2 := mul_pos hd.1 (Nat.pow_pos hs)
  have hdisc := discriminant_square_mul (-(d : ℤ)) s
    ((negativeDiscriminantAbs_iff d).mp hd).2
  have heq : -((d * s ^ 2 : ℕ) : ℤ) = -(d : ℤ) * (s : ℤ) ^ 2 := by push_cast; ring
  exact ⟨neg_neg_of_pos (by exact_mod_cast hpos), by rwa [heq]⟩

/-- §6.2: the double sum over fundamental discriminants and conductors is a single
sum over all discriminants, with the bijection proved explicitly. -/
theorem sum_discriminant_reindex {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ M ∈ discriminantDivisors n, f M =
      ∑ d ∈ fundamentalDivisors n, ∑ s ∈ conductors n d, f (d * s ^ 2) := by
  classical
  rw [← sum_sigma (fundamentalDivisors n) (conductors n)
    (fun p : Σ _ : ℕ, ℕ => f (p.1 * p.2 ^ 2))]
  symm
  refine sum_bij (fun p _ => p.1 * p.2 ^ 2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨hd, hs⟩ := mem_sigma.mp hp
    obtain ⟨hdn, hdf⟩ := mem_filter.mp hd
    have hdp : 0 < p.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdn).1 (NeZero.pos n)
    obtain ⟨hsp, hdsn⟩ := (mem_conductors (NeZero.pos n) hdp).mp hs
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hdsn, NeZero.ne n⟩, ?_⟩
    apply negativeDiscriminantAbs_square_mul _ hsp
    exact (negativeDiscriminantAbs_iff p.1).mpr ⟨by omega, hdf.1⟩
  · intro p hp q hq hpq
    obtain ⟨hpd, hps⟩ := mem_sigma.mp hp
    obtain ⟨hqd, hqs⟩ := mem_sigma.mp hq
    obtain ⟨hpdn, hpdf⟩ := mem_filter.mp hpd
    obtain ⟨hqdn, hqdf⟩ := mem_filter.mp hqd
    have hpdp : 0 < p.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hpdn).1 (NeZero.pos n)
    have hqdp : 0 < q.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hqdn).1 (NeZero.pos n)
    have h := fundamental_factor_unique ((mem_conductors (NeZero.pos n) hpdp).mp hps).1
      ((mem_conductors (NeZero.pos n) hqdp).mp hqs).1 hpdf hqdf hpq
    cases p
    cases q
    simp_all
  · intro M hM
    obtain ⟨hMn, hMD⟩ := mem_filter.mp hM
    obtain ⟨d, s, hdp, hsp, hdf, hds⟩ := exists_fundamental_factor M hMD
    have hdn : d ∣ n := dvd_trans (by rw [← hds]; exact dvd_mul_right _ _) (Nat.mem_divisors.mp hMn).1
    refine ⟨⟨d, s⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdn, NeZero.ne n⟩, hdf⟩,
      (mem_conductors (NeZero.pos n) hdp).mpr ⟨hsp, ?_⟩⟩, hds⟩
    rw [hds]
    exact (Nat.mem_divisors.mp hMn).1

/-- The character read off from the imaginary part of the primitive Gauss evaluation.
For even `M`, primitive residues `c` are odd, so Mathlib's Jacobi symbol suffices. -/
def gaussCharacter (M c : ℕ) : ℝ :=
  if M % 4 = 3 then (jacobiSym (c : ℤ) M : ℝ)
  else if M % 4 = 0 then (jacobiSym (-(M : ℤ)) c : ℝ) else 0

/-- Finite character cotangent sum at modulus `M`. -/
def characterCot (M : ℕ) : ℝ :=
  ∑ c ∈ primitiveResidues M, gaussCharacter M c * cotNat M c

/-- Genuine primitive positive binary quadratic forms of fixed discriminant. -/
structure PrimitivePositiveForm (Δ : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  positive : 0 < a
  discriminant : b ^ 2 - 4 * a * c = Δ
  primitive : Int.gcd a (Int.gcd b c : ℤ) = 1

def PrimitivePositiveForm.eval {Δ : ℤ} (f : PrimitivePositiveForm Δ) (v : Fin 2 → ℤ) : ℤ :=
  f.a * v 0 ^ 2 + f.b * v 0 * v 1 + f.c * v 1 ^ 2

/-- Proper equivalence, generated by determinant-one integral changes of variables. -/
def properChange {Δ : ℤ} (f g : PrimitivePositiveForm Δ) : Prop :=
  ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    ∀ v : Fin 2 → ℤ, f.eval v = g.eval ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)

theorem properChange_refl {Δ : ℤ} (f : PrimitivePositiveForm Δ) : properChange f f := by
  refine ⟨1, ?_⟩
  intro v
  simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem properChange_symm {Δ : ℤ} {f g : PrimitivePositiveForm Δ} (h : properChange f g) :
    properChange g f := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A⁻¹, ?_⟩
  intro v
  have hv := hA (((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at hv
  exact hv.symm

theorem properChange_trans {Δ : ℤ} {f g h : PrimitivePositiveForm Δ}
    (hfg : properChange f g) (hgh : properChange g h) : properChange f h := by
  obtain ⟨A, hA⟩ := hfg
  obtain ⟨B, hB⟩ := hgh
  refine ⟨B * A, ?_⟩
  intro v
  rw [hA, hB, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

/-- The generated relation is exactly ordinary proper equivalence, not a larger quotient. -/
theorem properChange_eqvGen_iff {Δ : ℤ} (f g : PrimitivePositiveForm Δ) :
    Relation.EqvGen properChange f g ↔ properChange f g := by
  constructor
  · intro h
    induction h with
    | rel f g h => exact h
    | refl f => exact properChange_refl f
    | symm f g h ih => exact properChange_symm ih
    | trans f g h hfg hgh ihfg ihgh => exact properChange_trans ihfg ihgh
  · intro h
    exact Relation.EqvGen.rel f g h

def FormClass (Δ : ℤ) :=
  Quotient (Relation.EqvGen.setoid (properChange (Δ := Δ)))

/-- Class number defined by proper classes of primitive positive forms, independently of
Gauss sums and the residue sum. -/
def orderClassNumber (Δ : ℤ) : ℕ := Nat.card (FormClass Δ)

/-- Standard unit count for an imaginary quadratic order, identified below with the
cardinality of the integral quadratic order's unit group. -/
def orderUnitCount (Δ : ℤ) : ℕ := if Δ = -3 then 6 else if Δ = -4 then 4 else 2

def classRatio (Δ : ℤ) : ℝ := (orderClassNumber Δ : ℝ) / orderUnitCount Δ

/-- Exact classical Gauss sign input; this proposition is not assumed as an axiom. -/
def GaussSignEvaluation : Prop := ∀ M : ℕ, 0 < M → ∀ c ∈ primitiveResidues M,
  (gaussNat M c).im = Real.sqrt M * gaussCharacter M c

/-- The finite cotangent form of the imaginary quadratic order class-number formula.
This combines the primitive Dirichlet formula, Euler factors, and the order formula.
This proposition is proved by the primitive and conductor arguments below. -/
def OrderClassNumberCotangent : Prop := ∀ M : ℕ, isNegativeDiscriminantAbs M →
  characterCot M = 4 * Real.sqrt M * classRatio (-(M : ℤ))

/-- The negative fundamental Kronecker character in terms of Mathlib's Jacobi symbol.
The even-denominator case is handled by the zero value on even arguments. -/
def fundamentalCharacter (d c : ℕ) : ℝ :=
  if d % 4 = 3 then (jacobiSym (c : ℤ) d : ℝ)
  else if d % 4 = 0 ∧ c % 2 = 1 then (jacobiSym (-(d : ℤ)) c : ℝ) else 0

def eulerProduct (d s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, (1 - fundamentalCharacter d p / p)

def conductorCorrection (d s : ℕ) : ℝ := (s : ℝ) * eulerProduct d s

/-- A Dirichlet character vanishes on primes dividing its level. -/
theorem character_prime_divisor_zero {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : p.Prime) (hpd : p ∣ d) : χ (p : ZMod d) = 0 := by
  apply χ.map_nonunit
  intro hu
  have hc := (ZMod.isUnit_iff_coprime p d).mp hu
  exact (hp.coprime_iff_not_dvd.mp hc) hpd

/-- The Euler-factor identity at `s = 1` is already available in Mathlib. -/
theorem LFunction_changeLevel_one {d M : ℕ} [NeZero d] [NeZero M]
    (hdM : d ∣ M) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) :
    (DirichletCharacter.changeLevel hdM χ).LFunction 1 =
      χ.LFunction 1 * ∏ p ∈ M.primeFactors, (1 - χ (p : ZMod d) / p) := by
  rw [DirichletCharacter.LFunction_changeLevel hdM χ (Or.inl hχ)]
  simp_rw [Complex.cpow_neg_one, ← div_eq_mul_inv]

/-- Removing the primes of the conductor from the Euler product leaves precisely
the primes of the square multiplier, as in §5.5. -/
theorem conductor_primeFactor_product {d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0)
    (χ : DirichletCharacter ℂ d) :
    ∏ p ∈ (d * s ^ 2).primeFactors, (1 - χ (p : ZMod d) / p) =
      ∏ p ∈ s.primeFactors, (1 - χ (p : ZMod d) / p) := by
  rw [Nat.primeFactors_mul hd (pow_ne_zero _ hs), Nat.primeFactors_pow s (by norm_num)]
  symm
  apply prod_subset subset_union_right
  intro p hp hps
  have hpd : p ∈ d.primeFactors := (mem_union.mp hp).resolve_right hps
  rw [character_prime_divisor_zero χ (Nat.mem_primeFactors.mp hpd).1
    (Nat.mem_primeFactors.mp hpd).2.1]
  simp

/-- Exact specialization of Mathlib's imprimitive Euler-factor theorem to `M = d s²`. -/
theorem LFunction_square_conductor_one {d s : ℕ} [NeZero d] [NeZero s]
    [NeZero (d * s ^ 2)] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1) :
    (DirichletCharacter.changeLevel (dvd_mul_right d (s ^ 2)) χ).LFunction 1 =
      χ.LFunction 1 * ∏ p ∈ s.primeFactors, (1 - χ (p : ZMod d) / p) := by
  rw [LFunction_changeLevel_one _ χ hχ,
    conductor_primeFactor_product (NeZero.ne d) (NeZero.ne s) χ]

/-- The primitive class-number formula in finite cotangent form. -/
def FundamentalClassNumberCotangent : Prop := ∀ d : ℕ, 0 < d →
  Int.IsFundamentalDiscr (-(d : ℤ)) →
    characterCot d = 4 * Real.sqrt d * classRatio (-(d : ℤ))

/-- The elementary imprimitive cotangent lifting/Euler-factor identity. -/
def CotangentConductorFormula : Prop := ∀ d s : ℕ, 0 < d → 0 < s →
  Int.IsFundamentalDiscr (-(d : ℤ)) →
    characterCot (d * s ^ 2) = (s : ℝ) ^ 2 * characterCot d * eulerProduct d s

/-- Cox's class-number formula for orders, in the form after dividing by unit counts. -/
def OrderClassNumberFormula : Prop := ∀ d s : ℕ, 0 < d → 0 < s →
  Int.IsFundamentalDiscr (-(d : ℤ)) →
    classRatio (-((d * s ^ 2 : ℕ) : ℤ)) = classRatio (-(d : ℤ)) * conductorCorrection d s

/-- §5.5--§6.1: the separate primitive, conductor, and order inputs give the needed
cotangent class-number identity. -/
theorem orderClassNumberCotangent_of_inputs (hF : FundamentalClassNumberCotangent)
    (hL : CotangentConductorFormula) (hO : OrderClassNumberFormula) :
    OrderClassNumberCotangent := by
  intro M hM
  obtain ⟨d, s, hdp, hsp, hdf, hds⟩ := exists_fundamental_factor M hM
  rw [← hds, hL d s hdp hsp hdf, hF d hdp hdf, hO d s hdp hsp hdf]
  have hsqrt : Real.sqrt ((d * s ^ 2 : ℕ) : ℝ) = Real.sqrt d * s := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg d),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg s)]
  rw [hsqrt]
  unfold conductorCorrection
  ring

/-- §6.1--§6.2: collapse the conductor factors into class numbers of orders. -/
theorem collapse_order_sum (hO : OrderClassNumberFormula) :
    ∑ M ∈ discriminantDivisors n, classRatio (-(M : ℤ)) =
      ∑ d ∈ fundamentalDivisors n, classRatio (-(d : ℤ)) *
        ∑ s ∈ conductors n d, conductorCorrection d s := by
  classical
  rw [sum_discriminant_reindex]
  apply sum_congr rfl
  intro d hd
  obtain ⟨hdn, hdf⟩ := mem_filter.mp hd
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdn).1 (NeZero.pos n)
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  exact hO d s hdp ((mem_conductors (NeZero.pos n) hdp).mp hs).1 hdf

/-- Substitute the signed Gauss evaluation into the primitive block. -/
theorem primitiveBlock_character (hG : GaussSignEvaluation) (M : ℕ) (hM : 0 < M) :
    primitiveBlock M = Real.sqrt M * characterCot M := by
  unfold primitiveBlock characterCot
  rw [mul_sum]
  apply sum_congr rfl
  intro c hc
  rw [hG M hM c hc]
  ring

theorem primitiveBlock_classNumber (hG : GaussSignEvaluation)
    (hC : OrderClassNumberCotangent) (M : ℕ) (hM : 0 < M) :
    primitiveBlock M = if isNegativeDiscriminantAbs M then
      4 * (M : ℝ) * classRatio (-(M : ℤ)) else 0 := by
  classical
  rw [primitiveBlock_character hG M hM]
  split_ifs with hD
  · rw [hC M hD]
    calc
      _ = 4 * (Real.sqrt M * Real.sqrt M) * classRatio (-(M : ℤ)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg M)]
  · have h0 : M % 4 ≠ 0 := fun h => hD ⟨hM, Or.inl h⟩
    have h3 : M % 4 ≠ 3 := fun h => hD ⟨hM, Or.inr h⟩
    simp [characterCot, gaussCharacter, h0, h3]

/-- Assemble all divisor blocks after the two explicitly named classical inputs. -/
theorem cotangent_classNumber_sum (hG : GaussSignEvaluation)
    (hC : OrderClassNumberCotangent) :
    ∑ t ∈ (univ : Finset (ZMod n)).erase 0, (quadraticGauss t).im * cotWeight t =
      4 * (n : ℝ) * ∑ M ∈ discriminantDivisors n, classRatio (-(M : ℤ)) := by
  classical
  rw [cotangent_gcd_blocks]
  have hterm : ∀ M ∈ n.divisors,
      (n / M : ℕ) * primitiveBlock M =
        if isNegativeDiscriminantAbs M then 4 * (n : ℝ) * classRatio (-(M : ℤ)) else 0 := by
    intro M hM
    have hMdvd := (Nat.mem_divisors.mp hM).1
    have hMp := Nat.pos_of_dvd_of_pos hMdvd (NeZero.pos n)
    rw [primitiveBlock_classNumber hG hC M hMp]
    split_ifs with hD
    · have hm : ((n / M : ℕ) : ℝ) * (M : ℝ) = n := by
        exact_mod_cast Nat.div_mul_cancel hMdvd
      calc
        _ = 4 * (((n / M : ℕ) : ℝ) * M) * classRatio (-(M : ℤ)) := by ring
        _ = _ := by rw [hm]
    · simp
  rw [sum_congr rfl hterm]
  simp only [← sum_filter, discriminantDivisors, mul_sum]

/-- A conditional assembly lemma; both inputs are proved below. -/
theorem closed_formula_of_classical_inputs (hG : GaussSignEvaluation)
    (hC : OrderClassNumberCotangent) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) := by
  rw [master_decomposition_squarePart, cotangent_classNumber_sum hG hC]
  unfold classRatio
  ring

/-- Assembly lemma with the standard identities exposed separately. -/
theorem closed_formula_of_standard_inputs (hG : GaussSignEvaluation)
    (hF : FundamentalClassNumberCotangent) (hL : CotangentConductorFormula)
    (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) :=
  closed_formula_of_classical_inputs hG (orderClassNumberCotangent_of_inputs hF hL hO)

/-- The expanded formula from the source, before the order-class-number collapse. -/
theorem expanded_formula_of_standard_inputs (hG : GaussSignEvaluation)
    (hF : FundamentalClassNumberCotangent) (hL : CotangentConductorFormula)
    (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ d ∈ fundamentalDivisors n, classRatio (-(d : ℤ)) *
        ∑ s ∈ conductors n d, conductorCorrection d s := by
  have h := closed_formula_of_standard_inputs (n := n) hG hF hL hO
  change (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
    2 * n * ∑ M ∈ discriminantDivisors n, classRatio (-(M : ℤ)) at h
  rw [collapse_order_sum hO] at h
  exact h

/-- A field of signature (0, 1) has regulator one. -/
theorem regulator_eq_one_of_signature (K : Type*) [Field K] [NumberField K]
    (hR : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hC : NumberField.InfinitePlace.nrComplexPlaces K = 1) :
    NumberField.Units.regulator K = 1 := by
  classical
  have hc : Fintype.card (NumberField.InfinitePlace K) = 1 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
  have hs : ∀ a b : NumberField.InfinitePlace K, a = b :=
    Fintype.card_le_one_iff.mp (by omega)
  let : IsEmpty {w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    ⟨fun w => w.property (hs _ _)⟩
  rw [NumberField.Units.regulator_eq_det', Matrix.det_isEmpty]
  norm_num
theorem residue_imaginary_quadratic (K : Type*) [Field K] [NumberField K]
    (hR : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hC : NumberField.InfinitePlace.nrComplexPlaces K = 1) :
    NumberField.dedekindZeta_residue K =
      2 * Real.pi * NumberField.classNumber K / (NumberField.Units.torsionOrder K * Real.sqrt |(NumberField.discr K : ℝ)|) := by
  rw [NumberField.dedekindZeta_residue_def, hR, hC, regulator_eq_one_of_signature K hR hC]
  simp


/-- Mathlib's analytic class-number formula specialized to signature (0, 1). -/
theorem imaginary_quadratic_class_number_limit (K : Type*) [Field K] [NumberField K]
    (hR : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (hC : NumberField.InfinitePlace.nrComplexPlaces K = 1) :
    Filter.Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((2 * Real.pi * NumberField.classNumber K /
        (NumberField.Units.torsionOrder K * Real.sqrt |(NumberField.discr K : ℝ)|) : ℝ) : ℂ)) := by
  rw [← residue_imaginary_quadratic K hR hC]
  exact NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

theorem mobius_weighted_inverse {R : Type*} [CommRing R] (f : ArithmeticFunction R)
    (hf1 : f 1 = 1) (hf : ∀ a b, f (a * b) = f a * f b) :
    (ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction R) f) * f = 1 := by
  ext M
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction R) f) a * f b)]
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply]
  have ht : ∀ q ∈ M.divisors,
      (ArithmeticFunction.moebius q : R) * f q * f (M / q) =
        (ArithmeticFunction.moebius q : R) * f M := by
    intro q hq
    rw [mul_assoc, ← hf, Nat.mul_div_cancel' (Nat.mem_divisors.mp hq).1]
  rw [sum_congr rfl ht, ← sum_mul]
  have hmu : ∑ q ∈ M.divisors, (ArithmeticFunction.moebius q : R) =
      (1 : ArithmeticFunction R) M := by
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] using
      congrArg (fun a : ArithmeticFunction R => a M)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := R))
  rw [hmu]
  by_cases hM : M = 1 <;> simp [hM, hf1]

theorem mobius_euler_product {R : Type*} [CommRing R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (M : ℕ) (hM : M ≠ 0) :
    ∑ q ∈ M.divisors, (ArithmeticFunction.moebius q : R) * f q =
      ∏ p ∈ M.primeFactors, (1 - f p) := by
  let h := ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction R) f
  have hm : h.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast.pmul hf
  have he : (ArithmeticFunction.zeta : ArithmeticFunction R) * h =
      ArithmeticFunction.prodPrimeFactors (fun p => 1 - f p) := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ (ArithmeticFunction.isMultiplicative_zeta.natCast.mul hm)
      _ (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)).mpr
    intro p k hp
    rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    by_cases hk : k = 0
    · simp [hk, h, hf.1]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_pow p (Nat.succ_ne_zero l), hp.primeFactors, prod_singleton]
    have hs : ∀ l : ℕ, ∑ j ∈ range (l + 2),
        (ArithmeticFunction.moebius (p ^ j) : R) * f (p ^ j) = 1 - f p := by
      intro l
      induction l with
      | zero => simp [sum_range_succ, hf.1, ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]
      | succ l ih =>
        rw [show l + 1 + 2 = (l + 2) + 1 by omega, sum_range_succ, ih,
          ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show l + 2 ≠ 1 by omega]
    simpa [h, ArithmeticFunction.pmul_apply] using hs l
  have heM := congrArg (fun a : ArithmeticFunction R => a M) he
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, h, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.prodPrimeFactors_apply hM] using heM

/-- Cotangent sum without the coprimality restriction. -/
def totalCharacterCot (f : ArithmeticFunction ℝ) (M : ℕ) : ℝ :=
  ∑ c ∈ range M, f c * cotNat M c

/-- Cotangent sum restricted to primitive representatives. -/
def primitiveCharacterCot (f : ArithmeticFunction ℝ) (M : ℕ) : ℝ :=
  ∑ c ∈ primitiveResidues M, f c * cotNat M c

theorem totalCharacterCot_gcd_blocks (f : ArithmeticFunction ℝ)
    (hf : ∀ a b, f (a * b) = f a * f b) (M : ℕ) (hM : 0 < M) :
    totalCharacterCot f M =
      ∑ q ∈ M.divisors, f (M / q) * primitiveCharacterCot f q := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  unfold totalCharacterCot
  have h0 : f 0 * cotNat M 0 = 0 := by simp
  rw [← sum_erase_add _ _ (mem_range.mpr hM), h0, add_zero,
    sum_gcd_blocks (n := M)]
  apply sum_congr rfl
  intro q hq
  have hqdvd := (Nat.mem_divisors.mp hq).1
  have hqp := Nat.pos_of_dvd_of_pos hqdvd hM
  have hg : M / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hM hqdvd) hqp).ne'
  unfold primitiveCharacterCot
  rw [mul_sum]
  apply sum_congr rfl
  intro c hc
  rw [hf]
  have hcot : cotNat M (M / q * c) = cotNat q c := by
    simpa only [Nat.div_mul_cancel hqdvd] using cotNat_scale (M / q) q c hg
  rw [hcot]
  ring

theorem primitiveCharacterCot_moebius (f : ArithmeticFunction ℝ)
    (hf1 : f 1 = 1) (hf : ∀ a b, f (a * b) = f a * f b) (M : ℕ) :
    primitiveCharacterCot f M =
      ∑ q ∈ M.divisors, (ArithmeticFunction.moebius q : ℝ) * f q *
        totalCharacterCot f (M / q) := by
  classical
  let T : ArithmeticFunction ℝ := ⟨totalCharacterCot f, by simp [totalCharacterCot]⟩
  let P : ArithmeticFunction ℝ := ⟨primitiveCharacterCot f, by
    simp [primitiveCharacterCot, primitiveResidues]⟩
  have hT : T = f * P := by
    ext N
    by_cases hN : N = 0
    · subst N; simp
    change totalCharacterCot f N = (f * P) N
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal' (fun a b => f a * P b)]
    exact totalCharacterCot_gcd_blocks f hf N (Nat.pos_of_ne_zero hN)
  have hInv := mobius_weighted_inverse f hf1 hf
  have hP : (ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction ℝ) f) * T = P := by
    rw [hT, ← mul_assoc, hInv, one_mul]
  have h := congrArg (fun a : ArithmeticFunction ℝ => a M) hP
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction ℝ) f) a * T b)] at h
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply] at h
  exact h.symm

/-- Normalization appearing in the finite Euler product. -/
def normalizedArithmetic (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun q => f q / (q : ℝ), by simp⟩

theorem normalizedArithmetic_multiplicative (f : ArithmeticFunction ℝ)
    (hf1 : f 1 = 1) (hf : ∀ a b, f (a * b) = f a * f b) :
    (normalizedArithmetic f).IsMultiplicative := by
  constructor
  · simp [normalizedArithmetic, hf1]
  · intro a b _
    change f (a * b) / ((a * b : ℕ) : ℝ) = (f a / (a : ℝ)) * (f b / (b : ℝ))
    rw [hf, Nat.cast_mul, mul_div_mul_comm]

theorem totalCharacterCot_periodic (f : ArithmeticFunction ℝ) (d L : ℕ)
    (hd : 0 < d) (hL : 0 < L) (hdL : d ∣ L) (hper : Function.Periodic f d) :
    totalCharacterCot f L = (L / d : ℕ) * totalCharacterCot f d := by
  have hg : 0 < L / d := Nat.div_pos (Nat.le_of_dvd hL hdL) hd
  unfold totalCharacterCot
  simpa only [Nat.div_mul_cancel hdL] using
    periodic_cotangent_lift d (L / d) hd hg f hper f.map_zero

/-- The conductor identity for any real completely multiplicative periodic character.
This proves the finite cotangent/Euler-factor calculation independently of class numbers. -/
theorem primitiveCharacterCot_conductor (f : ArithmeticFunction ℝ)
    (hf1 : f 1 = 1) (hf : ∀ a b, f (a * b) = f a * f b)
    (d M : ℕ) (hd : 0 < d) (hM : 0 < M) (hdM : d ∣ M)
    (hper : Function.Periodic f d) (hzero : ∀ q, ¬q.Coprime d → f q = 0) :
    primitiveCharacterCot f M =
      (M / d : ℕ) * totalCharacterCot f d *
        ∏ p ∈ M.primeFactors, (1 - f p / (p : ℝ)) := by
  classical
  rw [primitiveCharacterCot_moebius f hf1 hf]
  have ht : ∀ q ∈ M.divisors,
      (ArithmeticFunction.moebius q : ℝ) * f q * totalCharacterCot f (M / q) =
        ((M / d : ℕ) * totalCharacterCot f d) *
          ((ArithmeticFunction.moebius q : ℝ) * (f q / (q : ℝ))) := by
    intro q hq
    by_cases hfq : f q = 0
    · simp [hfq]
    have hcop : q.Coprime d := by
      by_contra h
      exact hfq (hzero q h)
    have hqdvd := (Nat.mem_divisors.mp hq).1
    have hqp := Nat.pos_of_dvd_of_pos hqdvd hM
    have hLp : 0 < M / q := Nat.div_pos (Nat.le_of_dvd hM hqdvd) hqp
    have hdL : d ∣ M / q := hcop.symm.dvd_of_dvd_mul_left
      (by simpa only [Nat.mul_div_cancel' hqdvd] using hdM)
    rw [totalCharacterCot_periodic f d (M / q) hd hLp hdL hper]
    have he : (M / q / d : ℕ) * d * q = M := by
      rw [Nat.div_mul_cancel hdL, Nat.div_mul_cancel hqdvd]
    have he' : (((M / q / d : ℕ) : ℝ)) * d * q = M := by exact_mod_cast he
    have heM : (((M / d : ℕ) : ℝ)) * d = M := by exact_mod_cast Nat.div_mul_cancel hdM
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne'
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hr : (((M / q / d : ℕ) : ℝ)) = (((M / d : ℕ) : ℝ)) / q := by
      apply (eq_div_iff hqR).mpr
      nlinarith
    rw [hr]
    ring
  rw [sum_congr rfl ht, ← mul_sum]
  congr 1
  exact mobius_euler_product (normalizedArithmetic f)
    (normalizedArithmetic_multiplicative f hf1 hf) M hM.ne'


theorem fundamentalCharacter_zero (d : ℕ) (_hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d 0 = 0 := by
  by_cases hd3 : d % 4 = 3
  · have hd : 1 < d := by omega
    simp [fundamentalCharacter, hd3, jacobiSym.zero_left hd]
  · simp [fundamentalCharacter, hd3]

theorem fundamentalCharacter_one (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d 1 = 1 := by
  have hd : d % 4 = 0 ∨ d % 4 = 3 := hD.2
  rcases hd with hd | hd <;> simp [fundamentalCharacter, hd, jacobiSym.one_left, jacobiSym.one_right]

theorem fundamentalCharacter_mul (d a b : ℕ) (hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d (a * b) = fundamentalCharacter d a * fundamentalCharacter d b := by
  by_cases hd3 : d % 4 = 3
  · simp only [fundamentalCharacter, ite_eq_left hd3, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]
  have hd4 : d % 4 = 0 := hD.2.resolve_right hd3
  by_cases ha : a % 2 = 1
  · by_cases hb : b % 2 = 1
    · have hab : (a * b) % 2 = 1 := by rw [Nat.mul_mod, ha, hb]
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      simp only [fundamentalCharacter, hd4, show (0 : ℕ) ≠ 3 by decide, ite_false, ha, hb, hab, and_self,
        ite_true, jacobiSym.mul_right' _ ha0 hb0, Int.cast_mul]
    · have hb0 : b % 2 = 0 := by omega
      have hab : (a * b) % 2 ≠ 1 := by rw [Nat.mul_mod, hb0]; simp
      simp [fundamentalCharacter, hd3, hb, hab]
  · have ha0 : a % 2 = 0 := by omega
    have hab : (a * b) % 2 ≠ 1 := by rw [Nat.mul_mod, ha0]; simp
    simp [fundamentalCharacter, hd3, ha, hab]

theorem negative_quarter_natAbs (d : ℕ) (hd4 : d % 4 = 0) :
    4 * ((-(d : ℤ)) / 4).natAbs = d := by
  have hd : (4 : ℤ) ∣ -(d : ℤ) := by
    have hdN : 4 ∣ d := Nat.dvd_of_mod_eq_zero hd4
    exact dvd_neg.mpr (by exact_mod_cast hdN)
  rw [Int.natAbs_ediv, ite_eq_left (Or.inr (Or.inr hd))]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]
  norm_num
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd4)

theorem fundamentalCharacter_periodic (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    Function.Periodic (fundamentalCharacter d) d := by
  intro c
  by_cases hd3 : d % 4 = 3
  · simp only [fundamentalCharacter, ite_eq_left hd3]
    congr 1
    apply jacobiSym.mod_left'
    simp
  have hd4 : d % 4 = 0 := hD.2.resolve_right hd3
  have hd2 : d % 2 = 0 := by omega
  have hc2 : (c + d) % 2 = c % 2 := by rw [Nat.add_mod, hd2]; simp
  simp only [fundamentalCharacter, hd4, show (0 : ℕ) ≠ 3 by decide, ite_false, true_and, hc2]
  by_cases hc : c % 2 = 1
  · rw [ite_eq_left hc, ite_eq_left hc]
    congr 1
    have hneg : (-(d : ℤ)) % 4 = 0 := by omega
    rw [← jacobiSym.div_four_left hneg (by omega),
      ← jacobiSym.div_four_left hneg hc]
    rw [jacobiSym.mod_right _ (Nat.odd_iff.mpr (by omega)),
      jacobiSym.mod_right _ (Nat.odd_iff.mpr hc),
      negative_quarter_natAbs d hd4]
    simp
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem fundamentalCharacter_eq_zero_of_not_coprime (d c : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hcop : ¬c.Coprime d) :
    fundamentalCharacter d c = 0 := by
  by_cases hd3 : d % 4 = 3
  · let : NeZero d := ⟨hD.1.ne'⟩
    have h0 : jacobiSym (c : ℤ) d = 0 := by
      apply jacobiSym.eq_zero_iff_not_coprime.mpr
      simpa [Nat.Coprime, Int.gcd_natCast_natCast] using hcop
    simp [fundamentalCharacter, hd3, h0]
  by_cases hc : c % 2 = 1
  · let : NeZero c := ⟨by omega⟩
    have h0 : jacobiSym (-(d : ℤ)) c = 0 := by
      apply jacobiSym.eq_zero_iff_not_coprime.mpr
      simpa [Nat.Coprime, Int.neg_gcd, Int.gcd_natCast_natCast, Nat.gcd_comm] using hcop
    simp [fundamentalCharacter, hd3, hc, h0]
  · simp [fundamentalCharacter, hd3, hc]

def fundamentalArithmetic (d : ℕ) (hD : isNegativeDiscriminantAbs d) : ArithmeticFunction ℝ :=
  ⟨fundamentalCharacter d, fundamentalCharacter_zero d hD⟩

theorem totalCharacterCot_eq_primitive (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    totalCharacterCot (fundamentalArithmetic d hD) d =
      primitiveCharacterCot (fundamentalArithmetic d hD) d := by
  classical
  unfold totalCharacterCot primitiveCharacterCot primitiveResidues
  rw [sum_filter]
  apply sum_congr rfl
  intro c hc
  split_ifs with h
  · rfl
  · have hf : fundamentalCharacter d c = 0 := by
      by_cases hc0 : c = 0
      · subst c; exact fundamentalCharacter_zero d hD
      · exact fundamentalCharacter_eq_zero_of_not_coprime d c hD
          (fun hcop => h ⟨hc0, hcop⟩)
    change (fundamentalCharacter d c) * cotNat d c = 0
    rw [hf, zero_mul]

theorem fundamental_eulerProduct_conductor (d s : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    ∏ p ∈ (d * s ^ 2).primeFactors, (1 - fundamentalCharacter d p / (p : ℝ)) =
      eulerProduct d s := by
  classical
  rw [Nat.primeFactors_mul hD.1.ne' (pow_ne_zero _ hs.ne'),
    Nat.primeFactors_pow s (by decide)]
  unfold eulerProduct
  symm
  apply prod_subset subset_union_right
  intro p hp hpnot
  have hpd : p ∈ d.primeFactors := (mem_union.mp hp).resolve_right hpnot
  have hprime := Nat.prime_of_mem_primeFactors hpd
  have hdiv := Nat.dvd_of_mem_primeFactors hpd
  have hzero := fundamentalCharacter_eq_zero_of_not_coprime d p hD
    (by simpa only [hprime.coprime_iff_not_dvd, not_not] using hdiv)
  simp [hzero]

/-- The weighted cotangent conductor calculation for the explicit quadratic character,
before identifying the character used in the primitive Gauss blocks. -/
theorem fundamental_cotangent_conductor (d s : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    primitiveCharacterCot (fundamentalArithmetic d hD) (d * s ^ 2) =
      (s : ℝ) ^ 2 * primitiveCharacterCot (fundamentalArithmetic d hD) d *
        eulerProduct d s := by
  have hmul : ∀ a b, (fundamentalArithmetic d hD) (a * b) =
      (fundamentalArithmetic d hD) a * (fundamentalArithmetic d hD) b :=
    fun a b => fundamentalCharacter_mul d a b hD
  have h := primitiveCharacterCot_conductor (fundamentalArithmetic d hD)
    (fundamentalCharacter_one d hD) hmul d (d * s ^ 2) hD.1
    (mul_pos hD.1 (pow_pos hs _)) (dvd_mul_right d _)
    (fundamentalCharacter_periodic d hD)
    (fun q hq => fundamentalCharacter_eq_zero_of_not_coprime d q hD hq)
  rw [totalCharacterCot_eq_primitive d hD] at h
  change primitiveCharacterCot (fundamentalArithmetic d hD) (d * s ^ 2) =
    ((d * s ^ 2) / d : ℕ) * primitiveCharacterCot (fundamentalArithmetic d hD) d *
      ∏ p ∈ (d * s ^ 2).primeFactors, (1 - fundamentalCharacter d p / (p : ℝ)) at h
  rw [Nat.mul_div_cancel_left _ hD.1, Nat.cast_pow,
    fundamental_eulerProduct_conductor d s hD hs] at h
  exact h


theorem jacobi_negative_three_mod_four {d c : ℕ} (hd : d % 4 = 3) (hc : c % 2 = 1) :
    jacobiSym (-(d : ℤ)) c = jacobiSym (c : ℤ) d := by
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hc), ZMod.χ₄_nat_eq_if_mod_four]
  have hc0 : c % 2 ≠ 0 := by omega
  rw [ite_eq_right hc0]
  rcases Nat.odd_mod_four_iff.mp hc with hc1 | hc3
  · rw [ite_eq_left hc1,
      jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) hc1,
      one_mul]
  · rw [ite_eq_right (by omega), jacobiSym.quadratic_reciprocity_three_mod_four hd hc3]
    ring

theorem gaussCharacter_square_conductor (d s c : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hs : 0 < s)
    (hc : c ∈ primitiveResidues (d * s ^ 2)) :
    gaussCharacter (d * s ^ 2) c = fundamentalCharacter d c := by
  have hcop := (mem_primitiveResidues.mp hc).2.2
  have hcsp : c.Coprime (s ^ 2) := (Nat.coprime_mul_iff_right.mp hcop).2
  have hcs : c.Coprime s := hcsp.of_dvd_right (dvd_pow_self s (by decide))
  have hM := negativeDiscriminantAbs_square_mul hD hs
  by_cases hM3 : (d * s ^ 2) % 4 = 3
  · have hd3 : d % 4 = 3 := by
      have hm : (d * s ^ 2) % 4 = (d % 4 * (s ^ 2 % 4)) % 4 := Nat.mul_mod _ _ _
      rcases hD.2 with hd0 | hd3
      · rw [hd0] at hm
        norm_num at hm
        omega
      · exact hd3
    have hj : jacobiSym (c : ℤ) (d * s ^ 2) = jacobiSym (c : ℤ) d := by
      rw [jacobiSym.mul_right' _ hD.1.ne' (pow_ne_zero _ hs.ne'),
        jacobiSym.pow_right, jacobiSym.sq_one (by simpa using hcs.gcd_eq_one), mul_one]
    simp [gaussCharacter, hM3, fundamentalCharacter, hd3, hj]
  · have hM4 : (d * s ^ 2) % 4 = 0 := hM.2.resolve_right hM3
    have hc2 : c % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp
      (hcop.of_dvd_right (by omega)))
    have hj : jacobiSym (-((d * s ^ 2 : ℕ) : ℤ)) c = jacobiSym (-(d : ℤ)) c := by
      rw [Nat.cast_mul, Nat.cast_pow, ← neg_mul, jacobiSym.mul_left,
        jacobiSym.sq_one' (by simpa [Nat.gcd_comm] using hcs.gcd_eq_one), mul_one]
    simp only [gaussCharacter, ite_eq_right hM3, ite_eq_left hM4, hj]
    by_cases hd3 : d % 4 = 3
    · rw [jacobi_negative_three_mod_four hd3 hc2]
      simp [fundamentalCharacter, hd3]
    · have hd4 := hD.2.resolve_right hd3
      simp [fundamentalCharacter, hd4, hc2]

theorem characterCot_eq_fundamental_primitive (d s : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    characterCot (d * s ^ 2) =
      primitiveCharacterCot (fundamentalArithmetic d hD) (d * s ^ 2) := by
  unfold characterCot primitiveCharacterCot
  apply sum_congr rfl
  intro c hc
  rw [gaussCharacter_square_conductor d s c hD hs hc]
  rfl

/-- The elementary conductor hypothesis is now discharged. -/
theorem cotangentConductorFormula : CotangentConductorFormula := by
  intro d s hd hs hdf
  have hD : isNegativeDiscriminantAbs d := by
    apply (negativeDiscriminantAbs_iff d).mpr
    exact ⟨by omega, hdf.emod_four_eq_zero_or_one⟩
  rw [characterCot_eq_fundamental_primitive d s hD hs,
    fundamental_cotangent_conductor d s hD hs]
  have hbase := characterCot_eq_fundamental_primitive d 1 hD (by decide)
  simpa only [one_pow, mul_one] using congrArg (fun x : ℝ => (s : ℝ) ^ 2 * x * eulerProduct d s) hbase.symm

/-- Assembly lemma using the signed Gauss and class-number identities. -/
theorem closed_formula_of_remaining_inputs (hG : GaussSignEvaluation)
    (hF : FundamentalClassNumberCotangent) (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) :=
  closed_formula_of_standard_inputs hG hF cotangentConductorFormula hO


theorem PrimitivePositiveForm.completing_square {Δ : ℤ} (f : PrimitivePositiveForm Δ)
    (x y : ℤ) :
    4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) =
      (2 * f.a * x + f.b * y) ^ 2 - Δ * y ^ 2 := by
  linear_combination -(y ^ 2) * f.discriminant

theorem PrimitivePositiveForm.c_pos {Δ : ℤ} (hΔ : Δ < 0) (f : PrimitivePositiveForm Δ) :
    0 < f.c := by
  have ha := f.positive
  have hb : 0 ≤ f.b ^ 2 := sq_nonneg _
  have hdisc := f.discriminant
  nlinarith

theorem PrimitivePositiveForm.eval_pos {Δ : ℤ} (hΔ : Δ < 0)
    (f : PrimitivePositiveForm Δ) (v : Fin 2 → ℤ) (hv : v ≠ 0) : 0 < f.eval v := by
  have ha := f.positive
  have hsq := f.completing_square (v 0) (v 1)
  change 4 * f.a * f.eval v = _ at hsq
  by_cases hy : v 1 = 0
  · have hx : v 0 ≠ 0 := by
      intro hx
      apply hv
      funext i
      fin_cases i <;> simp [hx, hy]
    simp only [PrimitivePositiveForm.eval, hy, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_pos ha (sq_pos_of_ne_zero hx)
  · have hy2 := sq_pos_of_ne_zero hy
    have hnon := sq_nonneg (2 * f.a * v 0 + f.b * v 1)
    have hprod : 0 < 4 * f.a * f.eval v := by nlinarith
    nlinarith

theorem primitive_coefficients_transfer {Δ : ℤ} (f : PrimitivePositiveForm Δ)
    (a b c : ℤ)
    (h : ∀ z : ℤ, z ∣ a → z ∣ b → z ∣ c → z ∣ f.a ∧ z ∣ f.b ∧ z ∣ f.c) :
    Int.gcd a (Int.gcd b c : ℤ) = 1 := by
  let g := Int.gcd a (Int.gcd b c : ℤ)
  have hga : (g : ℤ) ∣ a := Int.gcd_dvd_left _ _
  have hgg : (g : ℤ) ∣ (Int.gcd b c : ℤ) := Int.gcd_dvd_right _ _
  have hgb : (g : ℤ) ∣ b := hgg.trans (Int.gcd_dvd_left _ _)
  have hgc : (g : ℤ) ∣ c := hgg.trans (Int.gcd_dvd_right _ _)
  obtain ⟨hfa, hfb, hfc⟩ := h g hga hgb hgc
  have hg1 : (g : ℤ) ∣ (Int.gcd f.a (Int.gcd f.b f.c : ℤ) : ℤ) :=
    Int.dvd_coe_gcd hfa (Int.dvd_coe_gcd hfb hfc)
  rw [f.primitive] at hg1
  have hgN : g ∣ 1 := by exact_mod_cast hg1
  exact Nat.eq_one_of_dvd_one hgN

def PrimitivePositiveForm.shear {Δ : ℤ} (f : PrimitivePositiveForm Δ) (k : ℤ) :
    PrimitivePositiveForm Δ where
  a := f.a
  b := f.b + 2 * f.a * k
  c := f.a * k ^ 2 + f.b * k + f.c
  positive := f.positive
  discriminant := by
    calc _ = f.b ^ 2 - 4 * f.a * f.c := by ring
         _ = Δ := f.discriminant
  primitive := primitive_coefficients_transfer f _ _ _ (by
    intro z hza hzb hzc
    have hzb' : z ∣ f.b := by
      have h := hzb.sub (hza.mul_right (2 * k))
      convert h using 1; ring
    have hzc' : z ∣ f.c := by
      have h := (hzc.sub (hza.mul_right (k ^ 2))).sub (hzb'.mul_right k)
      convert h using 1; ring
    exact ⟨hza, hzb', hzc'⟩)

def PrimitivePositiveForm.swap {Δ : ℤ} (hΔ : Δ < 0) (f : PrimitivePositiveForm Δ) :
    PrimitivePositiveForm Δ where
  a := f.c
  b := -f.b
  c := f.a
  positive := f.c_pos hΔ
  discriminant := by
    calc _ = f.b ^ 2 - 4 * f.a * f.c := by ring
         _ = Δ := f.discriminant
  primitive := primitive_coefficients_transfer f _ _ _ (by
    intro z hzc hzb hza
    exact ⟨hza, dvd_neg.mp hzb, hzc⟩)

theorem properChange_shear {Δ : ℤ} (f : PrimitivePositiveForm Δ) (k : ℤ) :
    properChange (f.shear k) f := by
  refine ⟨⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro v
  simp [PrimitivePositiveForm.eval, PrimitivePositiveForm.shear, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem properChange_swap {Δ : ℤ} (hΔ : Δ < 0) (f : PrimitivePositiveForm Δ) :
    properChange (f.swap hΔ) f := by
  refine ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro v
  simp [PrimitivePositiveForm.eval, PrimitivePositiveForm.swap, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

def ReducedPositiveForm (Δ : ℤ) := {f : PrimitivePositiveForm Δ // |f.b| ≤ f.a ∧ f.a ≤ f.c}

theorem exists_reduced_properChange {Δ : ℤ} (hΔ : Δ < 0) (f : PrimitivePositiveForm Δ) :
    ∃ g : PrimitivePositiveForm Δ, |g.b| ≤ g.a ∧ g.a ≤ g.c ∧ properChange g f := by
  classical
  let P : ℕ → Prop := fun m => ∃ g : PrimitivePositiveForm Δ, properChange g f ∧ g.a.natAbs = m
  have hex : ∃ m, P m := ⟨f.a.natAbs, f, properChange_refl f, rfl⟩
  obtain ⟨g, hgf, hgm⟩ := Nat.find_spec hex
  have hmin : ∀ g' : PrimitivePositiveForm Δ, properChange g' f → g.a.natAbs ≤ g'.a.natAbs := by
    intro g' hg'
    rw [hgm]
    exact Nat.find_min' hex ⟨g', hg', rfl⟩
  let k : ℤ := -((g.b + g.a) / (2 * g.a))
  let r := g.shear k
  have hrg : properChange r g := properChange_shear g k
  have hrf : properChange r f := properChange_trans hrg hgf
  have ha : 0 < g.a := g.positive
  have hbmod : r.b = (g.b + g.a) % (2 * g.a) - g.a := by
    dsimp [r, PrimitivePositiveForm.shear, k]
    have h := Int.emod_add_ediv_mul (g.b + g.a) (2 * g.a)
    linear_combination -h
  have hb : |r.b| ≤ r.a := by
    rw [hbmod]
    change |(g.b + g.a) % (2 * g.a) - g.a| ≤ g.a
    have hn := Int.emod_nonneg (g.b + g.a) (by omega : 2 * g.a ≠ 0)
    have hl := Int.emod_lt_of_pos (g.b + g.a) (by omega : 0 < 2 * g.a)
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hrc : r.a ≤ r.c := by
    have hswap := properChange_swap hΔ r
    have hsf := properChange_trans hswap hrf
    have hm := hmin (r.swap hΔ) hsf
    have hrpos := r.positive
    have hcpos := r.c_pos hΔ
    change r.a.natAbs ≤ r.c.natAbs at hm
    have hm' : (r.a.natAbs : ℤ) ≤ (r.c.natAbs : ℤ) := by exact_mod_cast hm
    simpa only [Int.natCast_natAbs, abs_of_pos hrpos, abs_of_pos hcpos] using hm'
  exact ⟨r, hb, hrc, hrf⟩

theorem reduced_coefficients_bound {Δ : ℤ} (hΔ : Δ < 0) (g : ReducedPositiveForm Δ) :
    |g.val.a| ≤ Δ.natAbs ^ 2 + Δ.natAbs ∧
    |g.val.b| ≤ Δ.natAbs ^ 2 + Δ.natAbs ∧
    |g.val.c| ≤ Δ.natAbs ^ 2 + Δ.natAbs := by
  have ha := g.val.positive
  have hc := g.val.c_pos hΔ
  have hb := g.property.1
  have hac := g.property.2
  have hd := g.val.discriminant
  have hD : (Δ.natAbs : ℤ) = -Δ := by rw [Int.natCast_natAbs, abs_of_neg hΔ]
  have hb2 : g.val.b ^ 2 ≤ g.val.a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg g.val.b) ha.le).mpr hb
  have ha2 : 3 * g.val.a ^ 2 ≤ (Δ.natAbs : ℤ) := by
    rw [hD]
    nlinarith
  have haD : g.val.a ≤ (Δ.natAbs : ℤ) := by nlinarith [sq_nonneg (g.val.a - 1)]
  have hDN : 0 ≤ (Δ.natAbs : ℤ) := Int.natCast_nonneg _
  have hbD : |g.val.b| ≤ (Δ.natAbs : ℤ) := hb.trans haD
  have hbD2 : g.val.b ^ 2 ≤ (Δ.natAbs : ℤ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg g.val.b) hDN).mpr hbD
  have hcD : g.val.c ≤ (Δ.natAbs : ℤ) ^ 2 + Δ.natAbs := by nlinarith
  have haB : g.val.a ≤ (Δ.natAbs : ℤ) ^ 2 + Δ.natAbs :=
    haD.trans (by nlinarith [sq_nonneg (Δ.natAbs : ℤ)])
  have hbB := hb.trans haB
  simpa only [abs_of_pos ha, abs_of_pos hc] using And.intro haB (And.intro hbB hcD)

theorem finite_reducedPositiveForm (Δ : ℤ) (hΔ : Δ < 0) : Finite (ReducedPositiveForm Δ) := by
  classical
  let B : ℤ := (Δ.natAbs : ℤ) ^ 2 + Δ.natAbs
  let E := {z : ℤ // z ∈ Finset.Icc (-B) B}
  let coeff : ReducedPositiveForm Δ → Fin 3 → ℤ :=
    fun g => ![g.val.a, g.val.b, g.val.c]
  have hb : ∀ g : ReducedPositiveForm Δ, ∀ i : Fin 3, |coeff g i| ≤ B := by
    intro g i
    obtain ⟨ha, hb, hc⟩ := reduced_coefficients_bound hΔ g
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  let e : ReducedPositiveForm Δ → Fin 3 → E :=
    fun g i => ⟨coeff g i, Finset.mem_Icc.mpr (abs_le.mp (hb g i))⟩
  apply Finite.of_injective e
  intro g h he
  have ha : g.val.a = h.val.a := congrArg (fun F : Fin 3 → E => (F 0).val) he
  have hb : g.val.b = h.val.b := congrArg (fun F : Fin 3 → E => (F 1).val) he
  have hc : g.val.c = h.val.c := congrArg (fun F : Fin 3 → E => (F 2).val) he
  apply Subtype.ext
  cases g with
  | mk g hg =>
    cases h with
    | mk h hh =>
      cases g
      cases h
      simp_all

/-- Proper classes of primitive positive forms have finite cardinality at every
negative discriminant. This justifies the class number used in the endpoint. -/
theorem finite_FormClass (Δ : ℤ) (hΔ : Δ < 0) : Finite (FormClass Δ) := by
  classical
  let : Finite (ReducedPositiveForm Δ) := finite_reducedPositiveForm Δ hΔ
  let q : ReducedPositiveForm Δ → FormClass Δ :=
    fun g => Quotient.mk (Relation.EqvGen.setoid properChange) g.val
  apply Finite.of_surjective q
  intro c
  refine Quotient.inductionOn c ?_
  intro f
  obtain ⟨g, hgb, hgc, hgf⟩ := exists_reduced_properChange hΔ f
  refine ⟨⟨g, hgb, hgc⟩, ?_⟩
  exact Quotient.sound (Relation.EqvGen.rel _ _ hgf)

theorem primitivePositiveForm_ext {Δ : ℤ} {f g : PrimitivePositiveForm Δ}
    (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) : f = g := by
  cases f
  cases g
  simp_all

/-- The principal form exists for every negative quadratic discriminant. -/
def principalForm (Δ : ℤ) (_hΔ : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    PrimitivePositiveForm Δ where
  a := 1
  b := Δ % 2
  c := ((Δ % 2) ^ 2 - Δ) / 4
  positive := by decide
  discriminant := by
    have hdiv : 4 ∣ (Δ % 2) ^ 2 - Δ := by
      apply Int.dvd_of_emod_eq_zero
      rcases hmod with h0 | h1
      · have hb0 : Δ % 2 = 0 := by omega
        norm_num [hb0]
        exact Int.dvd_of_emod_eq_zero h0
      · have hb1 : Δ % 2 = 1 := by omega
        simp [hb1, Int.sub_emod, h1]
    have h := Int.mul_ediv_cancel' hdiv
    nlinarith
  primitive := by simp

theorem orderClassNumber_pos (Δ : ℤ) (hΔ : Δ < 0) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    0 < orderClassNumber Δ := by
  let : Finite (FormClass Δ) := finite_FormClass Δ hΔ
  let : Nonempty (FormClass Δ) :=
    ⟨Quotient.mk (Relation.EqvGen.setoid properChange) (principalForm Δ hΔ hmod)⟩
  exact Nat.card_pos

theorem reduced_a_bound {Δ : ℤ} (g : ReducedPositiveForm Δ) :
    3 * g.val.a ^ 2 ≤ -Δ := by
  have ha := g.val.positive
  have hb := g.property.1
  have hac := g.property.2
  have hd := g.val.discriminant
  have hb2 : g.val.b ^ 2 ≤ g.val.a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg g.val.b) ha.le).mpr hb
  nlinarith

theorem reduced_minus_three (g : ReducedPositiveForm (-3)) :
    g.val.a = 1 ∧ (g.val.b = 1 ∨ g.val.b = -1) ∧ g.val.c = 1 := by
  have ha := g.val.positive
  have hb := abs_le.mp g.property.1
  have hac := g.property.2
  have hd := g.val.discriminant
  have hbound := reduced_a_bound g
  have ha1 : g.val.a = 1 := by nlinarith [sq_nonneg (g.val.a - 1)]
  have hb3 : g.val.b = -1 ∨ g.val.b = 0 ∨ g.val.b = 1 := by omega
  rcases hb3 with hbn | hb0 | hbp
  · rw [ha1, hbn] at hd
    refine ⟨ha1, Or.inr hbn, ?_⟩
    nlinarith
  · rw [ha1, hb0] at hd
    omega
  · rw [ha1, hbp] at hd
    refine ⟨ha1, Or.inl hbp, ?_⟩
    nlinarith

theorem reduced_minus_four (g : ReducedPositiveForm (-4)) :
    g.val.a = 1 ∧ g.val.b = 0 ∧ g.val.c = 1 := by
  have ha := g.val.positive
  have hb := abs_le.mp g.property.1
  have hac := g.property.2
  have hd := g.val.discriminant
  have hbound := reduced_a_bound g
  have ha1 : g.val.a = 1 := by nlinarith [sq_nonneg (g.val.a - 1)]
  have hb3 : g.val.b = -1 ∨ g.val.b = 0 ∨ g.val.b = 1 := by omega
  rcases hb3 with hbn | hb0 | hbp
  · rw [ha1, hbn] at hd
    omega
  · rw [ha1, hb0] at hd
    refine ⟨ha1, hb0, ?_⟩
    nlinarith
  · rw [ha1, hbp] at hd
    omega

theorem class_eq_principal_of_reduced_equivalence (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1)
    (hred : ∀ g : ReducedPositiveForm Δ, properChange g.val (principalForm Δ hΔ hmod))
    (c : FormClass Δ) :
    c = Quotient.mk (Relation.EqvGen.setoid properChange) (principalForm Δ hΔ hmod) := by
  refine Quotient.inductionOn c ?_
  intro f
  obtain ⟨g, hgb, hgc, hgf⟩ := exists_reduced_properChange hΔ f
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact properChange_trans (properChange_symm hgf) (hred ⟨g, hgb, hgc⟩)

theorem formClass_minus_three_eq_principal (c : FormClass (-3)) :
    c = Quotient.mk (Relation.EqvGen.setoid properChange)
      (principalForm (-3) (by decide) (by decide)) := by
  apply class_eq_principal_of_reduced_equivalence
  intro g
  obtain ⟨ha, hb, hc⟩ := reduced_minus_three g
  let p := principalForm (-3) (by decide) (by decide)
  rcases hb with hb | hb
  · have hg : g.val = p := primitivePositiveForm_ext ha hb hc
    rw [hg]
    exact properChange_refl _
  · have hg : g.val = p.swap (by decide) := primitivePositiveForm_ext ha hb hc
    rw [hg]
    exact properChange_swap (by decide) _

theorem formClass_minus_four_eq_principal (c : FormClass (-4)) :
    c = Quotient.mk (Relation.EqvGen.setoid properChange)
      (principalForm (-4) (by decide) (by decide)) := by
  apply class_eq_principal_of_reduced_equivalence
  intro g
  obtain ⟨ha, hb, hc⟩ := reduced_minus_four g
  have hg : g.val = principalForm (-4) (by decide) (by decide) :=
    primitivePositiveForm_ext ha hb hc
  rw [hg]
  exact properChange_refl _

theorem orderClassNumber_minus_three : orderClassNumber (-3) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun a b => ?_⟩, ?_⟩
  · rw [formClass_minus_three_eq_principal a, formClass_minus_three_eq_principal b]
  · exact ⟨Quotient.mk (Relation.EqvGen.setoid properChange)
      (principalForm (-3) (by decide) (by decide))⟩

theorem orderClassNumber_minus_four : orderClassNumber (-4) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun a b => ?_⟩, ?_⟩
  · rw [formClass_minus_four_eq_principal a, formClass_minus_four_eq_principal b]
  · exact ⟨Quotient.mk (Relation.EqvGen.setoid properChange)
      (principalForm (-4) (by decide) (by decide))⟩


theorem paired_reciprocal_hasSum (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + 1 - z))
      (Real.pi * Real.cot (Real.pi * z)) := by
  have hzc : (z : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨m, hm⟩
    have hmR : (m : ℝ) = z := by
      simpa using congrArg Complex.re hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hm1 : (m : ℝ) < 1 := by linarith
    have hm0' : (0 : ℤ) < m := by exact_mod_cast hm0
    have hm1' : m < (1 : ℤ) := by exact_mod_cast hm1
    omega
  have hC : HasSum (fun k : ℕ => cotTerm (z : ℂ) k)
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / (z : ℂ)) := by
    rw [cot_series_rep' hzc]
    exact (summable_cotTerm hzc).hasSum
  have hterm (k : ℕ) : cotTerm (z : ℂ) k =
      ((1 / (z - ((k : ℝ) + 1)) + 1 / (z + ((k : ℝ) + 1)) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hval : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / (z : ℂ) =
      ((Real.pi * Real.cot (Real.pi * z) - 1 / z : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hval] at hC
  simp_rw [hterm] at hC
  have hreal := Complex.hasSum_re hC
  simp only [Complex.ofReal_re] at hreal
  have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + z)) Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop z
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have htel : HasSum (fun k : ℕ =>
      1 / ((k : ℝ) + z) - 1 / (((k + 1 : ℕ) : ℝ) + z)) (1 / z) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => ?_) (1 / z)).mpr
    · simp_rw [sum_range_sub']
      simpa using tendsto_const_nhds.sub hlim
    · apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast; linarith
  have hsum := hreal.add htel
  convert hsum using 1
  · ext k
    have h1 : z + ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (k : ℝ) + z ≠ 0 := by positivity
    have h3 : z - ((k : ℝ) + 1) ≠ 0 := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h4 : (k : ℝ) + 1 - z ≠ 0 := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    push_cast
    field_simp
    ring
  · ring

theorem paired_modulus_hasSum (d a : ℕ) (ha : 0 < a) (had : a < d) :
    HasSum (fun k : ℕ =>
      1 / ((a : ℝ) + d * k) - 1 / ((d - a : ℕ) + (d : ℝ) * k))
      (Real.pi / d * cotNat d a) := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have haz : (a : ℝ) / d < 1 := (div_lt_one hdR).mpr (Nat.cast_lt.mpr had)
  have h := (paired_reciprocal_hasSum ((a : ℝ) / d) (div_pos haR hdR) haz).div_const (d : ℝ)
  convert h using 1
  · ext k
    rw [Nat.cast_sub had.le]
    have h1 : ((a : ℝ) + d * k) / d = (k : ℝ) + (a : ℝ) / d := by
      field_simp
      ring
    have h2 : ((d : ℝ) - a + d * k) / d = (k : ℝ) + 1 - (a : ℝ) / d := by
      field_simp
      ring
    rw [← h1, ← h2, sub_div, div_div, div_div]
    simp only [div_mul_cancel₀ _ hdR.ne']
  · unfold cotNat
    rw [mul_div_assoc]
    ring

/-- The value at one of a periodic Dirichlet series, with consecutive blocks.
This definition uses the reciprocal series, independently of the cotangent formula. -/
def characterLValue (d : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, ∑ a ∈ range d, f a / ((a : ℝ) + (d : ℝ) * k)

theorem sum_odd_reciprocal_block (d k : ℕ) (hd : 0 < d)
    (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hodd : ∀ a, 0 < a → a < d → f (d - a) = -f a) :
    ∑ a ∈ range d, f a / ((a : ℝ) + (d : ℝ) * k) =
      (∑ a ∈ (range d).erase 0,
        f a * (1 / ((a : ℝ) + d * k) - 1 / ((d - a : ℕ) + (d : ℝ) * k))) / 2 := by
  classical
  have hp : ∑ a ∈ (range d).erase 0, f a / ((d - a : ℕ) + (d : ℝ) * k) =
      ∑ a ∈ (range d).erase 0, -f a / ((a : ℝ) + (d : ℝ) * k) := by
    refine sum_bij (fun a _ => d - a) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha0, hal⟩ := mem_erase.mp ha
      have hal' := mem_range.mp hal
      exact mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
    · intro a ha b hb hab
      have ha' := mem_range.mp (mem_erase.mp ha).2
      have hb' := mem_range.mp (mem_erase.mp hb).2
      omega
    · intro a ha
      have ha' := mem_range.mp (mem_erase.mp ha).2
      have ha0 := (mem_erase.mp ha).1
      exact ⟨d - a, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩, by omega⟩
    · intro a ha
      have ha' := mem_range.mp (mem_erase.mp ha).2
      have ha0 := Nat.pos_of_ne_zero (mem_erase.mp ha).1
      rw [hodd a ha0 ha', neg_neg]
  rw [← sum_erase_add _ _ (mem_range.mpr hd)]
  simp only [hf0, zero_div, add_zero, mul_sub, mul_one_div, sum_sub_distrib, hp,
    neg_div, sum_neg_distrib]
  ring

theorem characterLValue_eq_cotangent (d : ℕ) (hd : 0 < d)
    (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hodd : ∀ a, 0 < a → a < d → f (d - a) = -f a) :
    characterLValue d f =
      Real.pi / (2 * d) * ∑ a ∈ range d, f a * cotNat d a := by
  classical
  have hs : HasSum (fun k : ℕ => ∑ a ∈ (range d).erase 0,
      f a * (1 / ((a : ℝ) + d * k) - 1 / ((d - a : ℕ) + (d : ℝ) * k)))
      (∑ a ∈ (range d).erase 0, f a * (Real.pi / d * cotNat d a)) := by
    apply hasSum_sum
    intro a ha
    exact (paired_modulus_hasSum d a
      (Nat.pos_of_ne_zero (mem_erase.mp ha).1) (mem_range.mp (mem_erase.mp ha).2)).mul_left _
  have hb := (hs.div_const 2).congr_fun
    (fun k => sum_odd_reciprocal_block d k hd f hf0 hodd)
  unfold characterLValue
  rw [hb.tsum_eq, ← sum_erase_add _ _ (mem_range.mpr hd)]
  simp only [hf0, zero_mul, add_zero]
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro a ha
  ring


theorem fundamentalCharacter_minus_one (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d (d - 1) = -1 := by
  have hd : 1 < d := by
    rcases hD.2 with h0 | h3 <;> have hp := hD.1 <;> omega
  by_cases hd3 : d % 4 = 3
  · have hj : jacobiSym ((d - 1 : ℕ) : ℤ) d = jacobiSym (-1) d := by
      apply jacobiSym.mod_left'
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      simp
    rw [fundamentalCharacter, ite_eq_left hd3, hj,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
      ZMod.χ₄_nat_eq_if_mod_four]
    norm_num [show d % 2 ≠ 0 by omega, show d % 4 ≠ 1 by omega]
  · have hd4 := hD.2.resolve_right hd3
    have hc2 : (d - 1) % 2 = 1 := by omega
    have hc3 : (d - 1) % 4 = 3 := by omega
    have hj : jacobiSym (d : ℤ) (d - 1) = 1 := by
      have hmod : (d : ℤ) % (d - 1 : ℕ) = (1 : ℤ) % (d - 1 : ℕ) := by
        have hcast : (d : ℤ) = ((d - 1 : ℕ) : ℤ) + 1 := by omega
        rw [hcast, Int.add_emod]
        simp
      rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
    simp only [fundamentalCharacter, hd4, show (0 : ℕ) ≠ 3 by decide, ite_false,
      hc2, and_self, ite_true, jacobiSym.neg _ (Nat.odd_iff.mpr hc2),
      ZMod.χ₄_nat_eq_if_mod_four, hj]
    norm_num [show (d - 1) % 2 ≠ 0 by omega, show (d - 1) % 4 ≠ 1 by omega]

/-- The explicit quadratic character realized as Mathlib's genuine Dirichlet character. -/
def negativeDiscriminantCharacter (d : ℕ) [NeZero d] (hD : isNegativeDiscriminantAbs d) :
    DirichletCharacter ℝ d where
  toFun t := fundamentalCharacter d t.val
  map_one' := by
    have hd : 1 < d := by rcases hD.2 with h0 | h3 <;> have hp := hD.1 <;> omega
    let : Fact (1 < d) := ⟨hd⟩
    rw [ZMod.val_one]
    exact fundamentalCharacter_one d hD
  map_mul' := by
    intro a b
    rw [ZMod.val_mul, (fundamentalCharacter_periodic d hD).map_mod_nat,
      fundamentalCharacter_mul d a.val b.val hD]
  map_nonunit' := by
    intro a ha
    apply fundamentalCharacter_eq_zero_of_not_coprime d a.val hD
    intro hc
    apply ha
    simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val d).mpr hc

theorem negativeDiscriminantCharacter_natCast (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (a : ℕ) :
    negativeDiscriminantCharacter d hD (a : ZMod d) = fundamentalCharacter d a := by
  change fundamentalCharacter d (a : ZMod d).val = fundamentalCharacter d a
  rw [ZMod.val_natCast, (fundamentalCharacter_periodic d hD).map_mod_nat]

theorem negativeDiscriminantCharacter_odd (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) :
    (negativeDiscriminantCharacter d hD).Odd := by
  have hcast : ((d - 1 : ℕ) : ZMod d) = -1 := by
    rw [Nat.cast_sub (by
      have hp := hD.1
      omega : 1 ≤ d), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have h := negativeDiscriminantCharacter_natCast d hD (d - 1)
  rw [hcast, fundamentalCharacter_minus_one d hD] at h
  exact h

theorem fundamentalCharacter_odd_representatives (d : ℕ)
    (hD : isNegativeDiscriminantAbs d) (a : ℕ) (_ha : 0 < a) (had : a < d) :
    fundamentalCharacter d (d - a) = -fundamentalCharacter d a := by
  let : NeZero d := ⟨hD.1.ne'⟩
  have hcast : ((d - a : ℕ) : ZMod d) = -(a : ZMod d) := by
    rw [Nat.cast_sub had.le, ZMod.natCast_self, zero_sub]
  rw [← negativeDiscriminantCharacter_natCast d hD (d - a),
    hcast, (negativeDiscriminantCharacter_odd d hD).to_fun,
    negativeDiscriminantCharacter_natCast d hD a]

/-- §5.5: the finite cotangent expression for the quadratic character's value at one. -/
theorem fundamental_characterLValue_eq_cotangent (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    characterLValue d (fundamentalCharacter d) = Real.pi / (2 * d) * characterCot d := by
  rw [characterLValue_eq_cotangent d hD.1 _ (fundamentalCharacter_zero d hD)
    (fun a ha had => fundamentalCharacter_odd_representatives d hD a ha had)]
  have hbase := characterCot_eq_fundamental_primitive d 1 hD (by decide)
  have ht := totalCharacterCot_eq_primitive d hD
  change (∑ a ∈ range d, fundamentalCharacter d a * cotNat d a) =
    primitiveCharacterCot (fundamentalArithmetic d hD) d at ht
  have hc : (∑ a ∈ range d, fundamentalCharacter d a * cotNat d a) = characterCot d :=
    ht.trans (by simpa only [one_pow, mul_one] using hbase.symm)
  rw [hc]

/-- Dirichlet's imaginary quadratic class-number formula in its usual L(1) form.
The proposition is proved below as fundamentalDirichletClassNumberFormula. -/
def FundamentalDirichletClassNumberFormula : Prop := ∀ d : ℕ, 0 < d →
  Int.IsFundamentalDiscr (-(d : ℤ)) →
    characterLValue d (fundamentalCharacter d) =
      2 * Real.pi / Real.sqrt d * classRatio (-(d : ℤ))

theorem fundamentalClassNumberCotangent_of_dirichlet (hF : FundamentalDirichletClassNumberFormula) :
    FundamentalClassNumberCotangent := by
  intro d hd hdf
  have hD : isNegativeDiscriminantAbs d :=
    (negativeDiscriminantAbs_iff d).mpr ⟨by omega, hdf.emod_four_eq_zero_or_one⟩
  have h := hF d hd hdf
  rw [fundamental_characterLValue_eq_cotangent d hD] at h
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hd)).ne'
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg d)
  have hp := Real.pi_pos
  field_simp at h
  apply (mul_left_cancel₀ hs)
  calc
    Real.sqrt d * characterCot d = characterCot d * Real.sqrt d := mul_comm _ _
    _ = 4 * (d : ℝ) * classRatio (-(d : ℤ)) := by norm_num at h; exact h
    _ = 4 * (Real.sqrt d) ^ 2 * classRatio (-(d : ℤ)) := by rw [hs2]
    _ = Real.sqrt d * (4 * Real.sqrt d * classRatio (-(d : ℤ))) := by ring

theorem closed_formula_of_dirichlet_inputs (hG : GaussSignEvaluation)
    (hF : FundamentalDirichletClassNumberFormula) (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) :=
  closed_formula_of_remaining_inputs hG (fundamentalClassNumberCotangent_of_dirichlet hF) hO


theorem conjugate_stdAddChar (a : ZMod n) :
    (starRingEnd ℂ) (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [AddChar.starComp_apply (by simpa only [ZMod.ringChar_zmod_n] using NeZero.pos n)]
  rfl

/-- The squared norm of a quadratic Gauss sum reduces to the kernel of multiplication by 2t. -/
theorem quadraticGauss_mul_conj (t : ZMod n) :
    quadraticGauss t * (starRingEnd ℂ) (quadraticGauss t) =
      (n : ℂ) * ∑ a ∈ (univ : Finset (ZMod n)).filter (fun a => 2 * t * a = 0),
        ZMod.stdAddChar (t * a ^ 2) := by
  classical
  calc
    _ = ∑ y : ZMod n, ∑ x : ZMod n,
        ZMod.stdAddChar (t * x ^ 2) * ZMod.stdAddChar (-(t * y ^ 2)) := by
      unfold quadraticGauss
      rw [map_sum, mul_sum]
      apply sum_congr rfl
      intro y hy
      rw [conjugate_stdAddChar, sum_mul]
    _ = ∑ y : ZMod n, ∑ a : ZMod n,
        ZMod.stdAddChar (t * (y + a) ^ 2) * ZMod.stdAddChar (-(t * y ^ 2)) := by
      apply sum_congr rfl
      intro y hy
      exact (Equiv.sum_comp (Equiv.addLeft y) (fun x : ZMod n =>
        ZMod.stdAddChar (t * x ^ 2) * ZMod.stdAddChar (-(t * y ^ 2)))).symm
    _ = ∑ a : ZMod n, ∑ y : ZMod n,
        ZMod.stdAddChar (t * a ^ 2) * ZMod.stdAddChar ((2 * t * a) * y) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro y hy
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = (n : ℂ) * ∑ a ∈ (univ : Finset (ZMod n)).filter (fun a => 2 * t * a = 0),
        ZMod.stdAddChar (t * a ^ 2) := by
      simp_rw [← mul_sum, character_orthogonality]
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro a ha
      split_ifs <;> simp [mul_comm]

theorem quadraticGauss_normSq_of_two_mul_unit (t : ZMod n) (ht : IsUnit (2 * t)) :
    Complex.normSq (quadraticGauss t) = n := by
  classical
  have hkernel : (univ : Finset (ZMod n)).filter (fun a => 2 * t * a = 0) = {0} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => ht.mul_left_cancel (by simpa using h), fun h => by simp [h]⟩
  have h := quadraticGauss_mul_conj t
  rw [hkernel, sum_singleton] at h
  simpa [Complex.mul_conj] using congrArg Complex.re h

theorem gaussNat_normSq_odd_primitive (M c : ℕ) (hM : Odd M)
    (hc : c.Coprime M) :
    Complex.normSq (gaussNat M c) = M := by
  have hMp : 0 < M := hM.pos
  let : NeZero M := ⟨hMp.ne'⟩
  rw [gaussNat_eq]
  apply quadraticGauss_normSq_of_two_mul_unit
  exact ((ZMod.isUnit_iff_coprime 2 M).mpr (Nat.coprime_two_left.mpr hM)).mul
    ((ZMod.isUnit_iff_coprime c M).mpr hc)

theorem quadraticGauss_shift (t h : ZMod n) (hh : 2 * t * h = 0) :
    quadraticGauss t = ZMod.stdAddChar (t * h ^ 2) * quadraticGauss t := by
  classical
  calc
    quadraticGauss t = ∑ x : ZMod n, ZMod.stdAddChar (t * (h + x) ^ 2) :=
      (Equiv.sum_comp (Equiv.addLeft h) (fun x => ZMod.stdAddChar (t * x ^ 2))).symm
    _ = ∑ x : ZMod n, ZMod.stdAddChar (t * h ^ 2) * ZMod.stdAddChar (t * x ^ 2) := by
      apply sum_congr rfl
      intro x hx
      rw [← AddChar.map_add_eq_mul]
      congr 1
      calc
        t * (h + x) ^ 2 = t * h ^ 2 + t * x ^ 2 + (2 * t * h) * x := by ring
        _ = _ := by rw [hh, zero_mul, add_zero]
    _ = _ := by rw [← mul_sum]; rfl

theorem gaussNat_two_odd_zero (q c : ℕ) (hq : Odd q) (hc : Odd c) :
    gaussNat (2 * q) c = 0 := by
  have hqp : 0 < q := hq.pos
  let : NeZero (2 * q) := ⟨by omega⟩
  let t : ZMod (2 * q) := c
  let h : ZMod (2 * q) := q
  have hh : 2 * t * h = 0 := by
    change (2 : ZMod (2 * q)) * (c : ZMod (2 * q)) * (q : ZMod (2 * q)) = 0
    calc
      _ = (c : ZMod (2 * q)) * ((2 * q : ℕ) : ZMod (2 * q)) := by push_cast; ring
      _ = 0 := by rw [ZMod.natCast_self, mul_zero]
  have hz2 : ZMod.stdAddChar h ^ 2 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have hzero : (2 : ℕ) • h = 0 := by
      change (2 : ℕ) • (q : ZMod (2 * q)) = 0
      rw [nsmul_eq_mul]
      exact_mod_cast ZMod.natCast_self (2 * q)
    rw [hzero, map_zero_eq_one]
  have hh0 : h ≠ 0 := by
    intro h0
    have hv := congrArg ZMod.val h0
    change (q : ZMod (2 * q)).val = (0 : ZMod (2 * q)).val at hv
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  have hz1 : ZMod.stdAddChar h ≠ 1 := char_ne_one hh0
  have hz : ZMod.stdAddChar h = -1 := by
    have hm : (ZMod.stdAddChar h - 1) * (ZMod.stdAddChar h + 1) = 0 := by
      linear_combination hz2
    have hz' := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hz1)
    exact eq_neg_of_add_eq_zero_left hz'
  have hphase : ZMod.stdAddChar (t * h ^ 2) = -1 := by
    have he : t * h ^ 2 = (c * q : ℕ) • h := by
      dsimp [t, h]
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [he, AddChar.map_nsmul_eq_pow, hz]
    exact (hc.mul hq).neg_one_pow
  have hG := quadraticGauss_shift t h hh
  rw [hphase] at hG
  have hzero : quadraticGauss t = 0 := by linear_combination hG / 2
  rw [gaussNat_eq]
  exact hzero

theorem gaussNat_two_mod_four_zero (M c : ℕ) (hM : M % 4 = 2) (hc : c.Coprime M) :
    gaussNat M c = 0 := by
  have h2 : 2 * (M / 2) = M :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by omega : M % 2 = 0))
  have hq : Odd (M / 2) := by
    rw [Nat.odd_iff]
    omega
  have hc2 : Odd c := Nat.coprime_two_right.mp
    (hc.of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega : M % 2 = 0)))
  rw [← h2]
  exact gaussNat_two_odd_zero _ _ hq hc2

/-- Mathlib's square-root count identifies a quadratic exponential sum with a Gauss sum. -/
theorem sum_char_squares_eq_gaussSum (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ∑ x : F, ψ (x ^ 2) =
      gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ := by
  classical
  rw [← sum_fiberwise univ (fun x : F => x ^ 2) (fun x => ψ (x ^ 2))]
  have hterm : ∀ a : F,
      ∑ x ∈ (univ : Finset F).filter (fun x => x ^ 2 = a), ψ (x ^ 2) =
        (((quadraticChar F) a : ℂ) + 1) * ψ a := by
    intro a
    have hs : (univ : Finset F).filter (fun x => x ^ 2 = a) =
        {x : F | x ^ 2 = a}.toFinset := by ext; simp
    have hcard : (((univ : Finset F).filter (fun x => x ^ 2 = a)).card : ℂ) =
        ((quadraticChar F) a : ℂ) + 1 := by
      rw [hs]
      exact_mod_cast quadraticChar_card_sqrts hF a
    calc
      _ = ∑ x ∈ (univ : Finset F).filter (fun x => x ^ 2 = a), ψ a := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2]
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
  simp_rw [hterm, add_mul, one_mul]
  rw [sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

theorem quadraticGauss_prime_eq_gaussSum (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    quadraticGauss (1 : ZMod p) =
      gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) ZMod.stdAddChar := by
  have hp : Nat.Prime p := Fact.out
  have hψ : (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) ≠ 1 := by
    intro h
    have h1 := congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) h
    have hnon : (1 : ZMod p) ≠ 0 := one_ne_zero
    exact char_ne_one hnon (by simpa using h1)
  simpa only [quadraticGauss, one_mul] using
    sum_char_squares_eq_gaussSum (ZMod p)
      (by simpa only [ZMod.ringChar_zmod_n] using hp2) ZMod.stdAddChar hψ

/-- Reuse Mathlib's quadratic Gauss-square theorem. This determines the phase only up to sign. -/
theorem gaussNat_prime_sq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    gaussNat p 1 ^ 2 = (ZMod.χ₄ (p : ZMod 4) : ℂ) * p := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have hχ : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (by exact Int.cast_injective : Function.Injective (Int.castRingHom ℂ))).mpr (quadraticChar_ne_one hF)
  rw [gaussNat_eq, Nat.cast_one, quadraticGauss_prime_eq_gaussSum p hp2,
    gaussSum_sq hχ ((quadraticChar_isQuadratic (ZMod p)).comp _) (ZMod.isPrimitive_stdAddChar p)]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, ZMod.card,
    quadraticChar_neg_one hF]

theorem gaussNat_prime_coefficient (p c : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hc : c.Coprime p) :
    gaussNat p c = (jacobiSym (c : ℤ) p : ℂ) * gaussNat p 1 := by
  classical
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hu : IsUnit (c : ZMod p) := (ZMod.isUnit_iff_coprime c p).mpr hc
  let ψ := AddChar.mulShift (ZMod.stdAddChar (N := p)) hu.unit
  have hψ : ψ ≠ 1 := by
    intro h
    have h1 := congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) h
    have hc0 : (c : ZMod p) ≠ 0 := hu.ne_zero
    apply char_ne_one hc0
    simpa [ψ, AddChar.mulShift_apply, hu.unit_spec] using h1
  have hG : quadraticGauss (c : ZMod p) = gaussSum χ ψ := by
    have h := sum_char_squares_eq_gaussSum (ZMod p)
      (by simpa only [ZMod.ringChar_zmod_n] using hp2) ψ hψ
    simpa only [ψ, AddChar.mulShift_apply, hu.unit_spec, quadraticGauss] using h
  rw [gaussNat_eq, hG, gaussSum_mulShift_eq, ((quadraticChar_isQuadratic (ZMod p)).comp _).inv]
  have hχ : χ (hu.unit : ZMod p) = (jacobiSym (c : ℤ) p : ℂ) := by
    rw [hu.unit_spec, ← jacobiSym.legendreSym.to_jacobiSym]
    simp only [χ, MulChar.ringHomComp_apply, Int.coe_castRingHom, legendreSym, Int.cast_natCast]
  rw [hχ, gaussNat_eq, Nat.cast_one, quadraticGauss_prime_eq_gaussSum p hp2]

theorem gaussNat_prime_one_mod_four_im_zero (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 1) :
    (gaussNat p 1).im = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hs := gaussNat_prime_sq p (by omega : p ≠ 2)
  have hχ : ZMod.χ₄ (p : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp [show p % 2 ≠ 0 by omega, hp4]
  rw [hχ] at hs
  norm_num at hs
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im] at hr hi
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hrepr : (gaussNat p 1).re ≠ 0 := by
    intro h0
    rw [h0] at hr
    nlinarith [sq_nonneg (gaussNat p 1).im]
  have hm : (gaussNat p 1).re * (gaussNat p 1).im = 0 := by linarith
  exact (mul_eq_zero.mp hm).resolve_left hrepr

theorem gaussNat_prime_three_mod_four_re_zero (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    (gaussNat p 1).re = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hs := gaussNat_prime_sq p (by omega : p ≠ 2)
  have hχ : ZMod.χ₄ (p : ZMod 4) = -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp [show p % 2 ≠ 0 by omega, show p % 4 ≠ 1 by omega]
  rw [hχ] at hs
  norm_num at hs
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hr hi
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have himpr : (gaussNat p 1).im ≠ 0 := by
    intro h0
    rw [h0] at hr
    nlinarith [sq_nonneg (gaussNat p 1).re]
  have hm : (gaussNat p 1).re * (gaussNat p 1).im = 0 := by linarith
  exact (mul_eq_zero.mp hm).resolve_right himpr

theorem gaussNat_prime_three_mod_four_im_sq (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    (gaussNat p 1).im ^ 2 = p := by
  have hp : Nat.Prime p := Fact.out
  have hnorm := gaussNat_normSq_odd_primitive p 1
    (Nat.odd_iff.mpr (by omega)) (by simp)
  rw [Complex.normSq_apply, gaussNat_prime_three_mod_four_re_zero p hp4] at hnorm
  nlinarith

/-- Selecting the positive imaginary branch is the genuinely missing prime sign step. -/
theorem gaussNat_prime_three_mod_four_positive_branch (p c : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 3) (hc : c.Coprime p) (hpositive : 0 ≤ (gaussNat p 1).im) :
    (gaussNat p c).im = Real.sqrt p * (jacobiSym (c : ℤ) p : ℝ) := by
  have him : (gaussNat p 1).im = Real.sqrt p := by
    calc
      _ = |(gaussNat p 1).im| := (abs_of_nonneg hpositive).symm
      _ = Real.sqrt ((gaussNat p 1).im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ = _ := by rw [gaussNat_prime_three_mod_four_im_sq p hp4]
  rw [gaussNat_prime_coefficient p c (by omega) hc, Complex.mul_im, him]
  simp
  ring


/-- The additive phase with natural-number parameters. -/
def natPhase (M k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / M)

theorem natPhase_add (M k l : ℕ) :
    natPhase M (k + l) = natPhase M k * natPhase M l := by
  unfold natPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem natPhase_eq_char (M : ℕ) [NeZero M] (k : ℕ) :
    natPhase M k = ZMod.stdAddChar (k : ZMod M) := by
  simpa only [natPhase, Int.cast_natCast] using
    (ZMod.stdAddChar_coe (N := M) (k : ℤ)).symm

theorem natPhase_period (M k r : ℕ) (hM : M ≠ 0) :
    natPhase M (k + M * r) = natPhase M k := by
  let : NeZero M := ⟨hM⟩
  simp [natPhase_eq_char, Nat.cast_add, Nat.cast_mul]

theorem natPhase_lift (g M k : ℕ) (hg : g ≠ 0) :
    natPhase (g * M) (g * k) = natPhase M k := by
  unfold natPhase
  congr 1
  push_cast
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  field_simp

theorem sum_range_multiples {A : Type*} [AddCommMonoid A]
    (p M : ℕ) (hp : 0 < p) (f : ℕ → A) :
    ∑ a ∈ (range (p * M)).filter (fun a => p ∣ a), f a =
      ∑ k ∈ range M, f (p * k) := by
  classical
  symm
  refine sum_bij (fun k _ => p * k) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hk) hp),
      dvd_mul_right p k⟩
  · intro k hk l hl hkl
    exact Nat.eq_of_mul_eq_mul_left hp hkl
  · intro a ha
    obtain ⟨k, rfl⟩ := (mem_filter.mp ha).2
    refine ⟨k, mem_range.mpr ?_, rfl⟩
    exact (Nat.mul_lt_mul_left hp).mp (mem_range.mp (mem_filter.mp ha).1)

/-- Remove a square factor coprime to twice the coefficient, by finite character orthogonality. -/
theorem gaussNat_square_factor (p M c : ℕ) (hp : 0 < p) (hM : 0 < M)
    (hc : p.Coprime (2 * c)) :
    gaussNat (p ^ 2 * M) c = (p : ℂ) * gaussNat M c := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  have hNp : 0 < p ^ 2 * M := mul_pos (pow_pos hp _) hM
  change (∑ k ∈ range (p ^ 2 * M), natPhase (p ^ 2 * M) (c * k ^ 2)) =
    (p : ℂ) * ∑ k ∈ range M, natPhase M (c * k ^ 2)
  rw [show p ^ 2 * M = p * (p * M) by ring, sum_range_blocks (p * M) p (mul_pos hp hM)]
  have hterm (a b : ℕ) :
      natPhase (p * (p * M)) (c * (a + (p * M) * b) ^ 2) =
        natPhase (p * (p * M)) (c * a ^ 2) *
          ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod p) * (b : ZMod p)) := by
    have harg : c * (a + (p * M) * b) ^ 2 =
        (c * a ^ 2 + (p * M) * (2 * c * a * b)) +
          (p * (p * M)) * (c * M * b ^ 2) := by ring
    rw [harg, natPhase_period _ _ _ (by positivity), natPhase_add,
      show p * (p * M) = (p * M) * p by ring,
      natPhase_lift _ _ _ (by positivity), natPhase_eq_char p]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← mul_sum]
  rw [show p * (p * M) = p ^ 2 * M by ring]
  have hsum (a : ℕ) :
      ∑ b ∈ range p, ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod p) * (b : ZMod p)) =
        if p ∣ a then (p : ℂ) else 0 := by
    rw [← sum_zmod_eq_range (n := p) (fun b : ZMod p =>
      ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod p) * b)), character_orthogonality]
    have hcond : ((2 * c * a : ℕ) : ZMod p) = 0 ↔ p ∣ a := by
      rw [ZMod.natCast_eq_zero_iff, hc.dvd_mul_left]
    simp only [hcond]
  simp_rw [hsum]
  have ht : ∀ a ∈ range (p * M),
      natPhase (p ^ 2 * M) (c * a ^ 2) * (if p ∣ a then (p : ℂ) else 0) =
        if p ∣ a then (p : ℂ) * natPhase (p ^ 2 * M) (c * a ^ 2) else 0 := by
    intro a ha
    split_ifs <;> simp [mul_comm]
  rw [sum_congr rfl ht, ← sum_filter, ← mul_sum, sum_range_multiples p M hp]
  congr 1
  apply sum_congr rfl
  intro k hk
  have harg : c * (p * k) ^ 2 = p ^ 2 * (c * k ^ 2) := by ring
  rw [harg, natPhase_lift _ _ _ (pow_ne_zero _ hp.ne')]

theorem gaussNat_one (c : ℕ) : gaussNat 1 c = 1 := by simp [gaussNat]

theorem gaussNat_even_power (p c k : ℕ) (hp : Odd p) (hc : c.Coprime p) :
    gaussNat (p ^ (2 * k)) c = (p : ℂ) ^ k := by
  have hpc : p.Coprime (2 * c) :=
    (Nat.coprime_two_right.mpr hp).mul_right hc.symm
  induction k with
  | zero => simp [gaussNat_one]
  | succ k ih =>
    have hpow : p ^ (2 * (k + 1)) = p ^ 2 * p ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
    rw [hpow, gaussNat_square_factor p _ c hp.pos (pow_pos hp.pos _) hpc, ih, pow_succ]
    ring

theorem gaussNat_odd_power (p c k : ℕ) (hp : Odd p) (hc : c.Coprime p) :
    gaussNat (p ^ (2 * k + 1)) c = (p : ℂ) ^ k * gaussNat p c := by
  have hpc : p.Coprime (2 * c) :=
    (Nat.coprime_two_right.mpr hp).mul_right hc.symm
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : p ^ (2 * (k + 1) + 1) = p ^ 2 * p ^ (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by omega, pow_add]
    rw [hpow, gaussNat_square_factor p _ c hp.pos (pow_pos hp.pos _) hpc, ih, pow_succ]
    ring

theorem gaussNat_even_power_im_zero (p c k : ℕ) (hp : Odd p) (hc : c.Coprime p) :
    (gaussNat (p ^ (2 * k)) c).im = 0 := by
  rw [gaussNat_even_power p c k hp hc]
  norm_cast

theorem gaussNat_prime_odd_power (p c k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hc : c.Coprime p) :
    gaussNat (p ^ (2 * k + 1)) c =
      (p : ℂ) ^ k * (jacobiSym (c : ℤ) p : ℂ) * gaussNat p 1 := by
  have hp : Nat.Prime p := Fact.out
  rw [gaussNat_odd_power p c k (hp.odd_of_ne_two hp2) hc,
    gaussNat_prime_coefficient p c hp2 hc, mul_assoc]

theorem gaussNat_prime_power_one_mod_four_im_zero (p c k : ℕ) [Fact p.Prime]
    (hp4 : p % 4 = 1) (hc : c.Coprime p) :
    (gaussNat (p ^ k) c).im = 0 := by
  have hp2 : p ≠ 2 := by omega
  rcases Nat.even_or_odd' k with ⟨l, rfl | rfl⟩
  · exact gaussNat_even_power_im_zero p c l (Nat.odd_iff.mpr (by omega)) hc
  · rw [gaussNat_prime_odd_power p c l hp2 hc]
    have he : (p : ℂ) ^ l * (jacobiSym (c : ℤ) p : ℂ) =
        (((p : ℝ) ^ l * (jacobiSym (c : ℤ) p : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.mul_im, gaussNat_prime_one_mod_four_im_zero p hp4]
    simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]


theorem gaussNat_eq_phaseVal (M c : ℕ) [NeZero M] :
    gaussNat M c = ∑ a : ZMod M, natPhase M (c * a.val ^ 2) := by
  rw [sum_zmod_eq_range]
  change (∑ a ∈ range M, natPhase M (c * a ^ 2)) =
    ∑ a ∈ range M, natPhase M (c * (a : ZMod M).val ^ 2)
  apply sum_congr rfl
  intro a ha
  rw [ZMod.val_natCast_of_lt (mem_range.mp ha)]

theorem natPhase_crt_square (M N c a b : ℕ) (hM : 0 < M) (hN : 0 < N) :
    natPhase (M * N) (c * (N * a + M * b) ^ 2) =
      natPhase M (c * N * a ^ 2) * natPhase N (c * M * b ^ 2) := by
  have harg : c * (N * a + M * b) ^ 2 =
      (N * (c * N * a ^ 2) + M * (c * M * b ^ 2)) + M * N * (2 * c * a * b) := by ring
  rw [harg, natPhase_period _ _ _ (by positivity), natPhase_add,
    natPhase_lift M N _ hM.ne']
  conv_lhs =>
    arg 1
    rw [mul_comm M N, natPhase_lift N M _ hN.ne']

/-- Coprime Gauss-sum multiplication, proved by the Chinese-remainder bijection. -/
theorem gaussNat_coprime_mul (M N c : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hcop : M.Coprime N) :
    gaussNat (M * N) c = gaussNat M (c * N) * gaussNat N (c * M) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (M * N) := ⟨mul_ne_zero hM.ne' hN.ne'⟩
  let φ : ZMod M × ZMod N → ZMod (M * N) :=
    fun p => ((N * p.1.val + M * p.2.val : ℕ) : ZMod (M * N))
  have hfst (p : ZMod M × ZMod N) : (ZMod.cast (φ p) : ZMod M) = (N : ZMod M) * p.1 := by
    dsimp [φ]
    rw [ZMod.cast_natCast (dvd_mul_right M N)]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
      add_zero, ZMod.natCast_zmod_val]
  have hsnd (p : ZMod M × ZMod N) : (ZMod.cast (φ p) : ZMod N) = (M : ZMod N) * p.2 := by
    dsimp [φ]
    rw [ZMod.cast_natCast (dvd_mul_left N M)]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
      zero_add, ZMod.natCast_zmod_val]
  have hinj : Function.Injective φ := by
    intro p q he
    apply Prod.ext
    · have he' := congrArg (fun a : ZMod (M * N) => (ZMod.cast a : ZMod M)) he
      rw [hfst, hfst] at he'
      exact ((ZMod.isUnit_iff_coprime N M).mpr hcop.symm).mul_left_cancel he'
    · have he' := congrArg (fun a : ZMod (M * N) => (ZMod.cast a : ZMod N)) he
      rw [hsnd, hsnd] at he'
      exact ((ZMod.isUnit_iff_coprime M N).mpr hcop).mul_left_cancel he'
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp [ZMod.card]⟩
  rw [gaussNat_eq, gaussNat_eq_phaseVal M, gaussNat_eq_phaseVal N]
  unfold quadraticGauss
  calc
    _ = ∑ p : ZMod M × ZMod N, ZMod.stdAddChar ((c : ZMod (M * N)) * (φ p) ^ 2) :=
      (Fintype.sum_bijective φ hbij
        (fun p => ZMod.stdAddChar ((c : ZMod (M * N)) * (φ p) ^ 2))
        (fun a => ZMod.stdAddChar ((c : ZMod (M * N)) * a ^ 2)) (fun _ => rfl)).symm
    _ = ∑ p : ZMod M × ZMod N,
        natPhase M (c * N * p.1.val ^ 2) * natPhase N (c * M * p.2.val ^ 2) := by
      apply sum_congr rfl
      intro p hp
      have he : ZMod.stdAddChar ((c : ZMod (M * N)) * (φ p) ^ 2) =
          natPhase (M * N) (c * (N * p.1.val + M * p.2.val) ^ 2) := by
        rw [natPhase_eq_char]
        dsimp [φ]
        push_cast
        rfl
      rw [he, natPhase_crt_square M N c _ _ hM hN]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      dsimp only
      rw [← sum_mul_sum]


theorem chiFour_square_of_odd (M : ℕ) (hM : Odd M) :
    (ZMod.χ₄ (M : ZMod 4) : ℂ) ^ 2 = 1 := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right (by
    have h := Nat.odd_iff.mp hM
    omega : M % 2 ≠ 0)]
  split_ifs <;> norm_num

theorem gaussNat_odd_primePower_sq (p c k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hc : c.Coprime p) :
    gaussNat (p ^ k) c ^ 2 = (ZMod.χ₄ ((p ^ k : ℕ) : ZMod 4) : ℂ) * (p ^ k : ℕ) := by
  have hp : Nat.Prime p := Fact.out
  have hpOdd := hp.odd_of_ne_two hp2
  have hχ2 := chiFour_square_of_odd p hpOdd
  rcases Nat.even_or_odd' k with ⟨l, rfl | rfl⟩
  · have hχe : (ZMod.χ₄ ((p ^ (2 * l) : ℕ) : ZMod 4) : ℂ) = 1 := by
      rw [Nat.cast_pow, map_pow, Int.cast_pow, pow_mul, hχ2, one_pow]
    rw [gaussNat_even_power p c l hpOdd hc, hχe, one_mul, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  · have hχo : (ZMod.χ₄ ((p ^ (2 * l + 1) : ℕ) : ZMod 4) : ℂ) =
        (ZMod.χ₄ (p : ZMod 4) : ℂ) := by
      rw [Nat.cast_pow, map_pow, Int.cast_pow, pow_add, pow_mul, hχ2, one_pow, pow_one, one_mul]
    have hj : (jacobiSym (c : ℤ) p : ℂ) ^ 2 = 1 := by
      exact_mod_cast jacobiSym.sq_one (by simpa using hc.gcd_eq_one)
    rw [gaussNat_prime_odd_power p c l hp2 hc, mul_pow, mul_pow, hj,
      gaussNat_prime_sq p hp2, hχo, Nat.cast_pow]
    rw [← pow_mul, show l * 2 = 2 * l by omega, pow_succ]
    ring

/-- The square of every odd primitive quadratic Gauss sum, without a sign choice. -/
theorem gaussNat_odd_sq (M c : ℕ) (hM : Odd M) (hc : c.Coprime M) :
    gaussNat M c ^ 2 = (ZMod.χ₄ (M : ZMod 4) : ℂ) * M := by
  induction M using Nat.recOnPosPrimePosCoprime generalizing c with
  | zero => simp at hM
  | one =>
    rw [gaussNat_one]
    norm_num [ZMod.χ₄_nat_eq_if_mod_four]
  | prime_pow p k hp hk =>
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      rw [he, Nat.odd_iff] at hM
      simp [Nat.pow_mod, hk.ne'] at hM
    have hcP : c.Coprime p := hc.of_dvd_right (dvd_pow_self p hk.ne')
    exact gaussNat_odd_primePower_sq p c k hp2 hcP
  | coprime M N hMp hNp hcop ihM ihN =>
    have hodd := Nat.odd_mul.mp hM
    have hcMN := Nat.coprime_mul_iff_right.mp hc
    rw [gaussNat_coprime_mul M N c (by omega) (by omega) hcop, mul_pow,
      ihM _ hodd.1 (hcMN.1.mul_left hcop.symm),
      ihN _ hodd.2 (hcMN.2.mul_left hcop)]
    push_cast
    rw [map_mul, Int.cast_mul]
    ring

theorem gaussNat_one_mod_four_im_zero (M c : ℕ) (hM : M % 4 = 1) (hc : c.Coprime M) :
    (gaussNat M c).im = 0 := by
  have hOdd : Odd M := Nat.odd_iff.mpr (by omega)
  have hs := gaussNat_odd_sq M c hOdd hc
  have hχ : ZMod.χ₄ (M : ZMod 4) = 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp [show M % 2 ≠ 0 by omega, hM]
  rw [hχ] at hs
  norm_num at hs
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im] at hr hi
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hOdd.pos
  have hrepr : (gaussNat M c).re ≠ 0 := by
    intro h0
    rw [h0] at hr
    nlinarith [sq_nonneg (gaussNat M c).im]
  have hm : (gaussNat M c).re * (gaussNat M c).im = 0 := by linarith
  exact (mul_eq_zero.mp hm).resolve_left hrepr

/-- Only negative discriminant moduli now require the signed evaluation. -/
def GaussNegativeDiscriminantEvaluation : Prop := ∀ M : ℕ, isNegativeDiscriminantAbs M →
  ∀ c ∈ primitiveResidues M, (gaussNat M c).im = Real.sqrt M * gaussCharacter M c

theorem gaussSignEvaluation_of_negative_discriminants (hG : GaussNegativeDiscriminantEvaluation) :
    GaussSignEvaluation := by
  intro M hM c hc
  by_cases hD : isNegativeDiscriminantAbs M
  · exact hG M hD c hc
  have hcop := (mem_primitiveResidues.mp hc).2.2
  have h0 : M % 4 ≠ 0 := fun h => hD ⟨hM, Or.inl h⟩
  have h3 : M % 4 ≠ 3 := fun h => hD ⟨hM, Or.inr h⟩
  have h12 : M % 4 = 1 ∨ M % 4 = 2 := by omega
  rw [gaussCharacter, ite_eq_right h3, ite_eq_right h0, mul_zero]
  rcases h12 with h1 | h2
  · exact gaussNat_one_mod_four_im_zero M c h1 hcop
  · rw [gaussNat_two_mod_four_zero M c h2 hcop, Complex.zero_im]


/-- The period-halving identity for a quadratic phase at a modulus divisible by four. -/
theorem quadraticPhase_half_period (M c : ℕ) (hM : 0 < M) :
    Function.Periodic (fun k => natPhase (4 * M) (c * k ^ 2)) (2 * M) := by
  intro k
  dsimp only
  have he : c * (k + 2 * M) ^ 2 = c * k ^ 2 + (4 * M) * (c * k + c * M) := by ring
  rw [he, natPhase_period _ _ _ (by positivity)]

/-- The two-adic square-factor recurrence. -/
theorem gaussNat_sixteen_mul (M c : ℕ) (hM : 0 < M) (hc : Odd c) :
    gaussNat (16 * M) c = 2 * gaussNat (4 * M) c := by
  classical
  change (∑ k ∈ range (16 * M), natPhase (16 * M) (c * k ^ 2)) =
    2 * ∑ k ∈ range (4 * M), natPhase (4 * M) (c * k ^ 2)
  rw [show 16 * M = 4 * (4 * M) by ring,
    sum_range_blocks (4 * M) 4 (by positivity)]
  have hterm (a b : ℕ) :
      natPhase (4 * (4 * M)) (c * (a + 4 * M * b) ^ 2) =
        natPhase (4 * (4 * M)) (c * a ^ 2) *
          ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod 4) * (b : ZMod 4)) := by
    have harg : c * (a + 4 * M * b) ^ 2 =
        (c * a ^ 2 + (4 * M) * (2 * c * a * b)) +
          (4 * (4 * M)) * (c * M * b ^ 2) := by ring
    rw [harg, natPhase_period _ _ _ (by positivity), natPhase_add,
      show 4 * (4 * M) = (4 * M) * 4 by ring,
      natPhase_lift _ _ _ (by positivity), natPhase_eq_char 4]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← mul_sum]
  rw [show 4 * (4 * M) = 16 * M by ring]
  have hsum (a : ℕ) :
      ∑ b ∈ range 4, ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod 4) * (b : ZMod 4)) =
        if 2 ∣ a then (4 : ℂ) else 0 := by
    rw [← sum_zmod_eq_range (n := 4) (fun b : ZMod 4 =>
      ZMod.stdAddChar (((2 * c * a : ℕ) : ZMod 4) * b)), character_orthogonality]
    have hcond : ((2 * c * a : ℕ) : ZMod 4) = 0 ↔ 2 ∣ a := by
      rw [ZMod.natCast_eq_zero_iff]
      rw [mul_assoc]
      change 2 * 2 ∣ 2 * (c * a) ↔ 2 ∣ a
      rw [Nat.mul_dvd_mul_iff_left (by omega : 0 < 2),
        (Nat.coprime_two_right.mpr hc).symm.dvd_mul_left]
    simp only [hcond]
    norm_num
  simp_rw [hsum]
  have ht : ∀ a ∈ range (4 * M),
      natPhase (16 * M) (c * a ^ 2) * (if 2 ∣ a then (4 : ℂ) else 0) =
        if 2 ∣ a then (4 : ℂ) * natPhase (16 * M) (c * a ^ 2) else 0 := by
    intro a ha
    split_ifs <;> simp [mul_comm]
  rw [sum_congr rfl ht, ← sum_filter, ← mul_sum,
    show 4 * M = 2 * (2 * M) by ring, sum_range_multiples 2 (2 * M) (by omega)]
  have hlift (k : ℕ) :
      natPhase (16 * M) (c * (2 * k) ^ 2) = natPhase (4 * M) (c * k ^ 2) := by
    rw [show 16 * M = 4 * (4 * M) by ring,
      show c * (2 * k) ^ 2 = 4 * (c * k ^ 2) by ring, natPhase_lift _ _ _ (by omega)]
  simp_rw [hlift]
  have hperiod := sum_periodic_mul (2 * M) 2 _ (quadraticPhase_half_period M c hM)
  rw [show 2 * (2 * M) = 4 * M by ring] at hperiod
  rw [show 2 * (2 * M) = 4 * M by ring, hperiod]
  norm_num
  ring

theorem natPhase_mul_mod (M c k : ℕ) (hM : M ≠ 0) :
    natPhase M (c * k) = natPhase M (c * (k % M)) := by
  let : NeZero M := ⟨hM⟩
  simp [natPhase_eq_char, Nat.cast_mul]

theorem natPhase_mul_right (M k l : ℕ) :
    natPhase M (k * l) = natPhase M k ^ l := by
  unfold natPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem natPhase_four (k : ℕ) : natPhase 4 k = Complex.I ^ k := by
  have h1 : natPhase 4 1 = Complex.I := by
    unfold natPhase
    push_cast
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / 4 =
      (Real.pi : ℂ) / 2 * Complex.I by ring, Complex.exp_pi_div_two_mul_I]
  simpa using (natPhase_mul_right 4 1 k).trans (congrArg (fun z : ℂ => z ^ k) h1)

theorem gaussNat_four (c : ℕ) : gaussNat 4 c = 2 * (1 + Complex.I ^ c) := by
  change (∑ k ∈ range 4, natPhase 4 (c * k ^ 2)) = _
  have hs : ∀ k : ℕ, natPhase 4 (c * k ^ 2) = natPhase 4 (c * (k ^ 2 % 4)) :=
    fun k => natPhase_mul_mod 4 c _ (by omega)
  simp_rw [hs]
  norm_num [sum_range_succ, natPhase_four]
  ring

theorem natPhase_eight_four (c : ℕ) : natPhase 8 (c * 4) = (-1 : ℂ) ^ c := by
  rw [mul_comm, natPhase_mul_right]
  have h4 : natPhase 8 4 = (-1 : ℂ) := by
    unfold natPhase
    norm_num only
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (4 : ℂ) / 8 =
      (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [h4]

theorem natPhase_zero (M : ℕ) : natPhase M 0 = 1 := by simp [natPhase]

theorem gaussNat_eight (c : ℕ) (hc : Odd c) :
    gaussNat 8 c = 4 * natPhase 8 c := by
  change (∑ k ∈ range 8, natPhase 8 (c * k ^ 2)) = _
  have hs : ∀ k : ℕ, natPhase 8 (c * k ^ 2) = natPhase 8 (c * (k ^ 2 % 8)) :=
    fun k => natPhase_mul_mod 8 c _ (by omega)
  simp_rw [hs]
  norm_num only [sum_range_succ, sum_range_zero, Nat.reducePow, Nat.reduceMod,
    mul_zero, mul_one, natPhase_zero, natPhase_eight_four, hc.neg_one_pow]
  ring

theorem gaussNat_two_even_power (c k : ℕ) (hc : Odd c) :
    gaussNat (2 ^ (2 * k + 2)) c = (2 : ℂ) ^ k * gaussNat 4 c := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (2 * (k + 1) + 2) = 16 * 2 ^ (2 * k) := by
      rw [show 2 * (k + 1) + 2 = 4 + 2 * k by omega, pow_add]
      norm_num
    have hpow' : 4 * 2 ^ (2 * k) = 2 ^ (2 * k + 2) := by
      rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add]
      norm_num
    rw [hpow, gaussNat_sixteen_mul _ c (by positivity) hc, hpow', ih, pow_succ]
    ring

theorem gaussNat_two_odd_power (c k : ℕ) (hc : Odd c) :
    gaussNat (2 ^ (2 * k + 3)) c = (2 : ℂ) ^ k * gaussNat 8 c := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (2 * (k + 1) + 3) = 16 * 2 ^ (2 * k + 1) := by
      rw [show 2 * (k + 1) + 3 = 4 + (2 * k + 1) by omega, pow_add]
      norm_num
    have hpow' : 4 * 2 ^ (2 * k + 1) = 2 ^ (2 * k + 3) := by
      conv_rhs => rw [show 2 * k + 3 = 2 + (2 * k + 1) by omega, pow_add]
      norm_num
    rw [hpow, gaussNat_sixteen_mul _ c (by positivity) hc, hpow', ih, pow_succ]
    ring

theorem I_pow_im_of_odd (c : ℕ) (hc : Odd c) :
    (Complex.I ^ c).im = (ZMod.χ₄ (c : ZMod 4) : ℝ) := by
  rw [Complex.I_pow_eq_pow_mod, ZMod.χ₄_nat_eq_if_mod_four,
    ite_eq_right (by have h := Nat.odd_iff.mp hc; omega : c % 2 ≠ 0)]
  have h13 : c % 4 = 1 ∨ c % 4 = 3 := by
    have h := Nat.odd_iff.mp hc
    omega
  rcases h13 with h | h <;> norm_num [h, Complex.I_sq]

theorem gaussNat_four_im (c : ℕ) (hc : Odd c) :
    (gaussNat 4 c).im = 2 * (ZMod.χ₄ (c : ZMod 4) : ℝ) := by
  rw [gaussNat_four, Complex.mul_im, Complex.add_im, I_pow_im_of_odd c hc]
  norm_num

theorem natPhase_mod (M k : ℕ) (hM : M ≠ 0) :
    natPhase M k = natPhase M (k % M) := by
  let : NeZero M := ⟨hM⟩
  simp [natPhase_eq_char]

theorem natPhase_eight_one :
    natPhase 8 1 = (Real.sqrt 2 / 2 : ℂ) * (1 + Complex.I) := by
  unfold natPhase
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / 8 =
    ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    ← Complex.cos_add_sin_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

theorem natPhase_eight_im (c : ℕ) (hc : Odd c) :
    (natPhase 8 c).im = Real.sqrt 2 / 2 * (ZMod.χ₈' (c : ZMod 8) : ℝ) := by
  rw [natPhase_mod 8 c (by omega),
    ← one_mul (c % 8), natPhase_mul_right, natPhase_eight_one,
    ZMod.χ₈'_nat_eq_if_mod_eight,
    ite_eq_right (by have h := Nat.odd_iff.mp hc; omega : c % 2 ≠ 0)]
  have hm : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by
    have h := Nat.odd_iff.mp hc
    omega
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, hs]
  have hs5 : Real.sqrt 2 ^ 5 = 4 * Real.sqrt 2 := by
    rw [show 5 = 3 + 2 by omega, pow_add, hs3, hs]
    ring
  have hs7 : Real.sqrt 2 ^ 7 = 8 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 7 = Real.sqrt 2 ^ 5 * Real.sqrt 2 ^ 2 := by ring
      _ = 8 * Real.sqrt 2 := by rw [hs5, hs]; ring
  rcases hm with h | h | h | h <;>
    norm_num [h, pow_succ, Complex.mul_im, Complex.mul_re] <;>
    ring_nf <;> first | ring | (rw [hs]; norm_num) | (rw [hs5]; ring) | (rw [hs7]; ring)

theorem gaussNat_eight_im (c : ℕ) (hc : Odd c) :
    (gaussNat 8 c).im = 2 * Real.sqrt 2 * (ZMod.χ₈' (c : ZMod 8) : ℝ) := by
  rw [gaussNat_eight c hc, Complex.mul_im, natPhase_eight_im c hc]
  norm_num
  ring

theorem sqrt_nat_even_power (p k : ℕ) :
    Real.sqrt (p ^ (2 * k) : ℕ) = (p : ℝ) ^ k := by
  rw [Nat.cast_pow, show 2 * k = k * 2 by omega, pow_mul, Real.sqrt_sq (by positivity)]

theorem jacobi_neg_two_even_power (c k : ℕ) (hc : Odd c) :
    jacobiSym (-((2 ^ (2 * k + 2) : ℕ) : ℤ)) c = ZMod.χ₄ (c : ZMod 4) := by
  have hj : jacobiSym ((2 : ℕ) : ℤ) c ^ 2 = 1 := jacobiSym.sq_one (by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hc).gcd_eq_one)
  rw [jacobiSym.neg _ hc, Nat.cast_pow, jacobiSym.pow_left,
    show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul, hj, one_pow, mul_one]

theorem jacobi_neg_two_odd_power (c k : ℕ) (hc : Odd c) :
    jacobiSym (-((2 ^ (2 * k + 3) : ℕ) : ℤ)) c = ZMod.χ₈' (c : ZMod 8) := by
  have hj : jacobiSym ((2 : ℕ) : ℤ) c ^ 2 = 1 := jacobiSym.sq_one (by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hc).gcd_eq_one)
  rw [jacobiSym.neg _ hc, Nat.cast_pow, jacobiSym.pow_left,
    show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul, hj,
    one_pow, pow_one, one_mul]
  norm_num only [Nat.cast_ofNat]
  rw [jacobiSym.at_two hc]
  simpa only [Int.cast_natCast] using (ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (c : ℤ)).symm

/-- Signed evaluation for every even positive power of two. -/
theorem gaussNat_two_even_power_im (c k : ℕ) (hc : Odd c) :
    (gaussNat (2 ^ (2 * k + 2)) c).im =
      Real.sqrt (2 ^ (2 * k + 2) : ℕ) *
        (jacobiSym (-((2 ^ (2 * k + 2) : ℕ) : ℤ)) c : ℝ) := by
  have h2 : (2 : ℂ) ^ k = (((2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussNat_two_even_power c k hc, h2, Complex.mul_im, gaussNat_four_im c hc,
    jacobi_neg_two_even_power c k hc,
    show 2 * k + 2 = 2 * (k + 1) by omega, sqrt_nat_even_power]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [pow_succ]
  ring

/-- Signed evaluation for every odd power of two at least eight. -/
theorem gaussNat_two_odd_power_im (c k : ℕ) (hc : Odd c) :
    (gaussNat (2 ^ (2 * k + 3)) c).im =
      Real.sqrt (2 ^ (2 * k + 3) : ℕ) *
        (jacobiSym (-((2 ^ (2 * k + 3) : ℕ) : ℤ)) c : ℝ) := by
  have hs : Real.sqrt (2 ^ (2 * k + 3) : ℕ) = (2 : ℝ) ^ k * (2 * Real.sqrt 2) := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add]
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity), sqrt_nat_even_power]
    norm_num only [pow_one, Nat.cast_ofNat]
    rw [pow_succ]
    ring
  have h2 : (2 : ℂ) ^ k = (((2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussNat_two_odd_power c k hc, h2, Complex.mul_im, gaussNat_eight_im c hc,
    jacobi_neg_two_odd_power c k hc, hs]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- The signed Gauss evaluation for all powers of two divisible by four. -/
theorem gaussNat_two_power_im (c k : ℕ) (hk : 2 ≤ k) (hc : Odd c) :
    (gaussNat (2 ^ k) c).im =
      Real.sqrt (2 ^ k : ℕ) * (jacobiSym (-((2 ^ k : ℕ) : ℤ)) c : ℝ) := by
  rcases Nat.even_or_odd' k with ⟨l, hl | hl⟩
  · have he : k = 2 * (l - 1) + 2 := by omega
    rw [he]
    exact gaussNat_two_even_power_im c (l - 1) hc
  · have he : k = 2 * (l - 1) + 3 := by omega
    rw [he]
    exact gaussNat_two_odd_power_im c (l - 1) hc

theorem gaussSignEvaluation_two_power (c k : ℕ) (hk : 2 ≤ k)
    (hc : c ∈ primitiveResidues (2 ^ k)) :
    (gaussNat (2 ^ k) c).im = Real.sqrt (2 ^ k : ℕ) * gaussCharacter (2 ^ k) c := by
  have hcop := (mem_primitiveResidues.mp hc).2.2
  have hcOdd : Odd c := Nat.coprime_two_right.mp
    (hcop.of_dvd_right (dvd_pow_self 2 (by omega : k ≠ 0)))
  have h4 : (2 ^ k : ℕ) % 4 = 0 := by
    have he : k = 2 + (k - 2) := by omega
    rw [he, pow_add, Nat.mul_mod]
    norm_num
  rw [gaussCharacter, ite_eq_right (by omega : (2 ^ k : ℕ) % 4 ≠ 3),
    ite_eq_left h4]
  exact gaussNat_two_power_im c k hk hcOdd

/-- The final formula with the Gauss assumption restricted to negative discriminant moduli. -/
theorem closed_formula_of_negative_discriminant_inputs
    (hG : GaussNegativeDiscriminantEvaluation)
    (hF : FundamentalDirichletClassNumberFormula) (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n, classRatio (-(M : ℤ)) := by
  exact closed_formula_of_dirichlet_inputs (gaussSignEvaluation_of_negative_discriminants hG) hF hO


theorem gaussNat_primePower_coefficient (p c k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hc : c.Coprime p) :
    gaussNat (p ^ k) c = (jacobiSym (c : ℤ) (p ^ k) : ℂ) * gaussNat (p ^ k) 1 := by
  have hp : Nat.Prime p := Fact.out
  have hpOdd := hp.odd_of_ne_two hp2
  have hj : (jacobiSym (c : ℤ) p : ℂ) ^ 2 = 1 := by
    exact_mod_cast jacobiSym.sq_one (by simpa using hc.gcd_eq_one)
  rcases Nat.even_or_odd' k with ⟨l, rfl | rfl⟩
  · rw [gaussNat_even_power p c l hpOdd hc,
      gaussNat_even_power p 1 l hpOdd (Nat.coprime_one_left p),
      jacobiSym.pow_right, Int.cast_pow, pow_mul, hj, one_pow, one_mul]
  · rw [gaussNat_prime_odd_power p c l hp2 hc,
      gaussNat_odd_power p 1 l hpOdd (Nat.coprime_one_left p),
      jacobiSym.pow_right, Int.cast_pow, pow_add, pow_mul, hj, one_pow, pow_one, one_mul]
    ring

/-- Coefficient scaling by the Jacobi symbol for every odd modulus. -/
theorem gaussNat_odd_coefficient (M c : ℕ) (hM : Odd M) (hc : c.Coprime M) :
    gaussNat M c = (jacobiSym (c : ℤ) M : ℂ) * gaussNat M 1 := by
  induction M using Nat.recOnPosPrimePosCoprime generalizing c with
  | zero => simp at hM
  | one => simp [gaussNat_one]
  | prime_pow p k hp hk =>
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      rw [he, Nat.odd_iff] at hM
      simp [Nat.pow_mod, hk.ne'] at hM
    have hcP : c.Coprime p := hc.of_dvd_right (dvd_pow_self p hk.ne')
    exact gaussNat_primePower_coefficient p c k hp2 hcP
  | coprime M N hMp hNp hcop ihM ihN =>
    let : NeZero M := ⟨by omega⟩
    let : NeZero N := ⟨by omega⟩
    have hodd := Nat.odd_mul.mp hM
    have hcMN := Nat.coprime_mul_iff_right.mp hc
    rw [gaussNat_coprime_mul M N c (by omega) (by omega) hcop,
      gaussNat_coprime_mul M N 1 (by omega) (by omega) hcop]
    rw [ihM _ hodd.1 (hcMN.1.mul_left hcop.symm),
      ihN _ hodd.2 (hcMN.2.mul_left hcop)]
    rw [one_mul, one_mul, ihM N hodd.1 hcop.symm,
      ihN M hodd.2 hcop]
    rw [jacobiSym.mul_right]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.mul_left]
    push_cast
    ring


theorem natPhase_eight_two : natPhase 8 2 = Complex.I := by
  calc
    _ = natPhase 4 1 := by simpa using natPhase_lift 2 4 1 (by omega)
    _ = _ := by rw [natPhase_four]; simp

theorem chiEightPrime_add_two (c : ℕ) (hc : Odd c) :
    ZMod.χ₈' ((c + 2 : ℕ) : ZMod 8) = ZMod.χ₈ (c : ZMod 8) := by
  have h2 := Nat.odd_iff.mp hc
  have hm : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by omega
  rw [ZMod.χ₈'_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
  rcases hm with h | h | h | h <;> norm_num [Nat.add_mod, h2, h]

theorem natPhase_eight_re (c : ℕ) (hc : Odd c) :
    (natPhase 8 c).re = Real.sqrt 2 / 2 * (ZMod.χ₈ (c : ZMod 8) : ℝ) := by
  have hc' : Odd (c + 2) := by
    rw [Nat.odd_iff]
    have h := Nat.odd_iff.mp hc
    omega
  have hi := natPhase_eight_im (c + 2) hc'
  rw [natPhase_add, natPhase_eight_two, Complex.mul_im, chiEightPrime_add_two c hc] at hi
  simpa using hi

theorem gaussNat_eight_re (c : ℕ) (hc : Odd c) :
    (gaussNat 8 c).re = 2 * Real.sqrt 2 * (ZMod.χ₈ (c : ZMod 8) : ℝ) := by
  rw [gaussNat_eight c hc, Complex.mul_re, natPhase_eight_re c hc]
  norm_num
  ring

theorem I_pow_of_odd (c : ℕ) (hc : Odd c) :
    Complex.I ^ c = (ZMod.χ₄ (c : ZMod 4) : ℂ) * Complex.I := by
  rw [Complex.I_pow_eq_pow_mod, ZMod.χ₄_nat_eq_if_mod_four,
    ite_eq_right (by have h := Nat.odd_iff.mp hc; omega : c % 2 ≠ 0)]
  have h13 : c % 4 = 1 ∨ c % 4 = 3 := by
    have h := Nat.odd_iff.mp hc
    omega
  rcases h13 with h | h <;> norm_num [h, Complex.I_sq]

theorem gaussNat_two_even_power_full (c k : ℕ) (hc : Odd c) :
    gaussNat (2 ^ (2 * k + 2)) c =
      (Real.sqrt (2 ^ (2 * k + 2) : ℕ) : ℂ) *
        (1 + (ZMod.χ₄ (c : ZMod 4) : ℂ) * Complex.I) := by
  rw [gaussNat_two_even_power c k hc, gaussNat_four, I_pow_of_odd c hc,
    show 2 * k + 2 = 2 * (k + 1) by omega, sqrt_nat_even_power]
  push_cast
  rw [pow_succ]
  ring

theorem gaussNat_two_odd_power_full (c k : ℕ) (hc : Odd c) :
    gaussNat (2 ^ (2 * k + 3)) c =
      (Real.sqrt (2 ^ (2 * k + 3) : ℕ) : ℂ) *
        ((ZMod.χ₈ (c : ZMod 8) : ℂ) + (ZMod.χ₈' (c : ZMod 8) : ℂ) * Complex.I) := by
  have hs : Real.sqrt (2 ^ (2 * k + 3) : ℕ) = (2 : ℝ) ^ k * (2 * Real.sqrt 2) := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add,
      Nat.cast_mul, Real.sqrt_mul (by positivity), sqrt_nat_even_power]
    norm_num only [pow_one, Nat.cast_ofNat]
    rw [pow_succ]
    ring
  have h2 : (2 : ℂ) ^ k = (((2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussNat_two_odd_power c k hc, hs, h2]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      gaussNat_eight_re c hc, Complex.add_re, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      gaussNat_eight_im c hc, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    ring


/-- The usual phase in the signed evaluation of an odd quadratic Gauss sum. -/
def oddGaussPhase (M : ℕ) : ℂ := if M % 4 = 1 then 1 else Complex.I

theorem oddGaussPhase_even_power (p k : ℕ) (hp : Odd p) :
    oddGaussPhase (p ^ (2 * k)) = 1 := by
  have h13 : p % 4 = 1 ∨ p % 4 = 3 := by have h := Nat.odd_iff.mp hp; omega
  have hs : p ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases h13 with h | h <;> norm_num [h]
  have he : p ^ (2 * k) % 4 = 1 := by
    rw [pow_mul, Nat.pow_mod, hs]
    simp
  simp [oddGaussPhase, he]

theorem oddGaussPhase_odd_power (p k : ℕ) (hp : Odd p) :
    oddGaussPhase (p ^ (2 * k + 1)) = oddGaussPhase p := by
  have h13 : p % 4 = 1 ∨ p % 4 = 3 := by have h := Nat.odd_iff.mp hp; omega
  have hs : p ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases h13 with h | h <;> norm_num [h]
  have he : p ^ (2 * k + 1) % 4 = p % 4 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hs]
    simp
  simp only [oddGaussPhase, he]

theorem sqrt_nat_odd_power (p k : ℕ) :
    Real.sqrt (p ^ (2 * k + 1) : ℕ) = (p : ℝ) ^ k * Real.sqrt p := by
  rw [pow_add, Nat.cast_mul, Real.sqrt_mul (by positivity), sqrt_nat_even_power, pow_one]

/-- The phase correction in the coprime-product formula is precisely quadratic reciprocity. -/
theorem oddGaussPhase_coprime_mul (M N : ℕ) (hM : Odd M) (hN : Odd N)
    (hc : M.Coprime N) :
    (jacobiSym (N : ℤ) M : ℂ) * (jacobiSym (M : ℤ) N : ℂ) *
      oddGaussPhase M * oddGaussPhase N = oddGaussPhase (M * N) := by
  have hM13 : M % 4 = 1 ∨ M % 4 = 3 := by have h := Nat.odd_iff.mp hM; omega
  have hN13 : N % 4 = 1 ∨ N % 4 = 3 := by have h := Nat.odd_iff.mp hN; omega
  have hj : (jacobiSym (N : ℤ) M : ℂ) ^ 2 = 1 := by
    exact_mod_cast jacobiSym.sq_one (by simpa using hc.symm.gcd_eq_one)
  rcases hM13 with hM1 | hM3
  · have hprod : (M * N) % 4 = N % 4 := by
      rw [Nat.mul_mod, hM1]
      omega
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hM1 hN,
      ← pow_two, hj]
    simp [oddGaussPhase, hM1, hprod]
  · rcases hN13 with hN1 | hN3
    · have hprod : (M * N) % 4 = M % 4 := by
        rw [Nat.mul_mod, hN1]
        omega
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' hM hN1,
        ← pow_two, hj]
      simp [oddGaussPhase, hN1, hprod]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four hM3 hN3, Int.cast_neg]
      have hprod : (M * N) % 4 = 1 := by rw [Nat.mul_mod, hM3, hN3]
      simp only [oddGaussPhase, hM3, hN3, hprod]
      norm_num
      calc
        _ = (jacobiSym (N : ℤ) M : ℂ) ^ 2 := by ring_nf; rw [Complex.I_sq]; ring
        _ = 1 := hj

/-- The classical prime Gauss-sum sign proposition, proved below. -/
def OddPrimeGaussEvaluation : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
  gaussNat p 1 = (Real.sqrt p : ℂ) * oddGaussPhase p

/-- All odd moduli reduce to the signed evaluations at odd primes. -/
theorem gaussNat_odd_of_prime_evaluation (hG : OddPrimeGaussEvaluation)
    (M : ℕ) (hM : Odd M) :
    gaussNat M 1 = (Real.sqrt M : ℂ) * oddGaussPhase M := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => simp at hM
  | one => norm_num [gaussNat_one, oddGaussPhase]
  | prime_pow p k hp hk =>
    have hpOdd : Odd p := (Nat.odd_pow_iff hk.ne').mp hM
    have hp2 : p ≠ 2 := by have h := Nat.odd_iff.mp hpOdd; omega
    rcases Nat.even_or_odd' k with ⟨l, rfl | rfl⟩
    · rw [gaussNat_even_power p 1 l hpOdd (Nat.coprime_one_left p),
        sqrt_nat_even_power, oddGaussPhase_even_power p l hpOdd, mul_one]
      push_cast
      rfl
    · rw [gaussNat_odd_power p 1 l hpOdd (Nat.coprime_one_left p),
        hG p hp hp2, sqrt_nat_odd_power, oddGaussPhase_odd_power p l hpOdd]
      push_cast
      ring
  | coprime M N hMp hNp hcop ihM ihN =>
    have hodd := Nat.odd_mul.mp hM
    rw [gaussNat_coprime_mul M N 1 (by omega) (by omega) hcop, one_mul, one_mul,
      gaussNat_odd_coefficient M N hodd.1 hcop.symm,
      gaussNat_odd_coefficient N M hodd.2 hcop, ihM hodd.1, ihN hodd.2]
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    push_cast
    calc
      _ = (Real.sqrt M : ℂ) * (Real.sqrt N : ℂ) *
          ((jacobiSym (N : ℤ) M : ℂ) * (jacobiSym (M : ℤ) N : ℂ) *
            oddGaussPhase M * oddGaussPhase N) := by ring
      _ = _ := by rw [oddGaussPhase_coprime_mul M N hodd.1 hodd.2 hcop]


/-- The paper's imaginary-part formula at all odd moduli, given the classical prime signs. -/
theorem gaussSignEvaluation_odd_of_prime_evaluation (hG : OddPrimeGaussEvaluation)
    (M c : ℕ) (hM : Odd M) (hc : c.Coprime M) :
    (gaussNat M c).im = Real.sqrt M * gaussCharacter M c := by
  have h13 : M % 4 = 1 ∨ M % 4 = 3 := by have h := Nat.odd_iff.mp hM; omega
  rcases h13 with h1 | h3
  · rw [gaussNat_one_mod_four_im_zero M c h1 hc, gaussCharacter,
      ite_eq_right (by omega : M % 4 ≠ 3), ite_eq_right (by omega : M % 4 ≠ 0), mul_zero]
  · rw [gaussNat_odd_coefficient M c hM hc, gaussNat_odd_of_prime_evaluation hG M hM,
      oddGaussPhase, ite_eq_right (by omega : M % 4 ≠ 1),
      gaussCharacter, ite_eq_left h3]
    simp only [Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, add_zero]
    ring


theorem jacobi_two_even_power (c k : ℕ) (hc : Odd c) :
    jacobiSym ((2 ^ (2 * k + 2) : ℕ) : ℤ) c = 1 := by
  have hj : jacobiSym ((2 : ℕ) : ℤ) c ^ 2 = 1 := jacobiSym.sq_one (by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hc).gcd_eq_one)
  rw [Nat.cast_pow, jacobiSym.pow_left,
    show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul, hj, one_pow]

theorem jacobi_two_odd_power (c k : ℕ) (hc : Odd c) :
    jacobiSym ((2 ^ (2 * k + 3) : ℕ) : ℤ) c = ZMod.χ₈ (c : ZMod 8) := by
  have hj : jacobiSym ((2 : ℕ) : ℤ) c ^ 2 = 1 := jacobiSym.sq_one (by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hc).gcd_eq_one)
  rw [Nat.cast_pow, jacobiSym.pow_left,
    show 2 * k + 3 = 2 * (k + 1) + 1 by omega, pow_add, pow_mul, hj,
    one_pow, pow_one, one_mul]
  norm_num only [Nat.cast_ofNat]
  exact jacobiSym.at_two hc

theorem jacobi_negative_odd_swap (N c : ℕ) (hN : Odd N) (hc : Odd c) :
    jacobiSym (-(N : ℤ)) c =
      if N % 4 = 1 then ZMod.χ₄ (c : ZMod 4) * jacobiSym (c : ℤ) N
        else jacobiSym (c : ℤ) N := by
  have h13 : N % 4 = 1 ∨ N % 4 = 3 := by have h := Nat.odd_iff.mp hN; omega
  rcases h13 with h1 | h3
  · rw [ite_eq_left h1, jacobiSym.neg _ hc,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 hc]
  · rw [ite_eq_right (by omega : N % 4 ≠ 1)]
    exact jacobi_negative_three_mod_four h3 (Nat.odd_iff.mp hc)

theorem jacobi_negative_mixed_even_power (N c k : ℕ) (hN : Odd N) (hc : Odd c) :
    jacobiSym (-((2 ^ (2 * k + 2) * N : ℕ) : ℤ)) c =
      if N % 4 = 1 then ZMod.χ₄ (c : ZMod 4) * jacobiSym (c : ℤ) N
        else jacobiSym (c : ℤ) N := by
  rw [Nat.cast_mul, show -( ((2 ^ (2 * k + 2) : ℕ) : ℤ) * N) =
      -(N : ℤ) * ((2 ^ (2 * k + 2) : ℕ) : ℤ) by ring,
    jacobiSym.mul_left, jacobi_two_even_power c k hc, mul_one]
  exact jacobi_negative_odd_swap N c hN hc

theorem jacobi_negative_mixed_odd_power (N c k : ℕ) (hN : Odd N) (hc : Odd c) :
    jacobiSym (-((2 ^ (2 * k + 3) * N : ℕ) : ℤ)) c =
      if N % 4 = 1 then ZMod.χ₈' (c : ZMod 8) * jacobiSym (c : ℤ) N
        else ZMod.χ₈ (c : ZMod 8) * jacobiSym (c : ℤ) N := by
  rw [Nat.cast_mul, show -( ((2 ^ (2 * k + 3) : ℕ) : ℤ) * N) =
      -(N : ℤ) * ((2 ^ (2 * k + 3) : ℕ) : ℤ) by ring,
    jacobiSym.mul_left, jacobi_two_odd_power c k hc,
    jacobi_negative_odd_swap N c hN hc]
  split_ifs
  · have he := ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (c : ℤ)
    simp only [Int.cast_natCast] at he
    rw [he]
    ring
  · ring

theorem chiEight_sq_of_odd (N : ℕ) (hN : Odd N) :
    ZMod.χ₈ (N : ZMod 8) ^ 2 = 1 := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight,
    ite_eq_right (by have h := Nat.odd_iff.mp hN; omega : N % 2 ≠ 0)]
  split_ifs <;> norm_num

theorem chiEightPrime_mul_chiEight_of_odd (N : ℕ) (hN : Odd N) :
    ZMod.χ₈' (N : ZMod 8) * ZMod.χ₈ (N : ZMod 8) = ZMod.χ₄ (N : ZMod 4) := by
  have he := ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (N : ℤ)
  simp only [Int.cast_natCast] at he
  rw [he, mul_assoc, ← pow_two, chiEight_sq_of_odd N hN, mul_one]


/-- Mixed moduli with an even two-adic exponent reduce to the signed odd-prime evaluation. -/
theorem gaussNat_mixed_even_power_im (hG : OddPrimeGaussEvaluation)
    (N c k : ℕ) (hN : Odd N) (hc : Odd c) (hcop : c.Coprime N) :
    (gaussNat (2 ^ (2 * k + 2) * N) c).im =
      Real.sqrt (2 ^ (2 * k + 2) * N : ℕ) *
        (jacobiSym (-((2 ^ (2 * k + 2) * N : ℕ) : ℤ)) c : ℝ) := by
  have h2N : (2 ^ (2 * k + 2)).Coprime N :=
    (Nat.coprime_two_left.mpr hN).pow_left _
  have hj : jacobiSym ((c * 2 ^ (2 * k + 2) : ℕ) : ℤ) N = jacobiSym (c : ℤ) N := by
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobi_two_even_power N k hN, mul_one]
  rw [gaussNat_coprime_mul _ N c (by positivity) hN.pos h2N,
    gaussNat_two_even_power_full _ k (hc.mul hN),
    gaussNat_odd_coefficient N _ hN (hcop.mul_left h2N),
    gaussNat_odd_of_prime_evaluation hG N hN, hj,
    jacobi_negative_mixed_even_power N c k hN hc,
    Nat.cast_mul (2 ^ (2 * k + 2)) N, Real.sqrt_mul (by positivity)]
  have he : ZMod.χ₄ ((c * N : ℕ) : ZMod 4) =
      ZMod.χ₄ (c : ZMod 4) * ZMod.χ₄ (N : ZMod 4) := by
    rw [Nat.cast_mul, map_mul]
  rw [he, Int.cast_mul]
  have h13 : N % 4 = 1 ∨ N % 4 = 3 := by have h := Nat.odd_iff.mp hN; omega
  rcases h13 with h1 | h3
  · rw [oddGaussPhase, ite_eq_left h1, ite_eq_left h1,
      ZMod.χ₄_nat_one_mod_four h1]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Int.cast_one, Int.cast_mul,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    ring
  · rw [oddGaussPhase, ite_eq_right (by omega : N % 4 ≠ 1),
      ite_eq_right (by omega : N % 4 ≠ 1), ZMod.χ₄_nat_three_mod_four h3]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Int.cast_neg,
      Complex.neg_im, neg_zero,
      Int.cast_one, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    ring


/-- Mixed moduli with an odd two-adic exponent reduce to the signed odd-prime evaluation. -/
theorem gaussNat_mixed_odd_power_im (hG : OddPrimeGaussEvaluation)
    (N c k : ℕ) (hN : Odd N) (hc : Odd c) (hcop : c.Coprime N) :
    (gaussNat (2 ^ (2 * k + 3) * N) c).im =
      Real.sqrt (2 ^ (2 * k + 3) * N : ℕ) *
        (jacobiSym (-((2 ^ (2 * k + 3) * N : ℕ) : ℤ)) c : ℝ) := by
  have h2N : (2 ^ (2 * k + 3)).Coprime N :=
    (Nat.coprime_two_left.mpr hN).pow_left _
  have hj : jacobiSym ((c * 2 ^ (2 * k + 3) : ℕ) : ℤ) N =
      jacobiSym (c : ℤ) N * ZMod.χ₈ (N : ZMod 8) := by
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobi_two_odd_power N k hN]
  rw [gaussNat_coprime_mul _ N c (by positivity) hN.pos h2N,
    gaussNat_two_odd_power_full _ k (hc.mul hN),
    gaussNat_odd_coefficient N _ hN (hcop.mul_left h2N),
    gaussNat_odd_of_prime_evaluation hG N hN, hj,
    jacobi_negative_mixed_odd_power N c k hN hc,
    Nat.cast_mul (2 ^ (2 * k + 3)) N, Real.sqrt_mul (by positivity)]
  have he : ZMod.χ₈ ((c * N : ℕ) : ZMod 8) =
      ZMod.χ₈ (c : ZMod 8) * ZMod.χ₈ (N : ZMod 8) := by
    rw [Nat.cast_mul, map_mul]
  have he' : ZMod.χ₈' ((c * N : ℕ) : ZMod 8) =
      ZMod.χ₈' (c : ZMod 8) * ZMod.χ₈' (N : ZMod 8) := by
    rw [Nat.cast_mul, map_mul]
  rw [he, he']
  have hs : (ZMod.χ₈ (N : ZMod 8) : ℝ) ^ 2 = 1 := by
    exact_mod_cast chiEight_sq_of_odd N hN
  have hp : (ZMod.χ₈' (N : ZMod 8) : ℝ) * (ZMod.χ₈ (N : ZMod 8) : ℝ) =
      (ZMod.χ₄ (N : ZMod 4) : ℝ) := by
    exact_mod_cast chiEightPrime_mul_chiEight_of_odd N hN
  have h13 : N % 4 = 1 ∨ N % 4 = 3 := by have h := Nat.odd_iff.mp hN; omega
  rcases h13 with h1 | h3
  · rw [oddGaussPhase, ite_eq_left h1, ite_eq_left h1]
    simp only [Int.cast_mul, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im,
      mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    calc
      _ = Real.sqrt (2 ^ (2 * k + 3) : ℕ) * Real.sqrt N *
          (ZMod.χ₈' (c : ZMod 8) : ℝ) * (jacobiSym (c : ℤ) N : ℝ) *
          ((ZMod.χ₈' (N : ZMod 8) : ℝ) * (ZMod.χ₈ (N : ZMod 8) : ℝ)) := by ring
      _ = _ := by rw [hp, ZMod.χ₄_nat_one_mod_four h1]; norm_num; ring
  · rw [oddGaussPhase, ite_eq_right (by omega : N % 4 ≠ 1),
      ite_eq_right (by omega : N % 4 ≠ 1)]
    simp only [Int.cast_mul, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    calc
      _ = Real.sqrt (2 ^ (2 * k + 3) : ℕ) * Real.sqrt N *
          (ZMod.χ₈ (c : ZMod 8) : ℝ) * (jacobiSym (c : ℤ) N : ℝ) *
          (ZMod.χ₈ (N : ZMod 8) : ℝ) ^ 2 := by ring
      _ = _ := by rw [hs]; ring


/-- Every modulus divisible by four reduces to a power of two and an odd modulus. -/
theorem gaussNat_four_dvd_of_prime_evaluation (hG : OddPrimeGaussEvaluation)
    (M c : ℕ) (hM : 0 < M) (h4 : M % 4 = 0) (hc : c.Coprime M) :
    (gaussNat M c).im = Real.sqrt M * (jacobiSym (-(M : ℤ)) c : ℝ) := by
  obtain ⟨k, N, hN, he⟩ := Nat.exists_eq_two_pow_mul_odd hM.ne'
  have hk : 2 ≤ k := by
    have hodd := Nat.odd_iff.mp hN
    by_contra h
    have h01 : k = 0 ∨ k = 1 := by omega
    rcases h01 with rfl | rfl
    · rw [he] at h4
      norm_num only [pow_zero, one_mul] at h4
      omega
    · rw [he] at h4
      norm_num only [pow_one] at h4
      omega
  have h2M : 2 ∣ M := dvd_trans (by decide : 2 ∣ 4) (Nat.dvd_of_mod_eq_zero h4)
  have hcOdd : Odd c := Nat.coprime_two_right.mp (hc.of_dvd_right h2M)
  have hcN : c.Coprime N := hc.of_dvd_right (he ▸ dvd_mul_left N (2 ^ k))
  rw [he]
  rcases Nat.even_or_odd' k with ⟨l, hl | hl⟩
  · have he' : k = 2 * (l - 1) + 2 := by omega
    rw [he']
    exact gaussNat_mixed_even_power_im hG N c (l - 1) hN hcOdd hcN
  · have he' : k = 2 * (l - 1) + 3 := by omega
    rw [he']
    exact gaussNat_mixed_odd_power_im hG N c (l - 1) hN hcOdd hcN

theorem gaussNegativeDiscriminantEvaluation_of_prime_evaluation
    (hG : OddPrimeGaussEvaluation) : GaussNegativeDiscriminantEvaluation := by
  intro M hM c hc
  have hcop := (mem_primitiveResidues.mp hc).2.2
  rcases hM.2 with h0 | h3
  · rw [gaussCharacter, ite_eq_right (by omega : M % 4 ≠ 3), ite_eq_left h0]
    exact gaussNat_four_dvd_of_prime_evaluation hG M c hM.1 h0 hcop
  · exact gaussSignEvaluation_odd_of_prime_evaluation hG M c
      (Nat.odd_iff.mpr (by omega)) hcop

/-- The full Gauss-sum input follows from only the classical signs at odd primes. -/
theorem gaussSignEvaluation_of_prime_evaluation (hG : OddPrimeGaussEvaluation) :
    GaussSignEvaluation :=
  gaussSignEvaluation_of_negative_discriminants
    (gaussNegativeDiscriminantEvaluation_of_prime_evaluation hG)

/-- The original closed formula, with the Gauss input reduced to odd-prime signs. -/
theorem closed_formula_of_prime_gauss_inputs (hG : OddPrimeGaussEvaluation)
    (hF : FundamentalDirichletClassNumberFormula) (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n, classRatio (-(M : ℤ)) := by
  exact closed_formula_of_dirichlet_inputs (gaussSignEvaluation_of_prime_evaluation hG) hF hO


/-- A theta function with a fixed real first argument tends to one as the second
argument goes vertically to infinity. This is the boundary estimate for Gauss sums. -/
theorem tendsto_jacobiTheta₂_real {α : Type*} {l : Filter α}
    (τ : α → ℂ) (hτ : Filter.Tendsto (fun x => (τ x).im) l Filter.atTop) (z : ℝ) :
    Filter.Tendsto (fun x => jacobiTheta₂ (z : ℂ) (τ x)) l (nhds 1) := by
  have hs : Summable (fun k : ℤ => Real.exp (-Real.pi * (k : ℝ) ^ 2)) := by
    simpa only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] using
      summable_pow_mul_jacobiTheta₂_term_bound 0 (by norm_num : (0 : ℝ) < 1) 0
  have ht : ∀ k : ℤ, Filter.Tendsto (fun x => jacobiTheta₂_term k (z : ℂ) (τ x))
      l (nhds (if k = 0 then (1 : ℂ) else 0)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simpa [jacobiTheta₂_term] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : α => (1 : ℂ)) l (nhds 1))
    · rw [ite_eq_right hk]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have hn : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      have hc : -Real.pi * (k : ℝ) ^ 2 < 0 :=
        mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (sq_pos_of_ne_zero hn)
      convert Real.tendsto_exp_atBot.comp (hτ.const_mul_atTop_of_neg hc) using 1
      ext x
      rw [norm_jacobiTheta₂_term]
      simp only [Complex.ofReal_im, mul_zero, sub_zero]
      congr 1
  have hb : ∀ᶠ x in l, ∀ k : ℤ, ‖jacobiTheta₂_term k (z : ℂ) (τ x)‖ ≤
      Real.exp (-Real.pi * (k : ℝ) ^ 2) := by
    filter_upwards [hτ.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx k
    simpa only [Complex.ofReal_im, abs_zero, one_mul, mul_zero, zero_mul, sub_zero] using
      norm_jacobiTheta₂_term_le (by norm_num : (0 : ℝ) < 1)
        (by simp : |(z : ℂ).im| ≤ (0 : ℝ)) hx k
  simpa only [jacobiTheta₂, tsum_ite_eq, tsum_zero, add_zero] using
    tendsto_tsum_of_dominated_convergence hs ht hb


/-- A shifted Gaussian series, independent of the finite Gauss sum. -/
def shiftedGaussian (a : ℂ) (r : ℝ) : ℂ :=
  ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + r) ^ 2)

/-- Poisson summation for a shifted Gaussian, in theta-function form. -/
theorem shiftedGaussian_eq_theta (a : ℂ) (ha : 0 < a.re) (r : ℝ) :
    shiftedGaussian a r =
      1 / a ^ (1 / 2 : ℂ) * jacobiTheta₂ (r : ℂ) (Complex.I / a) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hterm (n : ℤ) :
      Complex.exp (-(Real.pi : ℂ) * a * (r : ℂ) ^ 2) *
          Complex.exp (-(Real.pi : ℂ) / a * ((n : ℂ) + Complex.I * (-a * r)) ^ 2) =
        jacobiTheta₂_term n (r : ℂ) (Complex.I / a) := by
    rw [← Complex.exp_add, jacobiTheta₂_term]
    congr 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  calc
    shiftedGaussian a r =
        Complex.exp (-(Real.pi : ℂ) * a * (r : ℂ) ^ 2) *
          ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2 +
            2 * Real.pi * (-a * r) * n) := by
      rw [shiftedGaussian, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = Complex.exp (-(Real.pi : ℂ) * a * (r : ℂ) ^ 2) *
          (1 / a ^ (1 / 2 : ℂ) *
            ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / a *
              ((n : ℂ) + Complex.I * (-a * r)) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha]
    _ = _ := by
      rw [mul_left_comm, ← tsum_mul_left]
      congr 1
      rw [jacobiTheta₂]
      exact tsum_congr hterm


/-- The normalized shifted Gaussian tends to one whenever its dual Gaussian
parameter has real part tending to infinity. -/
theorem tendsto_normalized_shiftedGaussian {α : Type*} {l : Filter α}
    (a : α → ℂ) (ha : ∀ᶠ x in l, 0 < (a x).re)
    (hdual : Filter.Tendsto (fun x => ((a x)⁻¹).re) l Filter.atTop) (r : ℝ) :
    Filter.Tendsto (fun x => (a x) ^ (1 / 2 : ℂ) * shiftedGaussian (a x) r)
      l (nhds 1) := by
  have hτ : Filter.Tendsto (fun x => (Complex.I / a x).im) l Filter.atTop := by
    simpa only [div_eq_mul_inv, Complex.I_mul_im] using hdual
  refine (tendsto_jacobiTheta₂_real (fun x => Complex.I / a x) hτ r).congr' ?_
  filter_upwards [ha] with x hx
  have ha0 : a x ≠ 0 := by intro h; simp [h] at hx
  have hp : (a x) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => ha0 h.1
  rw [shiftedGaussian_eq_theta (a x) hx r, ← mul_assoc, mul_one_div_cancel hp, one_mul]


theorem summable_shiftedGaussian (a : ℂ) (ha : 0 < a.re) (r : ℝ) :
    Summable (fun n : ℤ => Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + r) ^ 2)) := by
  have ht : Summable (fun n : ℤ => jacobiTheta₂_term n (Complex.I * a * r) (Complex.I * a)) :=
    (summable_jacobiTheta₂_term_iff _ _).mpr (by simpa only [Complex.I_mul_im] using ha)
  apply (ht.mul_left (Complex.exp (-(Real.pi : ℂ) * a * (r : ℂ) ^ 2))).congr
  intro n
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem gaussianTerm_eq_thetaTerm (a : ℂ) (n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2) =
      jacobiTheta₂_term n 0 (Complex.I * a) := by
  rw [jacobiTheta₂_term]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem summable_bounded_gaussian (f : ℤ → ℂ) (B : ℝ)
    (hB : ∀ n, ‖f n‖ ≤ B) (a : ℂ) (ha : 0 < a.re) :
    Summable (fun n : ℤ => f n * Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2)) := by
  have ht : Summable (fun n : ℤ => jacobiTheta₂_term n 0 (Complex.I * a)) :=
    (summable_jacobiTheta₂_term_iff _ _).mpr (by simpa only [Complex.I_mul_im] using ha)
  apply (ht.norm.mul_left B).of_norm_bounded
  intro n
  rw [norm_mul, gaussianTerm_eq_thetaTerm]
  exact mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _)

/-- A periodic function on the integers is uniformly bounded by the norms of one period. -/
theorem periodic_int_norm_bound (M : ℕ) [NeZero M] (f : ℤ → ℂ)
    (hf : Function.Periodic f (M : ℤ)) (n : ℤ) :
    ‖f n‖ ≤ ∑ r : Fin M, ‖f (r : ℤ)‖ := by
  have he : f n = f (((Int.divModEquiv M n).2 : Fin M) : ℤ) := by
    conv_lhs => rw [← (Int.divModEquiv M).symm_apply_apply n, Int.divModEquiv_symm_apply]
    simpa only [Int.cast_id, add_comm] using
      (hf.int_mul (Int.divModEquiv M n).1) (((Int.divModEquiv M n).2 : Fin M) : ℤ)
  rw [he]
  exact single_le_sum (s := univ) (f := fun r : Fin M => ‖f (r : ℤ)‖)
    (fun r _ => norm_nonneg _) (mem_univ ((Int.divModEquiv M n).2))

/-- Split a periodic Gaussian series into the finitely many residue classes. -/
theorem periodic_gaussian_cosets (M : ℕ) [NeZero M] (f : ℤ → ℂ)
    (hf : Function.Periodic f (M : ℤ)) (a : ℂ) (ha : 0 < a.re) :
    (∑' n : ℤ, f n * Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2)) =
      ∑ r : Fin M, f (r : ℤ) *
        shiftedGaussian (a * (M : ℂ) ^ 2) ((r : ℝ) / M) := by
  let e : Fin M × ℤ ≃ ℤ :=
    (Equiv.prodComm (Fin M) ℤ).trans (Int.divModEquiv M).symm
  let g : ℤ → ℂ := fun n => f n * Complex.exp (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2)
  have hs : Summable g :=
    summable_bounded_gaussian f _ (periodic_int_norm_bound M f hf) a ha
  have he : Summable (fun p : Fin M × ℤ => g (e p)) := by
    exact (e.summable_iff (f := g)).mpr hs
  calc
    (∑' n : ℤ, g n) = ∑' p : Fin M × ℤ, g (e p) := (e.tsum_eq g).symm
    _ = ∑ r : Fin M, ∑' q : ℤ, g (e (r, q)) := by rw [he.tsum_prod, tsum_fintype]
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [shiftedGaussian, ← tsum_mul_left]
      apply tsum_congr
      intro q
      dsimp [g, e]
      rw [Int.divModEquiv_symm_apply]
      have hf' : f (q * (M : ℤ) + r) = f (r : ℤ) := by
        simpa only [Int.cast_id, add_comm] using (hf.int_mul q) (r : ℤ)
      rw [hf']
      congr 1
      congr 1
      push_cast
      have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
      field_simp


/-- Multiplication by a positive real preserves the principal logarithm branch. -/
theorem cpow_mul_positive_real (a : ℂ) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r) (w : ℂ) :
    (a * (r : ℂ)) ^ w = a ^ w * (r : ℂ) ^ w := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha hr0),
    Complex.log_mul_ofReal r hr a ha, Complex.cpow_def_of_ne_zero ha,
    Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le, ← Complex.exp_add]
  congr 1
  ring

theorem half_cpow_mul_nat_square (a : ℂ) (ha : a ≠ 0) (M : ℕ) (hM : 0 < M) :
    (a * (M : ℂ) ^ 2) ^ (1 / 2 : ℂ) = a ^ (1 / 2 : ℂ) * M := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have he : (M : ℂ) ^ 2 = (((M : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, cpow_mul_positive_real a ha _ (sq_pos_of_pos hMR)]
  have hs : ((((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (M : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (sq_nonneg (M : ℝ)), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hMR.le]
    rfl
  rw [hs]


/-- The normalized Gaussian average of any periodic integer sequence tends to
the average of a single period. This is the rational-boundary step in the
Poisson-summation proof of the signed Gauss evaluation. -/
theorem tendsto_periodic_gaussian_average {α : Type*} {l : Filter α}
    (M : ℕ) [NeZero M] (f : ℤ → ℂ) (hf : Function.Periodic f (M : ℤ))
    (a : α → ℂ) (ha : ∀ᶠ x in l, 0 < (a x).re)
    (hdual : Filter.Tendsto (fun x => ((a x)⁻¹).re) l Filter.atTop) :
    Filter.Tendsto
      (fun x => (a x) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, f n * Complex.exp (-(Real.pi : ℂ) * a x * (n : ℂ) ^ 2))
      l (nhds ((∑ r : Fin M, f (r : ℤ)) / M)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := sq_pos_of_pos hMR
  have hMcast : (M : ℂ) ^ 2 = (((M : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have ha' : ∀ᶠ x in l, 0 < (a x * (M : ℂ) ^ 2).re := by
    filter_upwards [ha] with x hx
    rw [hMcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos hx hMsq
  have hdual' : Filter.Tendsto (fun x => ((a x * (M : ℂ) ^ 2)⁻¹).re) l Filter.atTop := by
    simp_rw [hMcast, mul_inv_rev, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    exact hdual.const_mul_atTop (inv_pos.mpr hMsq)
  have hr : ∀ r : Fin M, Filter.Tendsto
      (fun x => f (r : ℤ) * ((a x * (M : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        shiftedGaussian (a x * (M : ℂ) ^ 2) ((r : ℝ) / M)))
      l (nhds (f (r : ℤ))) := by
    intro r
    simpa only [mul_one] using
      (tendsto_normalized_shiftedGaussian (fun x => a x * (M : ℂ) ^ 2)
        ha' hdual' ((r : ℝ) / M)).const_mul (f (r : ℤ))
  have hs := tendsto_finsetSum (univ : Finset (Fin M)) (fun r _ => hr r)
  refine (hs.div_const (M : ℂ)).congr' ?_
  filter_upwards [ha] with x hx
  have ha0 : a x ≠ 0 := by intro h; simp [h] at hx
  rw [periodic_gaussian_cosets M f hf (a x) hx]
  simp_rw [half_cpow_mul_nat_square (a x) ha0 M hM]
  have he :
      (∑ r : Fin M, f (r : ℤ) *
        (a x ^ (1 / 2 : ℂ) * M *
          shiftedGaussian (a x * (M : ℂ) ^ 2) ((r : ℝ) / M))) =
      (a x ^ (1 / 2 : ℂ) *
        ∑ r : Fin M, f (r : ℤ) *
          shiftedGaussian (a x * (M : ℂ) ^ 2) ((r : ℝ) / M)) * M := by
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro r hr'
    ring
  rw [he, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hM.ne')]

/-- The principal square roots supply the orientation in the Poisson proof. -/
theorem gauss_poisson_root_constant (M : ℕ) (hM : 0 < M) :
    (((M : ℂ) ^ 2 / 4) ^ (1 / 2 : ℂ)) *
      ((-2 * Complex.I / M) ^ (1 / 2 : ℂ)) =
        (Real.sqrt M : ℂ) / (1 + Complex.I) := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hsR : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMR
  have hs0 : (Real.sqrt M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsR.ne'
  have hs : (Real.sqrt M : ℂ) ^ 2 = (M : ℂ) := by
    exact_mod_cast Real.sq_sqrt hMR.le
  have h1re : 0 < ((M : ℂ) / 2).re := by
    norm_num
    positivity
  have h1 : ((M : ℂ) ^ 2 / 4) ^ (1 / 2 : ℂ) = (M : ℂ) / 2 := by
    rw [← show ((M : ℂ) / 2) ^ 2 = (M : ℂ) ^ 2 / 4 by ring]
    simpa only [one_div] using Complex.sq_cpow_two_inv h1re
  have h2re : 0 < ((1 - Complex.I) / (Real.sqrt M : ℂ)).re := by
    simp only [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re, Complex.I_re, sub_zero]
    exact div_pos zero_lt_one hsR
  have h2sq : ((1 - Complex.I) / (Real.sqrt M : ℂ)) ^ 2 = -2 * Complex.I / M := by
    rw [div_pow, hs]
    congr 1
    linear_combination Complex.I_sq
  have h2 : (-2 * Complex.I / M) ^ (1 / 2 : ℂ) =
      (1 - Complex.I) / (Real.sqrt M : ℂ) := by
    rw [← h2sq]
    simpa only [one_div] using Complex.sq_cpow_two_inv h2re
  rw [h1, h2]
  have hi0 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  field_simp
  ring_nf
  rw [Complex.I_sq, hs]
  ring

/-- Quadratic phases on all integers, with modulus M. -/
def integerGaussPhase (M : ℕ) [NeZero M] (k : ℤ) : ℂ :=
  ZMod.stdAddChar ((k : ZMod M) ^ 2)

theorem integerGaussPhase_periodic (M : ℕ) [NeZero M] :
    Function.Periodic (integerGaussPhase M) (M : ℤ) := by
  intro k
  simp [integerGaussPhase, Int.cast_add]

theorem integerGaussPhase_exp (M : ℕ) [NeZero M] (k : ℤ) :
    integerGaussPhase M k =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) ^ 2 / M) := by
  unfold integerGaussPhase
  rw [← Int.cast_pow, ZMod.stdAddChar_coe (N := M) (k ^ 2 : ℤ), Int.cast_pow]

theorem sum_integerGaussPhase (M : ℕ) [NeZero M] :
    (∑ r : Fin M, integerGaussPhase M (r : ℤ)) = gaussNat M 1 := by
  change (∑ r : Fin M, (fun k : ℕ => integerGaussPhase M (k : ℤ)) (r : ℕ)) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => integerGaussPhase M (k : ℤ)) M]
  unfold gaussNat
  apply sum_congr rfl
  intro k hk
  rw [integerGaussPhase_exp]
  simp

/-- The period-two phase on the dual side of Gaussian Poisson summation. -/
def integerDualPhase (M : ℕ) (k : ℤ) : ℂ :=
  ZMod.stdAddChar (-(M : ZMod 4) * (k : ZMod 4) ^ 2)

theorem integerDualPhase_periodic (M : ℕ) :
    Function.Periodic (integerDualPhase M) (2 : ℤ) := by
  intro k
  unfold integerDualPhase
  apply congrArg (fun z : ZMod 4 => ZMod.stdAddChar z)
  push_cast
  ring_nf
  simp only [show (4 : ZMod 4) = 0 by decide, mul_zero, neg_zero, sub_zero, zero_sub]

theorem integerDualPhase_exp (M : ℕ) (k : ℤ) :
    integerDualPhase M k =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * M * (k : ℂ) ^ 2 / 2) := by
  unfold integerDualPhase
  have he : -(M : ZMod 4) * (k : ZMod 4) ^ 2 = ((-(M : ℤ) * k ^ 2 : ℤ) : ZMod 4) := by
    push_cast
    rfl
  rw [he, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem sum_integerDualPhase (M : ℕ) :
    (∑ r : Fin 2, integerDualPhase M (r : ℤ)) = 1 + (-Complex.I) ^ M := by
  have h0 : integerDualPhase M 0 = 1 := by simp [integerDualPhase]
  have h1 : integerDualPhase M 1 = (-Complex.I) ^ M := by
    rw [integerDualPhase_exp]
    norm_num only [Int.cast_one, one_pow, mul_one]
    rw [show -(Real.pi : ℂ) * Complex.I * M / 2 =
      (M : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  rw [Fin.sum_univ_two]
  exact congrArg₂ (· + ·) h0 h1

/-- The Gaussian theta series in the right half-plane. -/
def gaussianTheta (a : ℂ) : ℂ :=
  ∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * a * (k : ℂ) ^ 2)

theorem gaussianTheta_poisson (a : ℂ) (ha : 0 < a.re) :
    gaussianTheta a = 1 / a ^ (1 / 2 : ℂ) * gaussianTheta a⁻¹ := by
  simpa only [gaussianTheta, div_eq_mul_inv] using Complex.tsum_exp_neg_mul_int_sq ha

theorem gaussianTheta_gaussPhase (M : ℕ) [NeZero M] (t : ℝ) :
    gaussianTheta ((t : ℂ) - 2 * Complex.I / M) =
      ∑' k : ℤ, integerGaussPhase M k *
        Complex.exp (-(Real.pi : ℂ) * t * (k : ℂ) ^ 2) := by
  rw [gaussianTheta]
  apply tsum_congr
  intro k
  rw [integerGaussPhase_exp, ← Complex.exp_add]
  congr 1
  ring

theorem gaussianTheta_dualPhase (M : ℕ) (b : ℂ) :
    gaussianTheta (b + Complex.I * M / 2) =
      ∑' k : ℤ, integerDualPhase M k *
        Complex.exp (-(Real.pi : ℂ) * b * (k : ℂ) ^ 2) := by
  rw [gaussianTheta]
  apply tsum_congr
  intro k
  rw [integerDualPhase_exp, ← Complex.exp_add]
  congr 1
  ring

/-- The Gauss sum is the normalized rational-boundary value of the Gaussian theta series. -/
theorem tendsto_gaussianTheta_gauss_boundary (M : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) *
        gaussianTheta ((t : ℂ) - 2 * Complex.I / M))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (gaussNat M 1 / M)) := by
  have ha : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < (t : ℂ).re := by
    filter_upwards [(self_mem_nhdsWithin :
      Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))] with t ht
    exact ht
  have hd : Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹).re)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using
      (tendsto_inv_nhdsGT_zero : Filter.Tendsto (fun t : ℝ => t⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have h := tendsto_periodic_gaussian_average M (integerGaussPhase M)
    (integerGaussPhase_periodic M) (fun t : ℝ => (t : ℂ)) ha hd
  rw [sum_integerGaussPhase] at h
  simpa only [← gaussianTheta_gaussPhase M] using h

/-- The parameters paired by Gaussian Poisson summation near a rational boundary. -/
def gaussBoundaryA (M : ℕ) (t : ℝ) : ℂ := (t : ℂ) - 2 * Complex.I / M

def gaussBoundaryB (M : ℕ) (t : ℝ) : ℂ :=
  (M : ℂ) ^ 2 / (4 + 2 * Complex.I * M * t)

def gaussBoundaryDual (M : ℕ) (t : ℝ) : ℂ := (t : ℂ) * gaussBoundaryB M t

theorem gaussBoundary_den_ne_zero (M : ℕ) (t : ℝ) :
    (4 : ℂ) + 2 * Complex.I * M * t ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im] at h'

theorem gaussBoundaryA_re (M : ℕ) (t : ℝ) :
    (gaussBoundaryA M t).re = t := by
  simp [gaussBoundaryA, Complex.div_re, Complex.normSq_natCast]

theorem gaussBoundaryB_re (M : ℕ) (t : ℝ) :
    (gaussBoundaryB M t).re =
      (M : ℝ) ^ 2 * 4 / Complex.normSq (4 + 2 * Complex.I * M * t) := by
  have hMsq : (M : ℂ) ^ 2 = (((M : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussBoundaryB, hMsq, Complex.div_re]
  norm_num [Complex.mul_re, Complex.mul_im]
  rw [hMsq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]

theorem gaussBoundaryB_re_pos (M : ℕ) (hM : 0 < M) (t : ℝ) :
    0 < (gaussBoundaryB M t).re := by
  rw [gaussBoundaryB_re]
  exact div_pos (mul_pos (sq_pos_of_pos (Nat.cast_pos.mpr hM)) (by norm_num))
    (Complex.normSq_pos.mpr (gaussBoundary_den_ne_zero M t))

theorem gaussBoundaryDual_re_pos (M : ℕ) (hM : 0 < M) {t : ℝ} (ht : 0 < t) :
    0 < (gaussBoundaryDual M t).re := by
  simp only [gaussBoundaryDual, Complex.re_ofReal_mul]
  exact mul_pos ht (gaussBoundaryB_re_pos M hM t)

theorem gaussBoundaryDual_inv_re (M : ℕ) (t : ℝ) :
    ((gaussBoundaryDual M t)⁻¹).re = (4 / (M : ℝ) ^ 2) * t⁻¹ := by
  have hMsq : (M : ℂ) ^ 2 = (((M : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussBoundaryDual, gaussBoundaryB, mul_inv_rev, inv_div]
  rw [mul_comm, hMsq, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.div_ofReal_re]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

theorem gaussBoundary_poisson_parameter (M : ℕ) (hM : 0 < M) (t : ℝ) :
    (gaussBoundaryA M t)⁻¹ = gaussBoundaryDual M t + Complex.I * M / 2 := by
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have ha : gaussBoundaryA M t ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
    norm_num [gaussBoundaryA, Complex.div_im, Complex.normSq_natCast,
      Complex.mul_re, Complex.mul_im] at hi
    exact hMR (by linarith)
  have hscale : (4 : ℂ) + 2 * Complex.I * M * t =
      gaussBoundaryA M t * (2 * Complex.I * M) := by
    rw [gaussBoundaryA]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  apply (mul_left_cancel₀ ha)
  rw [mul_inv_cancel₀ ha, gaussBoundaryDual, gaussBoundaryB, hscale]
  field_simp [ha, hMC]
  rw [gaussBoundaryA]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  simp

theorem tendsto_gaussBoundaryA (M : ℕ) :
    Filter.Tendsto (gaussBoundaryA M) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-2 * Complex.I / M)) := by
  have ht := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  change Filter.Tendsto (fun t : ℝ => (t : ℂ) - 2 * Complex.I / M)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (-2 * Complex.I / M))
  convert ht.sub_const (2 * Complex.I / M) using 1
  congr 1
  simp only [Complex.ofReal_zero, zero_sub, neg_div, neg_mul]

theorem tendsto_gaussBoundaryB (M : ℕ) :
    Filter.Tendsto (gaussBoundaryB M) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((M : ℂ) ^ 2 / 4)) := by
  have ht := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  have hd : Filter.Tendsto (fun t : ℝ => (4 : ℂ) + 2 * Complex.I * M * t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (4 : ℂ)) := by
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      (ht.const_mul (2 * Complex.I * M)).const_add 4
  exact tendsto_const_nhds.div hd (by norm_num)

theorem tendsto_gaussBoundaryDual_inv_re (M : ℕ) (hM : 0 < M) :
    Filter.Tendsto (fun t : ℝ => ((gaussBoundaryDual M t)⁻¹).re)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  simp_rw [gaussBoundaryDual_inv_re]
  exact tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)

theorem tendsto_gaussBoundary_roots (M : ℕ) (hM : 0 < M) :
    Filter.Tendsto
      (fun t : ℝ => (gaussBoundaryB M t) ^ (1 / 2 : ℂ) *
        (gaussBoundaryA M t) ^ (1 / 2 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.sqrt M : ℂ) / (1 + Complex.I))) := by
  have hB : ((M : ℂ) ^ 2 / 4) ∈ Complex.slitPlane := by
    apply Or.inl
    have hMsq : (M : ℂ) ^ 2 = (((M : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hMsq]
    change 0 < ((((M : ℝ) ^ 2 : ℝ) : ℂ) / ((4 : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    exact div_pos (sq_pos_of_pos hMR) (by norm_num)
  have hA : (-2 * Complex.I / M) ∈ Complex.slitPlane := by
    apply Or.inr
    norm_num [Complex.div_im, Complex.normSq_natCast, Complex.mul_re,
      Complex.mul_im]
    exact hM.ne'
  have h := ((tendsto_gaussBoundaryB M).cpow (tendsto_const_nhds (x := (1 / 2 : ℂ))) hB).mul
    ((tendsto_gaussBoundaryA M).cpow (tendsto_const_nhds (x := (1 / 2 : ℂ))) hA)
  rw [gauss_poisson_root_constant M hM] at h
  exact h

theorem tendsto_gaussianTheta_dual_boundary (M : ℕ) (hM : 0 < M) :
    Filter.Tendsto
      (fun t : ℝ => (gaussBoundaryDual M t) ^ (1 / 2 : ℂ) *
        gaussianTheta ((gaussBoundaryA M t)⁻¹))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 + (-Complex.I) ^ M) / 2)) := by
  have ha : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < (gaussBoundaryDual M t).re := by
    filter_upwards [(self_mem_nhdsWithin :
      Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))] with t ht
    exact gaussBoundaryDual_re_pos M hM ht
  have h := tendsto_periodic_gaussian_average 2 (integerDualPhase M)
    (integerDualPhase_periodic M) (gaussBoundaryDual M) ha
    (tendsto_gaussBoundaryDual_inv_re M hM)
  rw [sum_integerDualPhase] at h
  simpa only [← gaussianTheta_dualPhase M, ← gaussBoundary_poisson_parameter M hM,
    Nat.cast_ofNat] using h

theorem gaussianTheta_boundary_relation (M : ℕ) (hM : 0 < M) {t : ℝ} (ht : 0 < t) :
    (gaussBoundaryDual M t) ^ (1 / 2 : ℂ) *
      gaussianTheta ((gaussBoundaryA M t)⁻¹) =
      ((gaussBoundaryB M t) ^ (1 / 2 : ℂ) * (gaussBoundaryA M t) ^ (1 / 2 : ℂ)) *
        ((t : ℂ) ^ (1 / 2 : ℂ) * gaussianTheta (gaussBoundaryA M t)) := by
  have hB : gaussBoundaryB M t ≠ 0 := by
    intro h
    have hr := gaussBoundaryB_re_pos M hM t
    simp [h] at hr
  have ha : 0 < (gaussBoundaryA M t).re := by rwa [gaussBoundaryA_re]
  have ha0 : gaussBoundaryA M t ≠ 0 := by intro h; simp [h] at ha
  have hc : (gaussBoundaryA M t) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h
    exact ha0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hp : gaussianTheta ((gaussBoundaryA M t)⁻¹) =
      (gaussBoundaryA M t) ^ (1 / 2 : ℂ) * gaussianTheta (gaussBoundaryA M t) := by
    rw [gaussianTheta_poisson _ ha]
    field_simp
  rw [gaussBoundaryDual, mul_comm (t : ℂ) (gaussBoundaryB M t),
    cpow_mul_positive_real _ hB t ht, hp]
  ring

/-- Comparing both rational-boundary limits fixes the Gauss sum's orientation. -/
theorem gaussNat_poisson_identity (M : ℕ) [NeZero M] :
    ((Real.sqrt M : ℂ) / (1 + Complex.I)) * (gaussNat M 1 / M) =
      (1 + (-Complex.I) ^ M) / 2 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hfirst : Filter.Tendsto
      (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) * gaussianTheta (gaussBoundaryA M t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (gaussNat M 1 / M)) :=
    tendsto_gaussianTheta_gauss_boundary M
  have hprod := (tendsto_gaussBoundary_roots M hM).mul hfirst
  have he : (fun t : ℝ =>
      ((gaussBoundaryB M t) ^ (1 / 2 : ℂ) * (gaussBoundaryA M t) ^ (1 / 2 : ℂ)) *
        ((t : ℂ) ^ (1 / 2 : ℂ) * gaussianTheta (gaussBoundaryA M t))) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ => (gaussBoundaryDual M t) ^ (1 / 2 : ℂ) *
        gaussianTheta ((gaussBoundaryA M t)⁻¹)) := by
    filter_upwards [(self_mem_nhdsWithin :
      Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))] with t ht
    exact (gaussianTheta_boundary_relation M hM ht).symm
  exact tendsto_nhds_unique (hprod.congr' he) (tendsto_gaussianTheta_dual_boundary M hM)

/-- The Gaussian Poisson proof evaluates the quadratic sum for every positive modulus. -/
theorem gaussNat_poisson_evaluation (M : ℕ) [NeZero M] :
    gaussNat M 1 = (Real.sqrt M : ℂ) * (1 + Complex.I) *
      (1 + (-Complex.I) ^ M) / 2 := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hs : (Real.sqrt M : ℂ) ^ 2 = (M : ℂ) := by
    exact_mod_cast Real.sq_sqrt hMR.le
  have hs0 : (Real.sqrt M : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hMR).ne'
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hI : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply mul_left_cancel₀ hs0
  calc
    (Real.sqrt M : ℂ) * gaussNat M 1 =
        (((Real.sqrt M : ℂ) / (1 + Complex.I)) * (gaussNat M 1 / M)) *
          ((M : ℂ) * (1 + Complex.I)) := by
      field_simp
    _ = ((1 + (-Complex.I) ^ M) / 2) * ((M : ℂ) * (1 + Complex.I)) := by
      rw [gaussNat_poisson_identity M]
    _ = (Real.sqrt M : ℂ) *
        ((Real.sqrt M : ℂ) * (1 + Complex.I) * (1 + (-Complex.I) ^ M) / 2) := by
      rw [← hs]
      ring

/-- The signed odd Gauss evaluation, with no Gauss-value hypothesis. -/
theorem gaussNat_odd_evaluation (M : ℕ) (hOdd : Odd M) :
    gaussNat M 1 = (Real.sqrt M : ℂ) * oddGaussPhase M := by
  have hm2 : M % 2 = 1 := Nat.odd_iff.mp hOdd
  have hM : M ≠ 0 := by omega
  let : NeZero M := ⟨hM⟩
  have hm : M % 4 = 1 ∨ M % 4 = 3 := by omega
  rw [gaussNat_poisson_evaluation M, neg_pow, hOdd.neg_one_pow,
    Complex.I_pow_eq_pow_mod]
  rcases hm with hm | hm
  · rw [hm]
    norm_num [oddGaussPhase, hm]
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [hm]
    norm_num [oddGaussPhase, hm]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem oddPrimeGaussEvaluation : OddPrimeGaussEvaluation := by
  intro p hp hp2
  exact gaussNat_odd_evaluation p (hp.odd_of_ne_two hp2)

/-- The signed Gauss input to the original proof is now discharged. -/
theorem gaussSignEvaluation : GaussSignEvaluation :=
  gaussSignEvaluation_of_prime_evaluation oddPrimeGaussEvaluation

/-- Assembly of the original formula from the two class-number identities. -/
theorem closed_formula_of_class_number_inputs
    (hF : FundamentalDirichletClassNumberFormula) (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) := by
  exact closed_formula_of_dirichlet_inputs gaussSignEvaluation hF hO

/-- The integral quadratic order with basis 1, ω and discriminant Δ.
The relation is ω² = (Δ - (Δ mod 4))/4 + (Δ mod 4)ω. -/
abbrev DiscriminantOrder (Δ : ℤ) :=
  QuadraticAlgebra ℤ ((Δ - Δ % 4) / 4) (Δ % 4)

theorem discriminantOrder_discr (Δ : ℤ) (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    (Δ % 4) ^ 2 + 4 * ((Δ - Δ % 4) / 4) = Δ := by
  have hdiv : (Δ - Δ % 4) / 4 * 4 + Δ % 4 = Δ := by omega
  rcases hmod with h | h <;> rw [h] at hdiv ⊢ <;> nlinarith

theorem discriminantOrder_norm_identity (Δ : ℤ)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (z : DiscriminantOrder Δ) :
    4 * QuadraticAlgebra.norm z = (2 * z.re + (Δ % 4) * z.im) ^ 2 - Δ * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  linear_combination -(z.im ^ 2) * (discriminantOrder_discr Δ hmod)

theorem discriminantOrder_norm_nonneg (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (z : DiscriminantOrder Δ) :
    0 ≤ QuadraticAlgebra.norm z := by
  have h := discriminantOrder_norm_identity Δ hmod z
  nlinarith [sq_nonneg (2 * z.re + (Δ % 4) * z.im), sq_nonneg z.im]

theorem discriminantOrder_isUnit_iff_norm_one (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (z : DiscriminantOrder Δ) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  have h := discriminantOrder_norm_nonneg Δ hΔ hmod z
  omega

theorem discriminantOrder_unit_norm_one (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (u : (DiscriminantOrder Δ)ˣ) :
    QuadraticAlgebra.norm (u : DiscriminantOrder Δ) = 1 :=
  (discriminantOrder_isUnit_iff_norm_one Δ hΔ hmod _).mp u.isUnit

theorem discriminantOrder_unit_im_zero (Δ : ℤ) (hΔ : Δ < -4)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (u : (DiscriminantOrder Δ)ˣ) :
    (u : DiscriminantOrder Δ).im = 0 := by
  have hn := discriminantOrder_unit_norm_one Δ (by omega) hmod u
  have hi := discriminantOrder_norm_identity Δ hmod (u : DiscriminantOrder Δ)
  rw [hn] at hi
  by_contra hy
  have hy2 : 1 ≤ (u : DiscriminantOrder Δ).im ^ 2 := by
    have h := sq_pos_of_ne_zero hy
    omega
  nlinarith [sq_nonneg (2 * (u : DiscriminantOrder Δ).re +
    (Δ % 4) * (u : DiscriminantOrder Δ).im)]

theorem discriminantOrder_unit_eq_one_or_neg_one (Δ : ℤ) (hΔ : Δ < -4)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) (u : (DiscriminantOrder Δ)ˣ) :
    u = 1 ∨ u = -1 := by
  have hy := discriminantOrder_unit_im_zero Δ hΔ hmod u
  have hn := discriminantOrder_unit_norm_one Δ (by omega) hmod u
  rw [QuadraticAlgebra.norm_def, hy] at hn
  have hx2 : (u : DiscriminantOrder Δ).re ^ 2 = 1 := by
    simpa only [mul_zero, zero_mul, add_zero, sub_zero, pow_two] using hn
  have hx := sq_eq_one_iff.mp hx2
  rcases hx with hx | hx
  · left
    apply Units.ext
    apply QuadraticAlgebra.ext
    · exact hx
    · exact hy
  · right
    apply Units.ext
    apply QuadraticAlgebra.ext
    · exact hx
    · exact hy

theorem discriminantOrder_unit_card_of_lt (Δ : ℤ) (hΔ : Δ < -4)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    Nat.card (DiscriminantOrder Δ)ˣ = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, -1, ?_, ?_⟩
  · intro h
    have hr := congrArg (fun u : (DiscriminantOrder Δ)ˣ =>
      (u : DiscriminantOrder Δ).re) h
    change (1 : ℤ) = -1 at hr
    omega
  · ext u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact discriminantOrder_unit_eq_one_or_neg_one Δ hΔ hmod u

def discriminantOrderUnitsEquivNormOne (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    (DiscriminantOrder Δ)ˣ ≃ {z : DiscriminantOrder Δ // QuadraticAlgebra.norm z = 1} where
  toFun u := ⟨u, discriminantOrder_unit_norm_one Δ hΔ hmod u⟩
  invFun z := ((discriminantOrder_isUnit_iff_norm_one Δ hΔ hmod z.val).mpr z.property).unit
  left_inv u := Units.ext (IsUnit.unit_spec _)
  right_inv z := by
    apply Subtype.ext
    exact IsUnit.unit_spec ((discriminantOrder_isUnit_iff_norm_one Δ hΔ hmod z.val).mpr z.property)

def negativeThreeNormOneSet : Finset (DiscriminantOrder (-3)) :=
  {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩}

theorem negativeThree_norm_one_iff (z : DiscriminantOrder (-3)) :
    QuadraticAlgebra.norm z = 1 ↔ z ∈ negativeThreeNormOneSet := by
  rcases z with ⟨x, y⟩
  norm_num [QuadraticAlgebra.norm_def, negativeThreeNormOneSet]
  constructor
  · intro hn
    have hx2 : x ^ 2 ≤ 1 := by
      have h : 3 * x ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * y + x)]
      omega
    have hy2 : y ^ 2 ≤ 1 := by
      have h : 3 * y ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * x + y)]
      omega
    have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
    have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith
    rcases hx with ⟨hxl, hxu⟩
    rcases hy with ⟨hyl, hyu⟩
    interval_cases x <;> interval_cases y <;> norm_num at *
  · intro h
    rcases h with h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> norm_num

def negativeFourNormOneSet : Finset (DiscriminantOrder (-4)) :=
  {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩}

theorem negativeFour_norm_one_iff (z : DiscriminantOrder (-4)) :
    QuadraticAlgebra.norm z = 1 ↔ z ∈ negativeFourNormOneSet := by
  rcases z with ⟨x, y⟩
  norm_num [QuadraticAlgebra.norm_def, negativeFourNormOneSet]
  constructor
  · intro hn
    have hx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith [sq_nonneg y]
    have hy : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith [sq_nonneg x]
    rcases hx with ⟨hxl, hxu⟩
    rcases hy with ⟨hyl, hyu⟩
    interval_cases x <;> interval_cases y <;> norm_num at *
  · intro h
    rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> norm_num

theorem discriminantOrder_unit_card_neg_three :
    Nat.card (DiscriminantOrder (-3))ˣ = 6 := by
  let e := (discriminantOrderUnitsEquivNormOne (-3) (by decide) (by decide)).trans
    (Equiv.subtypeEquivRight negativeThree_norm_one_iff)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

theorem discriminantOrder_unit_card_neg_four :
    Nat.card (DiscriminantOrder (-4))ˣ = 4 := by
  let e := (discriminantOrderUnitsEquivNormOne (-4) (by decide) (by decide)).trans
    (Equiv.subtypeEquivRight negativeFour_norm_one_iff)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

/-- The unit-count convention used in the source agrees with the actual group
of units of the integral quadratic order of discriminant Δ. -/
theorem discriminantOrder_unit_card (Δ : ℤ) (hΔ : Δ < 0)
    (hmod : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    Nat.card (DiscriminantOrder Δ)ˣ = orderUnitCount Δ := by
  by_cases h3 : Δ = -3
  · subst Δ
    exact discriminantOrder_unit_card_neg_three
  by_cases h4 : Δ = -4
  · subst Δ
    exact discriminantOrder_unit_card_neg_four
  have hlt : Δ < -4 := by omega
  rw [discriminantOrder_unit_card_of_lt Δ hlt hmod]
  simp [orderUnitCount, h3, h4]

/-- The rational quadratic field associated with an integral quadratic order. -/
abbrev IntegralQuadraticField (a b : ℤ) := QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)

instance integralQuadraticField_no_roots (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ (a : ℚ) + (b : ℚ) * r) := by
  constructor
  intro r hr
  have hd : (b : ℚ) ^ 2 + 4 * (a : ℚ) < 0 := by
    exact_mod_cast (Fact.out : b ^ 2 + 4 * a < 0)
  nlinarith [sq_nonneg (2 * r - (b : ℚ))]

instance integralQuadraticField_numberField (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    NumberField (IntegralQuadraticField a b) := NumberField.mk

theorem integralQuadraticField_finrank (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    Module.finrank ℚ (IntegralQuadraticField a b) = 2 :=
  QuadraticAlgebra.finrank_eq_two (a : ℚ) (b : ℚ)

theorem integralQuadraticField_no_real_embedding (a b : ℤ)
    [Fact (b ^ 2 + 4 * a < 0)] (φ : IntegralQuadraticField a b →+* ℝ) : False := by
  let w : IntegralQuadraticField a b := ⟨0, 1⟩
  have hw : w ^ 2 = (a : IntegralQuadraticField a b) +
      (b : IntegralQuadraticField a b) * w := by
    apply QuadraticAlgebra.ext <;> norm_num [w, pow_two,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  have h := congrArg φ hw
  simp only [map_pow, map_add, map_mul, map_intCast] at h
  have hd : (b : ℝ) ^ 2 + 4 * (a : ℝ) < 0 := by
    exact_mod_cast (Fact.out : b ^ 2 + 4 * a < 0)
  nlinarith [sq_nonneg (2 * φ w - (b : ℝ))]

theorem integralQuadraticField_nrRealPlaces (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    NumberField.InfinitePlace.nrRealPlaces (IntegralQuadraticField a b) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  exact integralQuadraticField_no_real_embedding a b
    (NumberField.InfinitePlace.embedding_of_isReal w.property)

theorem integralQuadraticField_nrComplexPlaces (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    NumberField.InfinitePlace.nrComplexPlaces (IntegralQuadraticField a b) = 1 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (IntegralQuadraticField a b)
  rw [integralQuadraticField_nrRealPlaces, integralQuadraticField_finrank] at h
  omega

/-- Inclusion of an integral quadratic order into its rational quadratic field. -/
def integralQuadraticOrderEmbedding (a b : ℤ) :
    QuadraticAlgebra ℤ a b →+* IntegralQuadraticField a b where
  toFun z := ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := rfl
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_zero' := rfl
  map_add' z w := by
    apply QuadraticAlgebra.ext <;> simp

theorem integralQuadraticOrderEmbedding_injective (a b : ℤ) :
    Function.Injective (integralQuadraticOrderEmbedding a b) := by
  intro z w h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  change (z.re : ℚ) = (w.re : ℚ) at hr
  change (z.im : ℚ) = (w.im : ℚ) at hi
  apply QuadraticAlgebra.ext
  · exact_mod_cast hr
  · exact_mod_cast hi

theorem integralQuadraticOrderEmbedding_isIntegral (a b : ℤ)
    (z : QuadraticAlgebra ℤ a b) :
    IsIntegral ℤ (integralQuadraticOrderEmbedding a b z) :=
  map_isIntegral_int (integralQuadraticOrderEmbedding a b) (Algebra.IsIntegral.isIntegral z)

/-- The order embeds in the actual ring of algebraic integers of its field. -/
def integralQuadraticOrderToIntegers (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    QuadraticAlgebra ℤ a b →+* NumberField.RingOfIntegers (IntegralQuadraticField a b) :=
  (integralQuadraticOrderEmbedding a b).codRestrict
    (integralClosure ℤ (IntegralQuadraticField a b))
    (integralQuadraticOrderEmbedding_isIntegral a b)

theorem integralQuadraticOrderToIntegers_injective (a b : ℤ)
    [Fact (b ^ 2 + 4 * a < 0)] :
    Function.Injective (integralQuadraticOrderToIntegers a b) := by
  intro z w h
  exact integralQuadraticOrderEmbedding_injective a b
    (congrArg NumberField.RingOfIntegers.val h)

/-- The field belonging to the discriminant presentation of a quadratic order. -/
abbrev DiscriminantField (Δ : ℤ) :=
  IntegralQuadraticField ((Δ - Δ % 4) / 4) (Δ % 4)

instance discriminantField_negative_discr (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    Fact ((Δ % 4) ^ 2 + 4 * ((Δ - Δ % 4) / 4) < 0) := by
  constructor
  rw [discriminantOrder_discr Δ Fact.out]
  exact Fact.out

def discriminantOrderToIntegers (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    DiscriminantOrder Δ →+* NumberField.RingOfIntegers (DiscriminantField Δ) :=
  integralQuadraticOrderToIntegers ((Δ - Δ % 4) / 4) (Δ % 4)

theorem discriminantOrderToIntegers_injective (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    Function.Injective (discriminantOrderToIntegers Δ) :=
  integralQuadraticOrderToIntegers_injective ((Δ - Δ % 4) / 4) (Δ % 4)

theorem discriminantField_nrRealPlaces (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    NumberField.InfinitePlace.nrRealPlaces (DiscriminantField Δ) = 0 :=
  integralQuadraticField_nrRealPlaces ((Δ - Δ % 4) / 4) (Δ % 4)

theorem discriminantField_nrComplexPlaces (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    NumberField.InfinitePlace.nrComplexPlaces (DiscriminantField Δ) = 1 :=
  integralQuadraticField_nrComplexPlaces ((Δ - Δ % 4) / 4) (Δ % 4)

/-- Mathlib's analytic class-number theorem now applies to the constructed
quadratic field, with its signature proved rather than assumed. -/
theorem discriminantField_class_number_limit (Δ : ℤ) [Fact (Δ < 0)]
    [Fact (Δ % 4 = 0 ∨ Δ % 4 = 1)] :
    Filter.Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (DiscriminantField Δ) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((2 * Real.pi * NumberField.classNumber (DiscriminantField Δ) /
        (NumberField.Units.torsionOrder (DiscriminantField Δ) *
          Real.sqrt |(NumberField.discr (DiscriminantField Δ) : ℝ)|) : ℝ) : ℂ)) :=
  imaginary_quadratic_class_number_limit (DiscriminantField Δ)
    (discriminantField_nrRealPlaces Δ) (discriminantField_nrComplexPlaces Δ)

theorem integralQuadraticField_norm (a b : ℤ) (z : IntegralQuadraticField a b) :
    Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem integralQuadraticField_trace (a b : ℤ) (z : IntegralQuadraticField a b) :
    Algebra.trace ℚ (IntegralQuadraticField a b) z = QuadraticAlgebra.trace z := by
  have hb : QuadraticAlgebra.basis (a : ℚ) (b : ℚ) (1 : Fin 2) =
      (⟨0, 1⟩ : IntegralQuadraticField a b) := by
    apply (QuadraticAlgebra.basis (a : ℚ) (b : ℚ)).repr.injective
    rw [Module.Basis.repr_self]
    ext i
    rw [QuadraticAlgebra.basis_repr_apply]
    fin_cases i <;> simp
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (a : ℚ) (b : ℚ)),
    Matrix.trace_fin_two, QuadraticAlgebra.trace_def]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, hb,
    QuadraticAlgebra.basis_repr_apply]
  ring

/-- Integral elements have integral rational trace and norm. -/
theorem integralQuadraticField_integral_trace_norm (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)]
    (z : IntegralQuadraticField a b) (hz : IsIntegral ℤ z) :
    (∃ t : ℤ, (t : ℚ) = 2 * z.re + (b : ℚ) * z.im) ∧
      (∃ q : ℤ, (q : ℚ) = z.re ^ 2 + (b : ℚ) * z.re * z.im - (a : ℚ) * z.im ^ 2) := by
  have ht := Algebra.isIntegral_trace (L := ℚ) hz
  have hn := Algebra.isIntegral_norm ℚ hz
  rw [integralQuadraticField_trace, QuadraticAlgebra.trace_def] at ht
  rw [integralQuadraticField_norm, QuadraticAlgebra.norm_def] at hn
  constructor
  · exact IsIntegrallyClosed.isIntegral_iff.mp ht
  · obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
    refine ⟨q, ?_⟩
    rw [← show (algebraMap ℤ ℚ) q = (q : ℚ) by rfl, hq]
    ring

theorem integralQuadraticField_isIntegral_of_trace_norm (a b : ℤ)
    (z : IntegralQuadraticField a b)
    (ht : ∃ t : ℤ, (t : ℚ) = 2 * z.re + (b : ℚ) * z.im)
    (hn : ∃ q : ℤ, (q : ℚ) = z.re ^ 2 + (b : ℚ) * z.re * z.im -
      (a : ℚ) * z.im ^ 2) : IsIntegral ℤ z := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨q, hn⟩ := hn
  refine ⟨Polynomial.X ^ 2 + (-Polynomial.C t * Polynomial.X + Polynomial.C q), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree
    norm_num
  · have htrace : QuadraticAlgebra.trace z = (t : ℚ) := by
      rw [QuadraticAlgebra.trace_def]
      exact ht.symm
    have hnorm : QuadraticAlgebra.norm z = (q : ℚ) := by
      rw [QuadraticAlgebra.norm_def, hn]
      ring
    have h := QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero z
    rw [htrace, hnorm] at h
    have h' : z ^ 2 - (t : IntegralQuadraticField a b) * z +
        (q : IntegralQuadraticField a b) = 0 := by
      simpa only [Algebra.smul_def, map_intCast] using h
    change Polynomial.aeval z
      (Polynomial.X ^ 2 + (-Polynomial.C t * Polynomial.X + Polynomial.C q)) = 0
    have hat : (algebraMap ℤ (IntegralQuadraticField a b)) t =
        (t : IntegralQuadraticField a b) := map_intCast _ t
    have haq : (algebraMap ℤ (IntegralQuadraticField a b)) q =
        (q : IntegralQuadraticField a b) := map_intCast _ q
    simpa only [map_add, map_mul, map_pow, map_neg, Polynomial.aeval_C,
      Polynomial.aeval_X, sub_eq_add_neg, neg_mul, hat, haq, add_assoc] using h'

/-- A quadratic element is integral exactly when its rational trace and norm
are integers. This is the starting point for identifying maximal orders. -/
theorem integralQuadraticField_isIntegral_iff (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)]
    (z : IntegralQuadraticField a b) :
    IsIntegral ℤ z ↔
      (∃ t : ℤ, (t : ℚ) = 2 * z.re + (b : ℚ) * z.im) ∧
      (∃ q : ℤ, (q : ℚ) = z.re ^ 2 + (b : ℚ) * z.re * z.im -
        (a : ℚ) * z.im ^ 2) :=
  ⟨integralQuadraticField_integral_trace_norm a b z,
    fun h => integralQuadraticField_isIntegral_of_trace_norm a b z h.1 h.2⟩

theorem rational_square_denominator_dvd (D k : ℤ) (y : ℚ)
    (hy : (D : ℚ) * y ^ 2 = (k : ℚ)) :
    (y.den : ℤ) ^ 2 ∣ D := by
  have heQ : (D : ℚ) * (y.num : ℚ) ^ 2 = (k : ℚ) * (y.den : ℚ) ^ 2 := by
    rw [← Rat.mul_den_eq_num]
    calc
      _ = ((D : ℚ) * y ^ 2) * (y.den : ℚ) ^ 2 := by ring
      _ = (k : ℚ) * (y.den : ℚ) ^ 2 := by rw [hy]
  have he : D * y.num ^ 2 = k * (y.den : ℤ) ^ 2 := by exact_mod_cast heQ
  have hc : IsCoprime (y.den : ℤ) y.num :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using y.reduced.symm)
  apply hc.pow.dvd_of_dvd_mul_left
  exact ⟨k, by nlinarith [he]⟩

/-- A fundamental discriminant cannot acquire a rational square factor while
remaining an integral discriminant. -/
theorem fundamental_discriminant_rational_factor_integral (D t q : ℤ)
    (hD : Int.IsFundamentalDiscr D) (y : ℚ)
    (hy : (D : ℚ) * y ^ 2 = (t : ℚ) ^ 2 - 4 * (q : ℚ)) :
    y.den = 1 := by
  have hs : (y.den : ℤ) ^ 2 ∣ D := rational_square_denominator_dvd D (t ^ 2 - 4 * q) y
    (by exact_mod_cast hy)
  have heQ : (D : ℚ) * (y.num : ℚ) ^ 2 =
      ((t : ℚ) ^ 2 - 4 * (q : ℚ)) * (y.den : ℚ) ^ 2 := by
    rw [← Rat.mul_den_eq_num]
    calc
      _ = ((D : ℚ) * y ^ 2) * (y.den : ℚ) ^ 2 := by ring
      _ = _ := by rw [hy]
  have he : D * y.num ^ 2 = (t ^ 2 - 4 * q) * (y.den : ℤ) ^ 2 := by
    exact_mod_cast heQ
  have hc : IsCoprime (y.den : ℤ) y.num :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using y.reduced.symm)
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  have hpdZ : (p : ℤ) ∣ (y.den : ℤ) := by exact_mod_cast hpd
  have hpD : (p : ℤ) ^ 2 ∣ D := (pow_dvd_pow_of_dvd hpdZ 2).trans hs
  by_cases hp2 : p = 2
  · subst p
    have h4 : (4 : ℤ) ∣ D := by simpa using hpD
    obtain ⟨e, heD⟩ := h4
    obtain ⟨k, hk⟩ := hpdZ
    have hnum : y.num % 2 = 1 := by
      by_contra h
      have hn : (2 : ℤ) ∣ y.num := by omega
      have hu : IsUnit (2 : ℤ) := hc.isUnit_of_dvd' ⟨k, by simpa using hk⟩ hn
      norm_num [Int.isUnit_iff] at hu
    rw [heD, hk] at he
    norm_num only [Nat.cast_ofNat] at he
    have hrel : e * y.num ^ 2 = (t * k) ^ 2 - 4 * q * k ^ 2 := by nlinarith [he]
    have hm := congrArg (fun z : ℤ => z % 4) hrel
    norm_num [Int.mul_emod, Int.sub_emod, Int.sq_emod_four, hnum] at hm
    have hemod : e % 4 = 0 ∨ e % 4 = 1 := by omega
    obtain ⟨hne4, hne1⟩ := hD.2.1 e heD
    rcases hemod with hemod | hemod
    · exact hne4 (by omega)
    · exact hne1 hemod
  · exact hD.2.2 p hp (hp.odd_of_ne_two hp2) hpD

/-- Fundamental discriminants force both coordinates of an integral element
to be integers in the order basis. -/
theorem integralQuadraticField_coordinates_of_fundamental (a b D : ℤ)
    [Fact (b ^ 2 + 4 * a < 0)] (hdisc : b ^ 2 + 4 * a = D)
    (hD : Int.IsFundamentalDiscr D) (z : IntegralQuadraticField a b) (hz : IsIntegral ℤ z) :
    ∃ x y : ℤ, z = integralQuadraticOrderEmbedding a b ⟨x, y⟩ := by
  obtain ⟨⟨t, ht⟩, ⟨q, hq⟩⟩ := integralQuadraticField_integral_trace_norm a b z hz
  have hdiscQ : (b : ℚ) ^ 2 + 4 * (a : ℚ) = (D : ℚ) := by exact_mod_cast hdisc
  have hyrel : (D : ℚ) * z.im ^ 2 = (t : ℚ) ^ 2 - 4 * (q : ℚ) := by
    rw [ht, hq, ← hdiscQ]
    ring
  have hyden := fundamental_discriminant_rational_factor_integral D t q hD z.im hyrel
  let y : ℤ := z.im.num
  have hy : (y : ℚ) = z.im := Rat.coe_int_num_of_den_eq_one hyden
  have hyrelInt : D * y ^ 2 = t ^ 2 - 4 * q := by
    rw [← hy] at hyrel
    exact_mod_cast hyrel
  have hparrel : t ^ 2 - (b * y) ^ 2 = 4 * (q + a * y ^ 2) := by
    nlinarith [hyrelInt, hdisc]
  have hm : t ^ 2 % 4 = (b * y) ^ 2 % 4 := by omega
  rw [Int.sq_emod_four, Int.sq_emod_four] at hm
  have h2 : (2 : ℤ) ∣ t - b * y := by omega
  obtain ⟨x, hx⟩ := h2
  have hxQ : (t : ℚ) - (b : ℚ) * (y : ℚ) = 2 * (x : ℚ) := by exact_mod_cast hx
  have hx' : z.re = (x : ℚ) := by
    rw [← hy] at ht
    nlinarith
  refine ⟨x, y, ?_⟩
  apply QuadraticAlgebra.ext
  · exact hx'
  · exact hy.symm

theorem discriminantOrderToIntegers_surjective (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Surjective (discriminantOrderToIntegers D) := by
  intro z
  obtain ⟨x, y, hxy⟩ := integralQuadraticField_coordinates_of_fundamental
    ((D - D % 4) / 4) (D % 4) D (discriminantOrder_discr D Fact.out) hD
    (NumberField.RingOfIntegers.val z) z.isIntegral_coe
  refine ⟨⟨x, y⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  exact hxy.symm

/-- At a fundamental discriminant the constructed quadratic order is the
maximal order, with an explicit equivalence to Mathlib's ring of integers. -/
def discriminantOrderEquivIntegers (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    DiscriminantOrder D ≃+* NumberField.RingOfIntegers (DiscriminantField D) :=
  RingEquiv.ofBijective (discriminantOrderToIntegers D)
    ⟨discriminantOrderToIntegers_injective D, discriminantOrderToIntegers_surjective D hD⟩

theorem discriminantField_unit_card (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Nat.card (NumberField.RingOfIntegers (DiscriminantField D))ˣ = orderUnitCount D := by
  let e := Units.mapEquiv (discriminantOrderEquivIntegers D hD).toMulEquiv
  calc
    _ = Nat.card (DiscriminantOrder D)ˣ := (Nat.card_congr e.toEquiv).symm
    _ = orderUnitCount D := discriminantOrder_unit_card D Fact.out Fact.out

/-- For an imaginary quadratic field all units are torsion, and their order
agrees with the unit count in the source formula. -/
theorem discriminantField_torsionOrder (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    NumberField.Units.torsionOrder (DiscriminantField D) = orderUnitCount D := by
  have hc := discriminantField_unit_card D hD
  have hp : orderUnitCount D ≠ 0 := by
    unfold orderUnitCount
    split_ifs <;> norm_num
  let : Finite (NumberField.RingOfIntegers (DiscriminantField D))ˣ :=
    Nat.finite_of_card_ne_zero (by rwa [hc])
  have ht : NumberField.Units.torsion (DiscriminantField D) = ⊤ := by
    ext u
    simp only [Subgroup.mem_top, iff_true]
    exact (CommGroup.mem_torsion u).mpr (isOfFinOrder_of_finite u)
  rw [NumberField.Units.torsionOrder, ht]
  exact (Nat.card_congr (Subgroup.topEquiv.toEquiv)).trans hc

theorem quadraticAlgebra_basis_one {R : Type*} [CommRing R] (a b : R) :
    QuadraticAlgebra.basis a b (1 : Fin 2) = (⟨0, 1⟩ : QuadraticAlgebra R a b) := by
  apply (QuadraticAlgebra.basis a b).repr.injective
  rw [Module.Basis.repr_self]
  ext i
  rw [QuadraticAlgebra.basis_repr_apply]
  fin_cases i <;> simp

theorem quadraticAlgebra_algebra_trace {R : Type*} [CommRing R]
    (a b : R) (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b),
    Matrix.trace_fin_two, QuadraticAlgebra.trace_def]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    QuadraticAlgebra.basis_repr_apply]
  ring

theorem quadraticAlgebra_basis_discriminant {R : Type*} [CommRing R] (a b : R) :
    Algebra.discr R (QuadraticAlgebra.basis a b) = b ^ 2 + 4 * a := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, quadraticAlgebra_algebra_trace,
    QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/-- The discriminant of the constructed field is D when D is fundamental. -/
theorem discriminantField_discr (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    NumberField.discr (DiscriminantField D) = D := by
  let e := (discriminantOrderEquivIntegers D hD).toIntAlgEquiv
  let B := QuadraticAlgebra.basis ((D - D % 4) / 4) (D % 4)
  have hm : Algebra.traceMatrix ℤ (B.map e.toLinearEquiv) = Algebra.traceMatrix ℤ B := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Module.Basis.map_apply]
    change Algebra.trace ℤ (NumberField.RingOfIntegers (DiscriminantField D))
      (e (B i) * e (B j)) = Algebra.trace ℤ (DiscriminantOrder D) (B i * B j)
    rw [← map_mul, Algebra.trace_eq_of_algEquiv]
    rfl
  calc
    _ = Algebra.discr ℤ (B.map e.toLinearEquiv) :=
      (NumberField.discr_eq_discr _ _).symm
    _ = Algebra.discr ℤ B := by rw [Algebra.discr_def, Algebra.discr_def, hm]
    _ = (D % 4) ^ 2 + 4 * ((D - D % 4) / 4) :=
      quadraticAlgebra_basis_discriminant _ _
    _ = D := discriminantOrder_discr D Fact.out

/-- The analytic residue formula with the actual fundamental discriminant
and unit count identified. The remaining class number is Mathlib's ideal class number. -/
theorem discriminantField_class_number_limit_explicit (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Filter.Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (DiscriminantField D) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((2 * Real.pi * NumberField.classNumber (DiscriminantField D) /
        (orderUnitCount D * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ)) := by
  have h := discriminantField_class_number_limit D
  rw [discriminantField_discr D hD, discriminantField_torsionOrder D hD] at h
  exact h

/-- The form's middle coefficient has the parity required by the order basis. -/
theorem PrimitivePositiveForm.discriminant_mod_four {D : ℤ} (f : PrimitivePositiveForm D) :
    D % 4 = f.b % 2 := by
  have he : f.b ^ 2 = D + 4 * (f.a * f.c) := by nlinarith [f.discriminant]
  have hm : f.b ^ 2 % 4 = D % 4 := by omega
  rw [Int.sq_emod_four] at hm
  exact hm.symm

theorem PrimitivePositiveForm.discriminant_is_discriminant {D : ℤ}
    (f : PrimitivePositiveForm D) : D % 4 = 0 ∨ D % 4 = 1 := by
  rw [f.discriminant_mod_four]
  omega

/-- In the order basis, (b + √D)/2 = shift + ω. -/
def formOrderShift {D : ℤ} (f : PrimitivePositiveForm D) : ℤ := (f.b - D % 4) / 2

theorem formOrderShift_relation {D : ℤ} (f : PrimitivePositiveForm D) :
    2 * formOrderShift f + D % 4 = f.b := by
  have hm := f.discriminant_mod_four
  unfold formOrderShift
  omega

theorem formOrderShift_norm_relation {D : ℤ} (f : PrimitivePositiveForm D) :
    formOrderShift f ^ 2 + (D % 4) * formOrderShift f - (D - D % 4) / 4 = f.a * f.c := by
  have hd := discriminantOrder_discr D f.discriminant_is_discriminant
  have hb := formOrderShift_relation f
  have hf := f.discriminant
  rw [← hb] at hf
  nlinarith

/-- The classical integral ideal [a, (b + √D)/2] attached to a primitive form. -/
def formOrderIdeal {D : ℤ} (f : PrimitivePositiveForm D) : Ideal (DiscriminantOrder D) where
  carrier := {z | f.a ∣ z.re - formOrderShift f * z.im}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    change f.a ∣ (z + w).re - formOrderShift f * (z + w).im
    have h := dvd_add hz hw
    simpa only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, mul_add,
      sub_add_sub_comm] using h
  smul_mem' := by
    intro r z hz
    change f.a ∣ (r * z).re - formOrderShift f * (r * z).im
    have hnorm := formOrderShift_norm_relation f
    obtain ⟨k, hk⟩ := hz
    refine ⟨(r.re - formOrderShift f * r.im) * k - f.c * r.im * z.im, ?_⟩
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (r.re - formOrderShift f * r.im) * hk -
      (r.im * z.im) * hnorm

theorem mem_formOrderIdeal {D : ℤ} (f : PrimitivePositiveForm D) (z : DiscriminantOrder D) :
    z ∈ formOrderIdeal f ↔ f.a ∣ z.re - formOrderShift f * z.im := Iff.rfl

theorem formOrderIdeal_basis_mem {D : ℤ} (f : PrimitivePositiveForm D) :
    (⟨f.a, 0⟩ : DiscriminantOrder D) ∈ formOrderIdeal f ∧
      (⟨formOrderShift f, 1⟩ : DiscriminantOrder D) ∈ formOrderIdeal f := by
  simp [mem_formOrderIdeal]

theorem formOrderIdeal_ne_bot {D : ℤ} (f : PrimitivePositiveForm D) :
    formOrderIdeal f ≠ ⊥ := by
  intro h
  have hm := formOrderIdeal_basis_mem f
  rw [h] at hm
  have hr := congrArg QuadraticAlgebra.re hm.1
  exact f.positive.ne' hr

theorem formOrderIdeal_lattice {D : ℤ} (f : PrimitivePositiveForm D) (z : DiscriminantOrder D) :
    z ∈ formOrderIdeal f ↔ ∃ x y : ℤ,
      z = ⟨f.a * x + formOrderShift f * y, y⟩ := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, z.im, ?_⟩
    apply QuadraticAlgebra.ext
    · change z.re = f.a * x + formOrderShift f * z.im
      linarith
    · rfl
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, by simp⟩

/-- The field norm on the ideal lattice is a times the original form. -/
theorem formOrderIdeal_norm {D : ℤ} (f : PrimitivePositiveForm D) (x y : ℤ) :
    QuadraticAlgebra.norm (⟨f.a * x + formOrderShift f * y, y⟩ : DiscriminantOrder D) =
      f.a * f.eval ![x, y] := by
  have h := formOrderShift_norm_relation f
  have hb := formOrderShift_relation f
  simp only [QuadraticAlgebra.norm_def, PrimitivePositiveForm.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (f.a * x * y) * hb + y ^ 2 * h

def formOrderResidueHom {D : ℤ} (f : PrimitivePositiveForm D) :
    DiscriminantOrder D →+* ZMod f.a.natAbs where
  toFun z := ((z.re - formOrderShift f * z.im : ℤ) : ZMod f.a.natAbs)
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by simp
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    push_cast
    ring
  map_mul' z w := by
    have ha : (f.a : ZMod f.a.natAbs) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd f.a f.a.natAbs).mpr (by
        rw [Int.natCast_natAbs, abs_of_pos f.positive])
    have hn := formOrderShift_norm_relation f
    have hc : (((D - D % 4) / 4 - formOrderShift f ^ 2 -
        (D % 4) * formOrderShift f : ℤ) : ZMod f.a.natAbs) = 0 := by
      rw [show (D - D % 4) / 4 - formOrderShift f ^ 2 -
        (D % 4) * formOrderShift f = -f.a * f.c by nlinarith [hn]]
      simp [ha]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast at hc ⊢
    linear_combination (z.im : ZMod f.a.natAbs) * (w.im : ZMod f.a.natAbs) * hc

theorem formOrderResidueHom_surjective {D : ℤ} (f : PrimitivePositiveForm D) :
    Function.Surjective (formOrderResidueHom f) := by
  intro z
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective z
  refine ⟨⟨x, 0⟩, ?_⟩
  simpa [formOrderResidueHom] using hx

theorem formOrderResidueHom_ker {D : ℤ} (f : PrimitivePositiveForm D) :
    RingHom.ker (formOrderResidueHom f) = formOrderIdeal f := by
  ext z
  change ((z.re - formOrderShift f * z.im : ℤ) : ZMod f.a.natAbs) = 0 ↔
    f.a ∣ z.re - formOrderShift f * z.im
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_natAbs, abs_of_pos f.positive]

/-- The ideal attached to a form has a residue ring of order a. -/
def formOrderIdeal_quotientEquiv {D : ℤ} (f : PrimitivePositiveForm D) :
    DiscriminantOrder D ⧸ formOrderIdeal f ≃+* ZMod f.a.natAbs :=
  (Ideal.quotEquivOfEq (formOrderResidueHom_ker f).symm).trans
    (RingHom.quotientKerEquivOfSurjective (formOrderResidueHom_surjective f))

theorem formOrderIdeal_quotient_card {D : ℤ} (f : PrimitivePositiveForm D) :
    Nat.card (DiscriminantOrder D ⧸ formOrderIdeal f) = f.a.natAbs := by
  rw [Nat.card_congr (formOrderIdeal_quotientEquiv f).toEquiv, Nat.card_zmod]

instance integralQuadraticOrderAlgebra (a b : ℤ) :
    Algebra (QuadraticAlgebra ℤ a b) (IntegralQuadraticField a b) :=
  (integralQuadraticOrderEmbedding a b).toAlgebra

instance integralQuadraticOrderFaithful (a b : ℤ) :
    FaithfulSMul (QuadraticAlgebra ℤ a b) (IntegralQuadraticField a b) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (integralQuadraticOrderEmbedding_injective a b)

instance integralQuadraticOrderIsDomain (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    IsDomain (QuadraticAlgebra ℤ a b) :=
  Function.Injective.isDomain (integralQuadraticOrderEmbedding a b)
    (integralQuadraticOrderEmbedding_injective a b)

theorem integralQuadraticOrder_clear_denominators (a b : ℤ) (z : IntegralQuadraticField a b) :
    ∃ x y : QuadraticAlgebra ℤ a b, y ≠ 0 ∧
      z * integralQuadraticOrderEmbedding a b y = integralQuadraticOrderEmbedding a b x := by
  let x : QuadraticAlgebra ℤ a b := ⟨z.re.num * z.im.den, z.im.num * z.re.den⟩
  let y : QuadraticAlgebra ℤ a b := ⟨(z.re.den * z.im.den : ℕ), 0⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    have hr := congrArg QuadraticAlgebra.re h
    change ((z.re.den * z.im.den : ℕ) : ℤ) = 0 at hr
    have hp : 0 < z.re.den * z.im.den := Nat.mul_pos z.re.den_pos z.im.den_pos
    exact (Nat.cast_ne_zero.mpr hp.ne') hr
  · apply QuadraticAlgebra.ext
    · change z.re * ((z.re.den * z.im.den : ℕ) : ℚ) + (a : ℚ) * z.im * 0 =
        ((z.re.num * z.im.den : ℤ) : ℚ)
      push_cast
      simp only [mul_zero, add_zero, ← mul_assoc, Rat.mul_den_eq_num]
    · change z.re * 0 + z.im * ((z.re.den * z.im.den : ℕ) : ℚ) + (b : ℚ) * z.im * 0 =
        ((z.im.num * z.re.den : ℤ) : ℚ)
      push_cast
      simp only [mul_zero, zero_add, add_zero]
      rw [mul_comm (z.re.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]

instance integralQuadraticOrderFractionRing (a b : ℤ) [Fact (b ^ 2 + 4 * a < 0)] :
    IsFractionRing (QuadraticAlgebra ℤ a b) (IntegralQuadraticField a b) :=
  IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, hy, hz⟩ := integralQuadraticOrder_clear_denominators a b z
    refine ⟨x, y, ?_⟩
    apply (eq_div_iff ?_).mpr hz
    exact fun h => hy (integralQuadraticOrderEmbedding_injective a b (by simpa using h))

theorem discriminantOrder_isDedekind (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    IsDedekindDomain (DiscriminantOrder D) := by
  let e := discriminantOrderEquivIntegers D hD
  have hn : IsNoetherianRing (DiscriminantOrder D) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  have hd : Ring.DimensionLEOne (DiscriminantOrder D) :=
    Ring.DimensionLEOne.of_ringEquiv e
  have hi : IsIntegrallyClosed (DiscriminantOrder D) :=
    IsIntegrallyClosed.of_equiv e.symm
  exact { hn, hd, hi with }

theorem properChange_coefficients {D : ℤ} (f g : PrimitivePositiveForm D)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ∀ v, f.eval v = g.eval ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)) :
    f.a = g.a * A 0 0 ^ 2 + g.b * A 0 0 * A 1 0 + g.c * A 1 0 ^ 2 ∧
    f.b = 2 * g.a * A 0 0 * A 0 1 +
      g.b * (A 0 0 * A 1 1 + A 0 1 * A 1 0) + 2 * g.c * A 1 0 * A 1 1 ∧
    f.c = g.a * A 0 1 ^ 2 + g.b * A 0 1 * A 1 1 + g.c * A 1 1 ^ 2 := by
  have h₀ := hA ![1, 0]
  have h₁ := hA ![0, 1]
  have h₂ := hA ![1, 1]
  simp [PrimitivePositiveForm.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₀ h₁ h₂
  refine ⟨h₀, ?_, h₁⟩
  linear_combination h₂ - h₀ - h₁

theorem properChange_ideal_basis_relation {D : ℤ} (f g : PrimitivePositiveForm D)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ∀ v, f.eval v = g.eval ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)) :
    (⟨g.a * A 0 0 + formOrderShift g * A 1 0, A 1 0⟩ : DiscriminantOrder D) *
      ⟨formOrderShift f, 1⟩ =
      (⟨f.a, 0⟩ : DiscriminantOrder D) *
        ⟨g.a * A 0 1 + formOrderShift g * A 1 1, A 1 1⟩ := by
  obtain ⟨ha, hb, _⟩ := properChange_coefficients f g A hA
  have hd := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hd
  have hf := formOrderShift_relation f
  have hg := formOrderShift_relation g
  have hn := formOrderShift_norm_relation g

  have him : g.a * A 0 0 + formOrderShift g * A 1 0 +
      formOrderShift f * A 1 0 + (D % 4) * A 1 0 = f.a * A 1 1 := by
    have hh : 2 * (g.a * A 0 0 + formOrderShift g * A 1 0 +
        formOrderShift f * A 1 0 + (D % 4) * A 1 0 - f.a * A 1 1) = 0 := by
      linear_combination (A 1 0) * hb + (A 1 0) * hg + (A 1 0) * hf -
        (2 * A 1 1) * ha - (2 * g.a * A 0 0 + g.b * A 1 0) * hd
    linarith
  apply QuadraticAlgebra.ext
  · change (g.a * A 0 0 + formOrderShift g * A 1 0) * formOrderShift f +
      ((D - D % 4) / 4) * A 1 0 * 1 =
        f.a * (g.a * A 0 1 + formOrderShift g * A 1 1) +
          ((D - D % 4) / 4) * 0 * A 1 1
    have hh : 2 * ((g.a * A 0 0 + formOrderShift g * A 1 0) * formOrderShift f +
        ((D - D % 4) / 4) * A 1 0 -
          f.a * (g.a * A 0 1 + formOrderShift g * A 1 1)) = 0 := by
      linear_combination
        (g.a * A 0 0) * hf - (g.a * A 0 0) * hg -
        (2 * A 1 0) * hn + (g.a * A 0 0) * hb - (2 * g.a * A 0 1) * ha +
        (g.a * (g.b * A 0 0 + 2 * g.c * A 1 0)) * hd +
        (2 * formOrderShift g) * him
    linarith
  · change (g.a * A 0 0 + formOrderShift g * A 1 0) * 1 +
      A 1 0 * formOrderShift f + (D % 4) * A 1 0 * 1 =
        f.a * A 1 1 + 0 * (g.a * A 0 1 + formOrderShift g * A 1 1) +
          (D % 4) * 0 * A 1 1
    simpa only [mul_one, one_mul, mul_zero, zero_mul, add_zero, add_assoc, mul_comm] using him

/-- Coordinates in the integral ideal basis attached to a form. -/
def formOrderVector {D : ℤ} (f : PrimitivePositiveForm D) (v : Fin 2 → ℤ) :
    DiscriminantOrder D := ⟨f.a * v 0 + formOrderShift f * v 1, v 1⟩

theorem formOrderVector_mem {D : ℤ} (f : PrimitivePositiveForm D) (v : Fin 2 → ℤ) :
    formOrderVector f v ∈ formOrderIdeal f :=
  (formOrderIdeal_lattice f _).mpr ⟨v 0, v 1, rfl⟩

theorem formOrderVector_surjective {D : ℤ} (f : PrimitivePositiveForm D)
    (z : DiscriminantOrder D) (hz : z ∈ formOrderIdeal f) :
    ∃ v : Fin 2 → ℤ, formOrderVector f v = z := by
  obtain ⟨x, y, rfl⟩ := (formOrderIdeal_lattice f z).mp hz
  exact ⟨![x, y], rfl⟩

theorem properChange_ideal_lattice_relation {D : ℤ} (f g : PrimitivePositiveForm D)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ∀ v, f.eval v = g.eval ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v))
    (v : Fin 2 → ℤ) :
    formOrderVector g ![A 0 0, A 1 0] * formOrderVector f v =
      (⟨f.a, 0⟩ : DiscriminantOrder D) *
        formOrderVector g ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v) := by
  have hb := properChange_ideal_basis_relation f g A hA
  have hr := congrArg QuadraticAlgebra.re hb
  have hi := congrArg QuadraticAlgebra.im hb
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] at hr hi
  simp only [formOrderVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  apply QuadraticAlgebra.ext
  · change (g.a * A 0 0 + formOrderShift g * A 1 0) *
        (f.a * v 0 + formOrderShift f * v 1) +
        ((D - D % 4) / 4) * A 1 0 * v 1 =
      f.a * (g.a * (A 0 0 * v 0 + A 0 1 * v 1) +
        formOrderShift g * (A 1 0 * v 0 + A 1 1 * v 1)) +
        ((D - D % 4) / 4) * 0 * (A 1 0 * v 0 + A 1 1 * v 1)
    linear_combination (v 1) * hr
  · change (g.a * A 0 0 + formOrderShift g * A 1 0) * v 1 +
        A 1 0 * (f.a * v 0 + formOrderShift f * v 1) +
        (D % 4) * A 1 0 * v 1 =
      f.a * (A 1 0 * v 0 + A 1 1 * v 1) +
        0 * (g.a * (A 0 0 * v 0 + A 0 1 * v 1) +
          formOrderShift g * (A 1 0 * v 0 + A 1 1 * v 1)) +
        (D % 4) * 0 * (A 1 0 * v 0 + A 1 1 * v 1)
    linear_combination (v 1) * hi

theorem properChange_ideal_multiplier_ne_zero {D : ℤ} (f g : PrimitivePositiveForm D)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ∀ v, f.eval v = g.eval ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)) :
    formOrderVector g ![A 0 0, A 1 0] ≠ 0 := by
  intro hz
  have hn := formOrderIdeal_norm g (A 0 0) (A 1 0)
  have ha := (properChange_coefficients f g A hA).1
  change QuadraticAlgebra.norm (formOrderVector g ![A 0 0, A 1 0]) = _ at hn
  rw [hz] at hn

  have hzero : QuadraticAlgebra.norm (0 : DiscriminantOrder D) = 0 := by
    simp [QuadraticAlgebra.norm_def]
  rw [hzero] at hn
  simp only [PrimitivePositiveForm.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← ha] at hn
  exact (mul_ne_zero g.positive.ne' f.positive.ne') hn.symm

/-- Proper equivalent forms give ideals differing by a nonzero field scalar. -/
theorem properChange_ideal_fractional_eq {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f g : PrimitivePositiveForm D)
    (hfg : properChange f g) :
    ∃ z : DiscriminantField D, z ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D)) z *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)) =
      (formOrderIdeal g : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)) := by
  obtain ⟨A, hA⟩ := hfg
  let j := algebraMap (DiscriminantOrder D) (DiscriminantField D)
  let γ := formOrderVector g ![A 0 0, A 1 0]
  let z := j γ / (f.a : DiscriminantField D)
  have hfa : (f.a : DiscriminantField D) ≠ 0 := Int.cast_ne_zero.mpr f.positive.ne'
  have hγ : j γ ≠ 0 := by
    intro h
    apply properChange_ideal_multiplier_ne_zero f g A hA
    have hi : Function.Injective j :=
      (faithfulSMul_iff_algebraMap_injective (DiscriminantOrder D) (DiscriminantField D)).mp
        inferInstance
    exact hi (by simpa only [map_zero] using h)
  have hz : z ≠ 0 := div_ne_zero hγ hfa
  have hj : j (⟨f.a, 0⟩ : DiscriminantOrder D) = (f.a : DiscriminantField D) := by
    apply QuadraticAlgebra.ext <;> rfl
  have hv : ∀ v : Fin 2 → ℤ,
      z * j (formOrderVector f v) =
        j (formOrderVector g ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v)) := by
    intro v
    have hh := congrArg j (properChange_ideal_lattice_relation f g A hA v)
    rw [map_mul, map_mul, hj] at hh
    calc
      z * j (formOrderVector f v) =
          (j γ * j (formOrderVector f v)) / (f.a : DiscriminantField D) := by
        dsimp [z]
        ring
      _ = ((f.a : DiscriminantField D) *
          j (formOrderVector g ((A : Matrix (Fin 2) (Fin 2) ℤ).mulVec v))) /
          (f.a : DiscriminantField D) := by rw [hh]
      _ = _ := mul_div_cancel_left₀ _ hfa
  refine ⟨z, hz, ?_⟩
  symm
  apply FractionalIdeal.eq_spanSingleton_mul.mpr
  constructor
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    obtain ⟨v, rfl⟩ := formOrderVector_surjective g x hx
    let u := ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ).mulVec v
    refine ⟨j (formOrderVector f u),
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem f u, rfl⟩, ?_⟩
    rw [hv]
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    obtain ⟨v, rfl⟩ := formOrderVector_surjective f x hx
    rw [hv]
    exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem g _, rfl⟩

/-- The ideal class associated to a form in a fundamental discriminant order. -/
def formIdealClass {D : ℤ} [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) (f : PrimitivePositiveForm D) :
    ClassGroup (DiscriminantOrder D) :=
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  ClassGroup.mk0 ⟨formOrderIdeal f, by
    simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using
      formOrderIdeal_ne_bot f⟩

theorem formIdealClass_eq_of_properChange {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (f g : PrimitivePositiveForm D) (hfg : properChange f g) :
    formIdealClass hD f = formIdealClass hD g := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  obtain ⟨z, hz, heq⟩ := properChange_ideal_fractional_eq f g hfg
  exact (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (DiscriminantField D)).mpr
    ⟨z, hz, heq⟩

/-- Proper form classes map to Mathlib's ideal class group. -/
def formClassToIdealClass {D : ℤ} [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) : FormClass D → ClassGroup (DiscriminantOrder D) :=
  Quotient.lift (formIdealClass hD) fun f g hfg =>
    formIdealClass_eq_of_properChange hD f g ((properChange_eqvGen_iff f g).mp hfg)

/-- Transport to the actual ring-of-integers class group used in the analytic formula. -/
def formClassToNumberFieldIdealClass {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    FormClass D → ClassGroup (NumberField.RingOfIntegers (DiscriminantField D)) :=
  (ClassGroup.mulEquiv (discriminantOrderEquivIntegers D hD)) ∘ formClassToIdealClass hD

theorem formOrderVector_injective {D : ℤ} (f : PrimitivePositiveForm D) :
    Function.Injective (formOrderVector f) := by
  intro v w h
  have hi := congrArg QuadraticAlgebra.im h
  have hr := congrArg QuadraticAlgebra.re h
  change v 1 = w 1 at hi
  change f.a * v 0 + formOrderShift f * v 1 =
    f.a * w 0 + formOrderShift f * w 1 at hr
  rw [hi] at hr
  have h₀ : v 0 = w 0 := mul_left_cancel₀ f.positive.ne' (add_right_cancel hr)
  funext i
  fin_cases i
  · exact h₀
  · exact hi

theorem discriminantField_norm_identity {D : ℤ} [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (z : DiscriminantField D) :
    4 * QuadraticAlgebra.norm z =
      (2 * z.re + ((D % 4 : ℤ) : ℚ) * z.im) ^ 2 - (D : ℚ) * z.im ^ 2 := by
  have hd : ((D % 4 : ℤ) : ℚ) ^ 2 +
      4 * (((D - D % 4) / 4 : ℤ) : ℚ) = (D : ℚ) := by
    exact_mod_cast discriminantOrder_discr D (Fact.out)
  rw [QuadraticAlgebra.norm_def]
  linear_combination -(z.im ^ 2) * hd

theorem discriminantField_norm_pos {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (z : DiscriminantField D) (hz : z ≠ 0) :
    0 < QuadraticAlgebra.norm z := by
  have hD : (D : ℚ) < 0 := by exact_mod_cast (Fact.out : D < 0)
  have hn := discriminantField_norm_identity z
  by_cases hi : z.im = 0
  · have hr : z.re ≠ 0 := by
      intro hr
      apply hz
      apply QuadraticAlgebra.ext <;> assumption
    rw [hi] at hn
    nlinarith [sq_pos_of_ne_zero hr]
  · have hp := sq_pos_of_ne_zero hi
    have hs := sq_nonneg (2 * z.re + ((D % 4 : ℤ) : ℚ) * z.im)
    nlinarith [mul_neg_of_neg_of_pos hD hp]

theorem formOrderVector_eq_basis {D : ℤ} (f : PrimitivePositiveForm D)
    (v : Fin 2 → ℤ) :
    formOrderVector f v = (v 0 : DiscriminantOrder D) * formOrderVector f ![1, 0] +
      (v 1 : DiscriminantOrder D) * formOrderVector f ![0, 1] := by
  apply QuadraticAlgebra.ext <;>
    simp [formOrderVector, mul_comm]

theorem formOrderVector_mulVec_columns {D : ℤ} (f : PrimitivePositiveForm D)
    (u w v : Fin 2 → ℤ) :
    formOrderVector f ((!![u 0, w 0; u 1, w 1] : Matrix (Fin 2) (Fin 2) ℤ).mulVec v) =
      (v 0 : DiscriminantOrder D) * formOrderVector f u +
      (v 1 : DiscriminantOrder D) * formOrderVector f w := by
  apply QuadraticAlgebra.ext <;>
    simp [formOrderVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem fractional_form_ideals_change_matrix {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f g : PrimitivePositiveForm D)
    (z : DiscriminantField D)
    (hfg : FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D)) z *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) =
      (formOrderIdeal g : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D))) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (∀ v, z * algebraMap (DiscriminantOrder D) (DiscriminantField D) (formOrderVector f v) =
        algebraMap (DiscriminantOrder D) (DiscriminantField D) (formOrderVector g (A.mulVec v))) ∧
      Function.Surjective A.mulVec := by
  let j := algebraMap (DiscriminantOrder D) (DiscriminantField D)
  have hm : ∀ v : Fin 2 → ℤ,
      ∃ w : Fin 2 → ℤ, z * j (formOrderVector f v) = j (formOrderVector g w) := by
    intro v
    have hv : z * j (formOrderVector f v) ∈
        (formOrderIdeal g : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) := by
      rw [← hfg]
      exact FractionalIdeal.mem_singleton_mul.mpr
        ⟨j (formOrderVector f v),
          (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem f v, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxeq⟩ := (FractionalIdeal.mem_coeIdeal _).mp hv
    obtain ⟨w, hw⟩ := formOrderVector_surjective g x hx
    exact ⟨w, by rw [hw]; exact hxeq.symm⟩
  obtain ⟨u, hu⟩ := hm ![1, 0]
  obtain ⟨w, hw⟩ := hm ![0, 1]
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![u 0, w 0; u 1, w 1]
  have hA : ∀ v : Fin 2 → ℤ, z * j (formOrderVector f v) =
      j (formOrderVector g (A.mulVec v)) := by
    intro v
    rw [formOrderVector_eq_basis, map_add, map_mul, map_mul]
    calc
      _ = j (v 0) * (z * j (formOrderVector f ![1, 0])) +
          j (v 1) * (z * j (formOrderVector f ![0, 1])) := by ring
      _ = j (v 0) * j (formOrderVector g u) + j (v 1) * j (formOrderVector g w) := by
        rw [hu, hw]
      _ = j (formOrderVector g (A.mulVec v)) := by
        rw [show A = !![u 0, w 0; u 1, w 1] from rfl,
          formOrderVector_mulVec_columns, map_add, map_mul, map_mul]
  refine ⟨A, hA, ?_⟩
  intro v
  have hv : j (formOrderVector g v) ∈
      (formOrderIdeal g : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D)) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem g v, rfl⟩
  rw [← hfg] at hv
  obtain ⟨x, hx, heq⟩ := FractionalIdeal.mem_singleton_mul.mp hv
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
  obtain ⟨v', rfl⟩ := formOrderVector_surjective f y hy
  refine ⟨v', formOrderVector_injective g ?_⟩
  have hi : Function.Injective j :=
    (faithfulSMul_iff_algebraMap_injective (DiscriminantOrder D) (DiscriminantField D)).mp
      inferInstance
  apply hi
  rw [← hA]
  exact heq.symm

theorem discriminantOrder_algebraMap_re (D : ℤ) (z : DiscriminantOrder D) :
    (algebraMap (DiscriminantOrder D) (DiscriminantField D) z).re = (z.re : ℚ) := rfl

theorem discriminantOrder_algebraMap_im (D : ℤ) (z : DiscriminantOrder D) :
    (algebraMap (DiscriminantOrder D) (DiscriminantField D) z).im = (z.im : ℚ) := rfl

theorem matrix_det_isUnit_of_mulVec_surjective (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : Function.Surjective A.mulVec) : IsUnit A.det := by
  obtain ⟨u, hu⟩ := hA ![1, 0]
  obtain ⟨w, hw⟩ := hA ![0, 1]
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![u 0, w 0; u 1, w 1]
  have hAB : A * B = 1 := by
    have h₀ := congrFun hu 0
    have h₁ := congrFun hu 1
    have h₂ := congrFun hw 0
    have h₃ := congrFun hw 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h₀ h₁ h₂ h₃
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, B, h₀, h₁, h₂, h₃]
  have hd : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  exact ⟨⟨A.det, B.det, hd, by simpa only [mul_comm] using hd⟩, rfl⟩

theorem fractional_form_change_det_norm {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f g : PrimitivePositiveForm D)
    (z : DiscriminantField D) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ v, z * algebraMap (DiscriminantOrder D) (DiscriminantField D)
      (formOrderVector f v) =
        algebraMap (DiscriminantOrder D) (DiscriminantField D)
          (formOrderVector g (A.mulVec v))) :
    (f.a : ℚ) * QuadraticAlgebra.norm z = (g.a : ℚ) * (A.det : ℚ) := by
  have h₀ := hA ![1, 0]
  have h₁ := hA ![0, 1]
  have hr₀ := congrArg QuadraticAlgebra.re h₀
  have hi₀ := congrArg QuadraticAlgebra.im h₀
  have hr₁ := congrArg QuadraticAlgebra.re h₁
  have hi₁ := congrArg QuadraticAlgebra.im h₁
  simp [formOrderVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    discriminantOrder_algebraMap_re, discriminantOrder_algebraMap_im] at hr₀ hi₀ hr₁ hi₁
  rw [QuadraticAlgebra.norm_def, Matrix.det_fin_two]
  push_cast

  linear_combination
    (z.re + ((D % 4 : ℤ) : ℚ) * z.im + (formOrderShift f : ℚ) * z.im) * hr₀ -
    ((((D - D % 4) / 4 : ℤ) : ℚ) * z.im + (formOrderShift f : ℚ) * z.re) * hi₀ -
    (A 1 0 : ℚ) * hr₁ +
    ((g.a : ℚ) * A 0 0 + (formOrderShift g : ℚ) * A 1 0) * hi₁

theorem discriminantOrder_algebraMap_norm (D : ℤ) (z : DiscriminantOrder D) :
    QuadraticAlgebra.norm (algebraMap (DiscriminantOrder D) (DiscriminantField D) z) =
      ((QuadraticAlgebra.norm z : ℤ) : ℚ) := by
  rw [QuadraticAlgebra.norm_def, discriminantOrder_algebraMap_re,
    discriminantOrder_algebraMap_im, QuadraticAlgebra.norm_def]
  push_cast
  rfl

theorem formOrderVector_norm {D : ℤ} (f : PrimitivePositiveForm D) (v : Fin 2 → ℤ) :
    QuadraticAlgebra.norm (formOrderVector f v) = f.a * f.eval v := by
  simpa only [formOrderVector, PrimitivePositiveForm.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one] using formOrderIdeal_norm f (v 0) (v 1)

/-- Equality of the scalar ideal classes recovers a proper change of variables. -/
theorem properChange_of_ideal_fractional_eq {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f g : PrimitivePositiveForm D)
    (z : DiscriminantField D) (hz : z ≠ 0)
    (hfg : FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D)) z *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) =
      (formOrderIdeal g : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D))) : properChange f g := by
  obtain ⟨A, hA, hsurj⟩ := fractional_form_ideals_change_matrix f g z hfg
  have hu := matrix_det_isUnit_of_mulVec_surjective A hsurj
  have hn := fractional_form_change_det_norm f g z A hA
  have hfa : (0 : ℚ) < f.a := by exact_mod_cast f.positive
  have hga : (0 : ℚ) < g.a := by exact_mod_cast g.positive
  have hp := discriminantField_norm_pos z hz
  have hdetpos : 0 < A.det := by
    have hpos : (0 : ℚ) < A.det := by nlinarith [mul_pos hfa hp]
    exact_mod_cast hpos
  have hdet : A.det = 1 := (Int.isUnit_iff.mp hu).resolve_right (by omega)
  have hnorm : (f.a : ℚ) * QuadraticAlgebra.norm z = (g.a : ℚ) := by
    simpa only [hdet, Int.cast_one, mul_one] using hn
  refine ⟨⟨A, hdet⟩, ?_⟩
  intro v
  have hv := congrArg QuadraticAlgebra.norm (hA v)
  rw [map_mul, discriminantOrder_algebraMap_norm, discriminantOrder_algebraMap_norm,
    formOrderVector_norm, formOrderVector_norm] at hv
  push_cast at hv
  have heq : (f.eval v : ℚ) =
      (g.eval (A.mulVec v) : ℚ) := by
    apply mul_left_cancel₀ (ne_of_gt hga)
    calc
      (g.a : ℚ) * (f.eval v : ℚ) =
          ((f.a : ℚ) * QuadraticAlgebra.norm z) * (f.eval v : ℚ) := by rw [hnorm]
      _ = (g.a : ℚ) * (g.eval (A.mulVec v) : ℚ) := by
        linear_combination hv
  exact_mod_cast heq

theorem formIdealClass_eq_iff_properChange {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (f g : PrimitivePositiveForm D) :
    formIdealClass hD f = formIdealClass hD g ↔ properChange f g := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  constructor
  · intro h
    obtain ⟨z, hz, heq⟩ :=
      (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (DiscriminantField D)).mp h
    exact properChange_of_ideal_fractional_eq f g z hz heq
  · exact formIdealClass_eq_of_properChange hD f g

theorem formClassToIdealClass_injective {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Injective (formClassToIdealClass hD) := by
  intro x y h
  induction x using Quotient.inductionOn with | _ f =>
    induction y using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      exact Relation.EqvGen.rel f g ((formIdealClass_eq_iff_properChange hD f g).mp h)

theorem formClassToNumberFieldIdealClass_injective {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Injective (formClassToNumberFieldIdealClass hD) :=
  (ClassGroup.mulEquiv (discriminantOrderEquivIntegers D hD)).injective.comp
    (formClassToIdealClass_injective hD)

theorem orderClassNumber_le_fieldClassNumber {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    orderClassNumber D ≤ NumberField.classNumber (DiscriminantField D) := by
  simpa only [orderClassNumber, NumberField.classNumber, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective (formClassToNumberFieldIdealClass hD)
      (formClassToNumberFieldIdealClass_injective hD)

theorem intIdeal_positive_generator (I : Ideal ℤ) (hI : I ≠ ⊥) :
    ∃ m : ℤ, 0 < m ∧ ∀ x : ℤ, x ∈ I ↔ m ∣ x := by
  let m : ℤ := (Submodule.IsPrincipal.generator I).natAbs
  have hg : Submodule.IsPrincipal.generator I ≠ 0 :=
    mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hI
  refine ⟨m, ?_, ?_⟩
  · dsimp only [m]
    exact_mod_cast Int.natAbs_pos.mpr hg
  · intro x
    dsimp only [m]
    rw [Int.natAbs_dvd, ← Ideal.mem_span_singleton, Ideal.span_singleton_generator]

/-- Projection of an integral ideal to its second lattice coordinate. -/
def discriminantIdealImaginary (D : ℤ) (I : Ideal (DiscriminantOrder D)) : Ideal ℤ where
  carrier := {y | ∃ x : ℤ, (⟨x, y⟩ : DiscriminantOrder D) ∈ I}
  zero_mem' := ⟨0, I.zero_mem⟩
  add_mem' := by
    rintro y z ⟨x, hx⟩ ⟨w, hw⟩
    exact ⟨x + w, I.add_mem hx hw⟩
  smul_mem' := by
    rintro r y ⟨x, hx⟩
    refine ⟨r * x, ?_⟩
    have hr := I.mul_mem_left (r : DiscriminantOrder D) hx
    convert hr using 1
    simp

theorem discriminantIdeal_constant_part_ne_bot {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥) :
    Ideal.comap (algebraMap ℤ (DiscriminantOrder D)) I ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hi : Function.Injective (algebraMap (DiscriminantOrder D) (DiscriminantField D)) :=
    (faithfulSMul_iff_algebraMap_injective (DiscriminantOrder D) (DiscriminantField D)).mp
      inferInstance
  have hm : algebraMap (DiscriminantOrder D) (DiscriminantField D) x ≠ 0 :=
    fun h => hx0 (hi (by simpa only [map_zero] using h))
  have hn : 0 < QuadraticAlgebra.norm x := by
    have hp := discriminantField_norm_pos _ hm
    rw [discriminantOrder_algebraMap_norm] at hp
    exact_mod_cast hp
  have hmem : QuadraticAlgebra.norm x ∈
      Ideal.comap (algebraMap ℤ (DiscriminantOrder D)) I := by
    change algebraMap ℤ (DiscriminantOrder D) (QuadraticAlgebra.norm x) ∈ I
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact I.mul_mem_right (star x) hx
  exact (Submodule.ne_bot_iff _).mpr ⟨_, hmem, hn.ne'⟩

/-- A nonzero quadratic-order ideal has an integral triangular lattice basis. -/
theorem discriminantIdeal_triangular_basis {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥) :
    ∃ m g r : ℤ, 0 < m ∧ 0 < g ∧ g ∣ m ∧ g ∣ r ∧
      ∀ z : DiscriminantOrder D, z ∈ I ↔
        ∃ x y : ℤ, z = ⟨m * x + r * y, g * y⟩ := by
  let P := Ideal.comap (algebraMap ℤ (DiscriminantOrder D)) I
  obtain ⟨m, hm, hP⟩ := intIdeal_positive_generator P
    (discriminantIdeal_constant_part_ne_bot I hI)
  have hmc : (⟨m, 0⟩ : DiscriminantOrder D) ∈ I := (hP m).mpr dvd_rfl
  have hmi : (⟨0, m⟩ : DiscriminantOrder D) ∈ I := by
    have h := I.mul_mem_left (⟨0, 1⟩ : DiscriminantOrder D) hmc
    simpa using h
  have hQ : discriminantIdealImaginary D I ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨m, ⟨0, hmi⟩, hm.ne'⟩
  obtain ⟨g, hg, hG⟩ := intIdeal_positive_generator (discriminantIdealImaginary D I) hQ
  obtain ⟨r, hr⟩ := (hG g).mpr dvd_rfl
  have hgm : g ∣ m := (hG m).mp ⟨0, hmi⟩
  have hgr : g ∣ r := by
    have h := I.mul_mem_left (⟨0, 1⟩ : DiscriminantOrder D) hr
    have hi : (⟨((D - D % 4) / 4) * g, r + (D % 4) * g⟩ : DiscriminantOrder D) ∈ I := by
      simpa using h
    have h' : g ∣ r + (D % 4) * g := (hG _).mp ⟨_, hi⟩
    simpa only [add_sub_cancel_right] using
      dvd_sub h' (dvd_mul_left g (D % 4))
  refine ⟨m, g, r, hm, hg, hgm, hgr, ?_⟩
  intro z
  constructor
  · intro hz
    have hy : g ∣ z.im := (hG _).mp ⟨z.re, hz⟩
    obtain ⟨y, hy⟩ := hy
    have hc : (⟨z.re - r * y, 0⟩ : DiscriminantOrder D) ∈ I := by
      have h := I.sub_mem hz (I.mul_mem_left (y : DiscriminantOrder D) hr)
      convert h using 1
      apply QuadraticAlgebra.ext <;> simp [hy, mul_comm]
    have hx : m ∣ z.re - r * y := (hP _).mp hc
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, y, ?_⟩
    apply QuadraticAlgebra.ext
    · change z.re = m * x + r * y
      linarith
    · exact hy
  · rintro ⟨x, y, rfl⟩
    have h := I.add_mem (I.mul_mem_left (x : DiscriminantOrder D) hmc)
      (I.mul_mem_left (y : DiscriminantOrder D) hr)
    convert h using 1
    apply QuadraticAlgebra.ext <;> simp [mul_comm]

/-- Dividing out the content leaves the standard ideal lattice [a, h + ω]. -/
theorem discriminantIdeal_normalized_basis {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥) :
    ∃ g a h c : ℤ, 0 < g ∧ 0 < a ∧
      h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c ∧
      ∀ z : DiscriminantOrder D, z ∈ I ↔
        ∃ x y : ℤ, z = ⟨g * (a * x + h * y), g * y⟩ := by
  obtain ⟨m, g, r, hm, hg, hgm, hgr, hL⟩ := discriminantIdeal_triangular_basis I hI
  obtain ⟨a, ha⟩ := hgm
  obtain ⟨h, hh⟩ := hgr
  have ha0 : 0 < a := by nlinarith
  have hβ : (⟨r, g⟩ : DiscriminantOrder D) ∈ I :=
    (hL _).mpr ⟨0, 1, by simp⟩
  have hωβ : (⟨((D - D % 4) / 4) * g, r + (D % 4) * g⟩ : DiscriminantOrder D) ∈ I := by
    simpa using I.mul_mem_left (⟨0, 1⟩ : DiscriminantOrder D) hβ
  obtain ⟨x, y, hxy⟩ := (hL _).mp hωβ
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  change r + (D % 4) * g = g * y at him
  have hy : y = h + D % 4 := by
    apply mul_left_cancel₀ hg.ne'
    rw [← him, hh]
    ring
  change ((D - D % 4) / 4) * g = m * x + r * y at hre
  have hn : (D - D % 4) / 4 = a * x + h * (h + D % 4) := by
    apply mul_left_cancel₀ hg.ne'
    rw [ha, hh, hy] at hre
    linear_combination hre
  refine ⟨g, a, h, -x, hg, ha0, ?_, ?_⟩
  · linear_combination -hn
  · intro z
    simpa only [ha, hh, mul_add, mul_assoc] using hL z

/-- Integral forms of fundamental discriminant are automatically primitive. -/
theorem primitive_of_fundamental_discriminant (D a b c : ℤ)
    (hD : Int.IsFundamentalDiscr D) (ha : 0 < a) (hd : b ^ 2 - 4 * a * c = D) :
    Int.gcd a (Int.gcd b c : ℤ) = 1 := by
  let g := Int.gcd a (Int.gcd b c : ℤ)
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_left _ ha.ne'
  have hga : (g : ℤ) ∣ a := Int.gcd_dvd_left _ _
  have hgb : (g : ℤ) ∣ b := (Int.gcd_dvd_right a (Int.gcd b c : ℤ)).trans
    (Int.gcd_dvd_left b c)
  have hgc : (g : ℤ) ∣ c := (Int.gcd_dvd_right a (Int.gcd b c : ℤ)).trans
    (Int.gcd_dvd_right b c)
  obtain ⟨a', ha'⟩ := hga
  obtain ⟨b', hb'⟩ := hgb
  obtain ⟨c', hc'⟩ := hgc
  have he : D = (g : ℤ) ^ 2 * (b' ^ 2 - 4 * a' * c') := by
    rw [ha', hb', hc'] at hd
    linear_combination -hd
  have heQ : (D : ℚ) = (g : ℚ) ^ 2 * ((b' : ℚ) ^ 2 - 4 * (a' : ℚ) * c') := by
    exact_mod_cast he
  have hy : (D : ℚ) * (g : ℚ)⁻¹ ^ 2 = (b' : ℚ) ^ 2 - 4 * (a' * c' : ℤ) := by
    rw [heQ]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hg.ne']
  have hint := fundamental_discriminant_rational_factor_integral D b' (a' * c') hD
    (g : ℚ)⁻¹ hy
  rw [Rat.inv_natCast_den_of_pos hg] at hint
  exact hint

/-- The primitive positive form obtained by normalizing an ideal basis. -/
def formOfNormalizedIdeal (D a h c : ℤ) (hD : Int.IsFundamentalDiscr D) (ha : 0 < a)
    (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hn : h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c) :
    PrimitivePositiveForm D where
  a := a
  b := 2 * h + D % 4
  c := c
  positive := ha
  discriminant := by
    have hd := discriminantOrder_discr D hm
    nlinarith [hn]
  primitive := primitive_of_fundamental_discriminant D a (2 * h + D % 4) c hD ha (by
    have hd := discriminantOrder_discr D hm
    nlinarith [hn])

theorem formOfNormalizedIdeal_shift (D a h c : ℤ) (hD : Int.IsFundamentalDiscr D)
    (ha : 0 < a) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hn : h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c) :
    formOrderShift (formOfNormalizedIdeal D a h c hD ha hm hn) = h := by
  simp [formOrderShift, formOfNormalizedIdeal]

/-- Every nonzero maximal-order ideal is a scalar multiple of a form ideal. -/
theorem discriminantIdeal_eq_scaled_form {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥) :
    ∃ f : PrimitivePositiveForm D, ∃ g : ℤ, 0 < g ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D))
        (g : DiscriminantField D) *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) =
      (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D)) := by
  obtain ⟨g, a, h, c, hg, ha, hn, hL⟩ := discriminantIdeal_normalized_basis I hI
  let f := formOfNormalizedIdeal D a h c hD ha Fact.out hn
  let j := algebraMap (DiscriminantOrder D) (DiscriminantField D)
  have hfa : f.a = a := rfl
  have hfh : formOrderShift f = h :=
    formOfNormalizedIdeal_shift D a h c hD ha Fact.out hn
  have hv : ∀ v : Fin 2 → ℤ,
      (g : DiscriminantOrder D) * formOrderVector f v =
        ⟨g * (a * v 0 + h * v 1), g * v 1⟩ := by
    intro v
    apply QuadraticAlgebra.ext <;> simp [formOrderVector, hfa, hfh]
  refine ⟨f, g, hg, ?_⟩
  symm
  apply FractionalIdeal.eq_spanSingleton_mul.mpr
  constructor
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨u, v, rfl⟩ := (hL x).mp hx
    refine ⟨j (formOrderVector f ![u, v]),
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem f _, rfl⟩, ?_⟩
    rw [← map_intCast j g, ← map_mul, hv]
    rfl
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨v, rfl⟩ := formOrderVector_surjective f x hx
    refine (FractionalIdeal.mem_coeIdeal _).mpr
      ⟨(g : DiscriminantOrder D) * formOrderVector f v,
        (hL _).mpr ⟨v 0, v 1, hv v⟩, ?_⟩
    rw [map_mul, map_intCast]

theorem formClassToIdealClass_surjective {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Surjective (formClassToIdealClass hD) := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  intro C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  have hI : (I : Ideal (DiscriminantOrder D)) ≠ ⊥ := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot] using I.property
  obtain ⟨f, g, hg, heq⟩ := discriminantIdeal_eq_scaled_form hD I hI
  refine ⟨Quotient.mk _ f, ?_⟩
  exact (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (DiscriminantField D)).mpr
    ⟨(g : DiscriminantField D), Int.cast_ne_zero.mpr hg.ne', heq⟩

/-- The classical form/ideal-class correspondence for negative fundamental discriminants. -/
def formClassEquivIdealClass {D : ℤ} [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) : FormClass D ≃ ClassGroup (DiscriminantOrder D) :=
  Equiv.ofBijective (formClassToIdealClass hD)
    ⟨formClassToIdealClass_injective hD, formClassToIdealClass_surjective hD⟩

def formClassEquivNumberFieldIdealClass {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    FormClass D ≃ ClassGroup (NumberField.RingOfIntegers (DiscriminantField D)) :=
  (formClassEquivIdealClass hD).trans
    (ClassGroup.mulEquiv (discriminantOrderEquivIntegers D hD)).toEquiv

/-- The form class number agrees with the class number in Mathlib's analytic theorem. -/
theorem orderClassNumber_eq_fieldClassNumber {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    orderClassNumber D = NumberField.classNumber (DiscriminantField D) := by
  rw [orderClassNumber, Nat.card_congr (formClassEquivNumberFieldIdealClass hD),
    Nat.card_eq_fintype_card]
  rfl

/-- Mathlib's analytic class-number residue expressed using the independently defined
proper form class number and the actual order unit count. -/
theorem discriminantField_class_number_limit_forms (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Filter.Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (DiscriminantField D) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (((2 * Real.pi * (orderClassNumber D : ℝ) /
        (orderUnitCount D * Real.sqrt |(D : ℝ)|)) : ℝ) : ℂ)) := by
  have h := discriminantField_class_number_limit_explicit D hD
  rw [← orderClassNumber_eq_fieldClassNumber hD] at h
  exact h

theorem integralQuadraticOrder_norm (a b : ℤ) (z : QuadraticAlgebra ℤ a b) :
    Algebra.norm ℤ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

theorem formOrderIdeal_absNorm {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (f : PrimitivePositiveForm D) :
    let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
    Ideal.absNorm (formOrderIdeal f) = f.a.natAbs := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  change Ideal.absNorm (formOrderIdeal f) = f.a.natAbs
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact formOrderIdeal_quotient_card f

theorem discriminantOrder_principal_absNorm {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) (g : ℤ) :
    let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
    Ideal.absNorm (Ideal.span {(g : DiscriminantOrder D)}) = g.natAbs ^ 2 := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  change Ideal.absNorm (Ideal.span {(g : DiscriminantOrder D)}) = g.natAbs ^ 2
  rw [Ideal.absNorm_span_singleton]
  change (Algebra.norm ℤ (g : DiscriminantOrder D)).natAbs = g.natAbs ^ 2
  rw [integralQuadraticOrder_norm ((D - D % 4) / 4) (D % 4) (g : DiscriminantOrder D),
    QuadraticAlgebra.norm_intCast, Int.natAbs_pow, Int.cast_id]

theorem discriminantIdeal_absNorm_of_scaled_form {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (I : Ideal (DiscriminantOrder D)) (f : PrimitivePositiveForm D) (g : ℤ)
    (heq : FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D))
        (g : DiscriminantField D) *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) =
      (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D))) :
    let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
    Ideal.absNorm I = g.natAbs ^ 2 * f.a.natAbs := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  change Ideal.absNorm I = g.natAbs ^ 2 * f.a.natAbs
  have hmul : Ideal.span {(g : DiscriminantOrder D)} * formOrderIdeal f = I := by
    apply (FractionalIdeal.coeIdeal_inj (K := DiscriminantField D)).mp
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, map_intCast]
    exact heq
  rw [← hmul, map_mul, discriminantOrder_principal_absNorm hD, formOrderIdeal_absNorm hD]

theorem ideal_absNorm_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Infinite R] [Infinite S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.absNorm (Ideal.map e I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map e I) e rfl).toEquiv.symm

/-- The normalized triangular lattice underlying a quadratic-order ideal. -/
def normalizedOrderLattice (D g a h : ℤ) (z : DiscriminantOrder D) : Prop :=
  ∃ x y : ℤ, z = ⟨g * (a * x + h * y), g * y⟩

theorem normalizedOrderLattice_imaginary (D g a h y : ℤ) :
    (∃ x : ℤ, normalizedOrderLattice D g a h ⟨x, y⟩) ↔ g ∣ y := by
  constructor
  · rintro ⟨x, u, v, huv⟩
    exact ⟨v, congrArg QuadraticAlgebra.im huv⟩
  · rintro ⟨v, rfl⟩
    exact ⟨g * (h * v), 0, v, by ext <;> simp⟩

theorem normalizedOrderLattice_constant (D g a h x : ℤ) (hg : g ≠ 0) :
    normalizedOrderLattice D g a h ⟨x, 0⟩ ↔ g * a ∣ x := by
  constructor
  · rintro ⟨u, v, huv⟩
    have hi := congrArg QuadraticAlgebra.im huv
    change 0 = g * v at hi
    have hv : v = 0 := (mul_eq_zero.mp hi.symm).resolve_left hg
    refine ⟨u, ?_⟩
    have hr := congrArg QuadraticAlgebra.re huv
    simpa only [hv, mul_zero, add_zero, mul_assoc] using hr
  · rintro ⟨u, rfl⟩
    exact ⟨u, 0, by ext <;> simp [mul_assoc]⟩

/-- The content and coefficient are unique; shifts are unique modulo the coefficient. -/
theorem normalizedOrderLattice_parameters_unique (D g a h g' a' h' : ℤ)
    (hg : 0 < g) (ha : 0 < a) (hg' : 0 < g') (ha' : 0 < a')
    (hL : ∀ z : DiscriminantOrder D,
      normalizedOrderLattice D g a h z ↔ normalizedOrderLattice D g' a' h' z) :
    g = g' ∧ a = a' ∧ a ∣ h - h' := by
  have him : ∀ y : ℤ, g ∣ y ↔ g' ∣ y := by
    intro y
    rw [← normalizedOrderLattice_imaginary D g a h,
      ← normalizedOrderLattice_imaginary D g' a' h']
    exact exists_congr fun x => hL ⟨x, y⟩
  have hgeq : g = g' := Int.dvd_antisymm hg.le hg'.le ((him g').mpr dvd_rfl)
    ((him g).mp dvd_rfl)
  subst g'
  have hc : ∀ x : ℤ, g * a ∣ x ↔ g * a' ∣ x := by
    intro x
    rw [← normalizedOrderLattice_constant D g a h x hg.ne',
      ← normalizedOrderLattice_constant D g a' h' x hg.ne']
    exact hL ⟨x, 0⟩
  have hmeq : g * a = g * a' :=
    Int.dvd_antisymm (mul_pos hg ha).le (mul_pos hg ha').le
      ((hc (g * a')).mpr dvd_rfl) ((hc (g * a)).mp dvd_rfl)
  have haeq : a = a' := mul_left_cancel₀ hg.ne' hmeq
  subst a'
  have hβ : normalizedOrderLattice D g a h ⟨g * h, g⟩ := ⟨0, 1, by ext <;> simp⟩
  obtain ⟨u, v, huv⟩ := (hL _).mp hβ
  have hi := congrArg QuadraticAlgebra.im huv
  change g = g * v at hi
  have hv : v = 1 := by
    apply mul_left_cancel₀ hg.ne'
    simpa only [mul_one] using hi.symm
  have hr := congrArg QuadraticAlgebra.re huv
  change g * h = g * (a * u + h' * v) at hr
  rw [hv, mul_one] at hr
  have hh : h = a * u + h' := mul_left_cancel₀ hg.ne' hr
  exact ⟨rfl, rfl, ⟨u, by linarith⟩⟩

theorem normalizedOrderLattice_parameters_unique_reduced (D g a h g' a' h' : ℤ)
    (hg : 0 < g) (ha : 0 < a) (hg' : 0 < g') (ha' : 0 < a')
    (hh : 0 ≤ h ∧ h < a) (hh' : 0 ≤ h' ∧ h' < a')
    (hL : ∀ z : DiscriminantOrder D,
      normalizedOrderLattice D g a h z ↔ normalizedOrderLattice D g' a' h' z) :
    g = g' ∧ a = a' ∧ h = h' := by
  obtain ⟨hgeq, haeq, hdiv⟩ :=
    normalizedOrderLattice_parameters_unique D g a h g' a' h' hg ha hg' ha' hL
  subst g'
  subst a'
  have he : h % a = h' % a := (Int.modEq_iff_dvd).mpr (dvd_sub_comm.mp hdiv)
  rw [Int.emod_eq_of_lt hh.1 hh.2, Int.emod_eq_of_lt hh'.1 hh'.2] at he
  exact ⟨rfl, rfl, he⟩

theorem normalizedOrderLattice_shift (D g a h k : ℤ) (z : DiscriminantOrder D) :
    normalizedOrderLattice D g a (h + a * k) z ↔ normalizedOrderLattice D g a h z := by
  constructor
  · rintro ⟨x, y, hz⟩
    refine ⟨x + k * y, y, ?_⟩
    rw [hz]
    apply QuadraticAlgebra.ext <;> ring
  · rintro ⟨x, y, hz⟩
    refine ⟨x - k * y, y, ?_⟩
    rw [hz]
    apply QuadraticAlgebra.ext <;> ring

/-- Canonical integral parameters for a nonzero quadratic-order ideal. -/
structure QuadraticIdealParameter (D : ℤ) where
  content : ℤ
  coefficient : ℤ
  shift : ℤ
  content_pos : 0 < content
  coefficient_pos : 0 < coefficient
  shift_nonneg : 0 ≤ shift
  shift_lt : shift < coefficient
  root : coefficient ∣ shift ^ 2 + (D % 4) * shift - (D - D % 4) / 4

theorem discriminantIdeal_canonical_parameters {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥) :
    ∃ p : QuadraticIdealParameter D, ∀ z : DiscriminantOrder D,
      z ∈ I ↔ normalizedOrderLattice D p.content p.coefficient p.shift z := by
  obtain ⟨g, a, h, c, hg, ha, hn, hL⟩ := discriminantIdeal_normalized_basis I hI
  let r := h % a
  let q := h / a
  have hdiv : h = r + a * q := by
    exact (Int.emod_add_mul_ediv h a).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ ha.ne'
  have hra : r < a := Int.emod_lt_of_pos _ ha
  have hnr : r ^ 2 + (D % 4) * r - (D - D % 4) / 4 =
      a * (c - q * (h + r + D % 4)) := by
    linear_combination hn - (h + r + D % 4) * hdiv
  refine ⟨⟨g, a, r, hg, ha, hr0, hra, ⟨_, hnr⟩⟩, ?_⟩
  intro z
  change z ∈ I ↔ normalizedOrderLattice D g a r z
  rw [hL]
  change normalizedOrderLattice D g a h z ↔ normalizedOrderLattice D g a r z
  rw [hdiv, normalizedOrderLattice_shift]

@[ext]
theorem QuadraticIdealParameter.ext {D : ℤ} {p q : QuadraticIdealParameter D}
    (hg : p.content = q.content) (ha : p.coefficient = q.coefficient)
    (hh : p.shift = q.shift) : p = q := by
  cases p
  cases q
  congr

theorem QuadraticIdealParameter.eq_of_lattice_eq {D : ℤ} (p q : QuadraticIdealParameter D)
    (hL : ∀ z : DiscriminantOrder D,
      normalizedOrderLattice D p.content p.coefficient p.shift z ↔
        normalizedOrderLattice D q.content q.coefficient q.shift z) : p = q := by
  obtain ⟨hg, ha, hh⟩ := normalizedOrderLattice_parameters_unique_reduced D
    p.content p.coefficient p.shift q.content q.coefficient q.shift
    p.content_pos p.coefficient_pos q.content_pos q.coefficient_pos
    ⟨p.shift_nonneg, p.shift_lt⟩ ⟨q.shift_nonneg, q.shift_lt⟩ hL
  exact QuadraticIdealParameter.ext hg ha hh

def QuadraticIdealParameter.form {D : ℤ} [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) (p : QuadraticIdealParameter D) : PrimitivePositiveForm D :=
  formOfNormalizedIdeal D p.coefficient p.shift
    ((p.shift ^ 2 + (D % 4) * p.shift - (D - D % 4) / 4) / p.coefficient)
    hD p.coefficient_pos Fact.out (by
      have hd := Int.ediv_mul_cancel p.root
      linear_combination -hd)

theorem QuadraticIdealParameter.form_shift {D : ℤ} [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) (p : QuadraticIdealParameter D) :
    formOrderShift (p.form hD) = p.shift := by
  exact formOfNormalizedIdeal_shift _ _ _ _ _ _ _ _

def QuadraticIdealParameter.ideal {D : ℤ} [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) (p : QuadraticIdealParameter D) :
    Ideal (DiscriminantOrder D) :=
  Ideal.span {(p.content : DiscriminantOrder D)} * formOrderIdeal (p.form hD)

theorem QuadraticIdealParameter.ideal_ne_bot {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (p : QuadraticIdealParameter D) : p.ideal hD ≠ ⊥ := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  apply mul_ne_zero
  · change Ideal.span {(p.content : DiscriminantOrder D)} ≠ ⊥
    intro h
    have hm : (p.content : DiscriminantOrder D) ∈
        Ideal.span {(p.content : DiscriminantOrder D)} := Ideal.subset_span (by simp)
    rw [h] at hm
    exact (Int.cast_ne_zero.mpr p.content_pos.ne') hm
  · exact formOrderIdeal_ne_bot (p.form hD)

theorem QuadraticIdealParameter.mem_ideal {D : ℤ} [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (hD : Int.IsFundamentalDiscr D) (p : QuadraticIdealParameter D)
    (z : DiscriminantOrder D) :
    z ∈ p.ideal hD ↔ normalizedOrderLattice D p.content p.coefficient p.shift z := by
  have ha : (p.form hD).a = p.coefficient := rfl
  have hv : ∀ v : Fin 2 → ℤ,
      (p.content : DiscriminantOrder D) * formOrderVector (p.form hD) v =
        ⟨p.content * (p.coefficient * v 0 + p.shift * v 1), p.content * v 1⟩ := by
    intro v
    apply QuadraticAlgebra.ext <;>
      simp [formOrderVector, ha, QuadraticIdealParameter.form_shift]
  change z ∈ Ideal.span {(p.content : DiscriminantOrder D)} * formOrderIdeal (p.form hD) ↔ _
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨x, hx, heq⟩
    obtain ⟨v, rfl⟩ := formOrderVector_surjective (p.form hD) x hx
    exact ⟨v 0, v 1, heq.symm.trans (hv v)⟩
  · rintro ⟨u, v, hz⟩
    exact ⟨formOrderVector (p.form hD) ![u, v], formOrderVector_mem _ _,
      (hv ![u, v]).trans hz.symm⟩

theorem QuadraticIdealParameter.ideal_injective {D : ℤ}
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Injective (fun p : QuadraticIdealParameter D => p.ideal hD) := by
  intro p q h
  change p.ideal hD = q.ideal hD at h
  apply QuadraticIdealParameter.eq_of_lattice_eq
  intro z
  rw [← QuadraticIdealParameter.mem_ideal hD, ← QuadraticIdealParameter.mem_ideal hD, h]

abbrev NonzeroDiscriminantIdeal (D : ℤ) := {I : Ideal (DiscriminantOrder D) // I ≠ ⊥}

def QuadraticIdealParameter.toNonzeroIdeal {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (p : QuadraticIdealParameter D) : NonzeroDiscriminantIdeal D :=
  ⟨p.ideal hD, p.ideal_ne_bot hD⟩

theorem QuadraticIdealParameter.toNonzeroIdeal_bijective {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    Function.Bijective (QuadraticIdealParameter.toNonzeroIdeal hD) := by
  constructor
  · intro p q h
    exact QuadraticIdealParameter.ideal_injective hD (congrArg Subtype.val h)
  · intro I
    obtain ⟨p, hp⟩ := discriminantIdeal_canonical_parameters I.val I.property
    refine ⟨p, Subtype.ext ?_⟩
    ext z
    exact ((QuadraticIdealParameter.mem_ideal hD p z).trans (hp z).symm)

def quadraticIdealParameterEquiv {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    QuadraticIdealParameter D ≃ NonzeroDiscriminantIdeal D :=
  Equiv.ofBijective (QuadraticIdealParameter.toNonzeroIdeal hD)
    (QuadraticIdealParameter.toNonzeroIdeal_bijective hD)

theorem QuadraticIdealParameter.ideal_absNorm {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (p : QuadraticIdealParameter D) :
    let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
    Ideal.absNorm (p.ideal hD) = p.content.natAbs ^ 2 * p.coefficient.natAbs := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  change Ideal.absNorm (Ideal.span {(p.content : DiscriminantOrder D)} *
    formOrderIdeal (p.form hD)) = _
  rw [map_mul, discriminantOrder_principal_absNorm hD, formOrderIdeal_absNorm hD]
  rfl

def idealEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Ideal R ≃ Ideal S where
  toFun := Ideal.map e
  invFun := Ideal.comap e
  left_inv _ := Ideal.comap_map_of_bijective e e.bijective
  right_inv I := Ideal.map_comap_of_surjective e e.surjective I

def nonzeroIdealEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    {I : Ideal R // I ≠ ⊥} ≃ {I : Ideal S // I ≠ ⊥} :=
  (idealEquivOfRingEquiv e).subtypeEquiv fun I => by
    exact not_congr (Ideal.map_eq_bot_iff_of_injective e.injective).symm

def quadraticIdealParameterEquivIntegers {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D) :
    QuadraticIdealParameter D ≃
      {I : Ideal (NumberField.RingOfIntegers (DiscriminantField D)) // I ≠ ⊥} :=
  (quadraticIdealParameterEquiv hD).trans
    (nonzeroIdealEquivOfRingEquiv (discriminantOrderEquivIntegers D hD))

theorem quadraticIdealParameterEquivIntegers_absNorm {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (p : QuadraticIdealParameter D) :
    Ideal.absNorm (quadraticIdealParameterEquivIntegers hD p).val =
      p.content.natAbs ^ 2 * p.coefficient.natAbs := by
  let : IsDedekindDomain (DiscriminantOrder D) := discriminantOrder_isDedekind D hD
  change Ideal.absNorm (Ideal.map (discriminantOrderEquivIntegers D hD) (p.ideal hD)) = _
  rw [ideal_absNorm_ringEquiv]
  exact p.ideal_absNorm hD

def nonzeroIdealNormSubtypeEquiv (K : Type*) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    {I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥} // Ideal.absNorm I.val = n} ≃
      {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.val.val, I.property⟩
  invFun I := ⟨⟨I.val, by
    intro h
    have he := I.property
    rw [h, Ideal.absNorm_bot] at he
    exact hn.ne' he.symm⟩, I.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Ideals of norm n are exactly the canonical root parameters with g²a = n. -/
def quadraticIdealNormParameterEquiv {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (n : ℕ) (hn : 0 < n) :
    {p : QuadraticIdealParameter D // p.content.natAbs ^ 2 * p.coefficient.natAbs = n} ≃
      {I : Ideal (NumberField.RingOfIntegers (DiscriminantField D)) // Ideal.absNorm I = n} :=
  ((quadraticIdealParameterEquivIntegers hD).subtypeEquiv fun p => by
      rw [quadraticIdealParameterEquivIntegers_absNorm]).trans
    (nonzeroIdealNormSubtypeEquiv (DiscriminantField D) n hn)

theorem quadraticIdeal_count_eq_parameter_count {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers (DiscriminantField D)) // Ideal.absNorm I = n} =
      Nat.card {p : QuadraticIdealParameter D //
        p.content.natAbs ^ 2 * p.coefficient.natAbs = n} :=
  Nat.card_congr (quadraticIdealNormParameterEquiv hD n hn).symm

/-- Number of roots of the quadratic order polynomial modulo a. -/
def quadraticOrderRootCount (D : ℤ) (a : ℕ) : ℕ :=
  Nat.card {h : ZMod a //
    h ^ 2 + ((D % 4 : ℤ) : ZMod a) * h - (((D - D % 4) / 4 : ℤ) : ZMod a) = 0}

theorem quadraticOrderRootCount_one (D : ℤ) : quadraticOrderRootCount D 1 = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨inferInstance, ?_⟩
  exact ⟨⟨0, Subsingleton.elim _ _⟩⟩

def quadraticOrderRootSquareEquiv (D : ℤ) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    {h : ZMod p //
      h ^ 2 + ((D % 4 : ℤ) : ZMod p) * h - (((D - D % 4) / 4 : ℤ) : ZMod p) = 0} ≃
    {x : ZMod p // x ^ 2 = (D : ZMod p)} := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  have hfour : (4 : ZMod p) ≠ 0 := by
    simpa only [show (2 : ZMod p) ^ 2 = 4 by ring] using pow_ne_zero 2 htwo
  let e := (Equiv.mulLeft₀ (2 : ZMod p) htwo).trans
    (Equiv.addRight ((D % 4 : ℤ) : ZMod p))
  apply e.subtypeEquiv
  intro h
  have hd := congrArg (fun x : ℤ => (x : ZMod p)) (discriminantOrder_discr D hm)
  push_cast at hd
  change h ^ 2 + ((D % 4 : ℤ) : ZMod p) * h -
      (((D - D % 4) / 4 : ℤ) : ZMod p) = 0 ↔
    (2 * h + ((D % 4 : ℤ) : ZMod p)) ^ 2 = (D : ZMod p)
  constructor
  · intro hr
    linear_combination 4 * hr + hd
  · intro hr
    have he : (4 : ZMod p) *
        (h ^ 2 + ((D % 4 : ℤ) : ZMod p) * h -
          (((D - D % 4) / 4 : ℤ) : ZMod p)) = 0 := by
      linear_combination hr - hd
    exact (mul_eq_zero.mp he).resolve_left hfour

theorem quadraticOrderRootCount_prime (D : ℤ) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (quadraticOrderRootCount D p : ℤ) = legendreSym p D + 1 := by
  rw [quadraticOrderRootCount,
    Nat.card_congr (quadraticOrderRootSquareEquiv D p hp2 hm)]
  convert legendreSym.card_sqrts p hp2 D using 1
  congr 1
  exact Nat.card_eq_card_toFinset {x : ZMod p | x ^ 2 = (D : ZMod p)}

/-- Root counts multiply over coprime moduli. -/
def quadraticOrderRootCrtEquiv (D : ℤ) (a b : ℕ) (hab : a.Coprime b) :
    {h : ZMod (a * b) //
      h ^ 2 + ((D % 4 : ℤ) : ZMod (a * b)) * h -
        (((D - D % 4) / 4 : ℤ) : ZMod (a * b)) = 0} ≃
      {h : ZMod a //
        h ^ 2 + ((D % 4 : ℤ) : ZMod a) * h -
          (((D - D % 4) / 4 : ℤ) : ZMod a) = 0} ×
      {h : ZMod b //
        h ^ 2 + ((D % 4 : ℤ) : ZMod b) * h -
          (((D - D % 4) / 4 : ℤ) : ZMod b) = 0} := by
  let e := ZMod.chineseRemainder hab
  refine (e.toEquiv.subtypeEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro h
  rw [← e.map_eq_zero_iff]
  simp only [map_sub, map_add, map_mul, map_intCast, pow_two, Prod.ext_iff,
    Prod.fst_sub, Prod.fst_add, Prod.fst_mul, Prod.fst_intCast,
    Prod.snd_sub, Prod.snd_add, Prod.snd_mul, Prod.snd_intCast,
    Prod.fst_zero, Prod.snd_zero]
  rfl

theorem quadraticOrderRootCount_mul (D : ℤ) (a b : ℕ) (hab : a.Coprime b) :
    quadraticOrderRootCount D (a * b) = quadraticOrderRootCount D a * quadraticOrderRootCount D b := by
  rw [quadraticOrderRootCount, Nat.card_congr (quadraticOrderRootCrtEquiv D a b hab),
    Nat.card_prod]
  rfl

theorem quadraticOrder_polynomial_discriminant (D h : ℤ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (2 * h + D % 4) ^ 2 - D =
      4 * (h ^ 2 + (D % 4) * h - (D - D % 4) / 4) := by
  linear_combination (discriminantOrder_discr D hm)

theorem quadraticOrder_polynomial_no_ramified_odd_square (D h : ℤ) (p : ℕ)
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : (p : ℤ) ∣ D) :
    ¬(p : ℤ) ^ 2 ∣ h ^ 2 + (D % 4) * h - (D - D % 4) / 4 := by
  intro hr
  have he := quadraticOrder_polynomial_discriminant D h hm
  have hb2 : (p : ℤ) ^ 2 ∣ (2 * h + D % 4) ^ 2 - D := by
    rw [he]
    exact dvd_mul_of_dvd_right hr 4
  have hb : (p : ℤ) ∣ (2 * h + D % 4) ^ 2 := by
    have hsub : (p : ℤ) ∣ (2 * h + D % 4) ^ 2 - D :=
      (dvd_pow_self (p : ℤ) (by decide : 2 ≠ 0)).trans hb2
    simpa only [sub_add_cancel] using dvd_add hsub hpd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpb := hpZ.dvd_of_dvd_pow hb
  have hsq : (p : ℤ) ^ 2 ∣ (2 * h + D % 4) ^ 2 := pow_dvd_pow_of_dvd hpb 2
  have hpd2 : (p : ℤ) ^ 2 ∣ D := by
    simpa only [sub_sub_cancel] using dvd_sub hsq hb2
  exact hD.2.2 p hp (hp.odd_of_ne_two hp2) hpd2

theorem quadraticOrder_polynomial_no_ramified_two_square (D h : ℤ)
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0) :
    ¬(4 : ℤ) ∣ h ^ 2 + (D % 4) * h - (D - D % 4) / 4 := by
  intro hr
  have he : D = 4 * (D / 4) := by omega
  have hbad := hD.2.1 (D / 4) he
  rw [hm] at hr
  norm_num at hr
  have hs := Int.sq_emod_four h
  have hmod : (D / 4) % 4 = 0 ∨ (D / 4) % 4 = 1 := by omega
  rcases hmod with hmod | hmod
  · exact hbad.1 (by omega)
  · exact hbad.2 hmod

theorem quadraticOrderRoot_int_representative (D : ℤ) (a : ℕ) [NeZero a]
    (h : ZMod a)
    (hh : h ^ 2 + ((D % 4 : ℤ) : ZMod a) * h -
      (((D - D % 4) / 4 : ℤ) : ZMod a) = 0) :
    (a : ℤ) ∣ (h.val : ℤ) ^ 2 + (D % 4) * h.val - (D - D % 4) / 4 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hh

theorem quadraticOrderRootCount_zero_of_no_integral_roots (D : ℤ) (a : ℕ) [NeZero a]
    (hroot : ∀ x : ℤ, ¬(a : ℤ) ∣ x ^ 2 + (D % 4) * x - (D - D % 4) / 4) :
    quadraticOrderRootCount D a = 0 := by
  let : IsEmpty {h : ZMod a //
      h ^ 2 + ((D % 4 : ℤ) : ZMod a) * h -
        (((D - D % 4) / 4 : ℤ) : ZMod a) = 0} :=
    ⟨fun h => hroot _ (quadraticOrderRoot_int_representative D a h.val h.property)⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem quadraticOrderRootCount_ramified_odd_square (D : ℤ) (p : ℕ) [Fact p.Prime]
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hp2 : p ≠ 2) (hpd : (p : ℤ) ∣ D) :
    quadraticOrderRootCount D (p ^ 2) = 0 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply quadraticOrderRootCount_zero_of_no_integral_roots
  intro h
  simpa only [Nat.cast_pow] using
    quadraticOrder_polynomial_no_ramified_odd_square D h p hD hm Fact.out hp2 hpd

theorem quadraticOrderRootCount_ramified_two_square (D : ℤ)
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0) :
    quadraticOrderRootCount D 4 = 0 := by
  apply quadraticOrderRootCount_zero_of_no_integral_roots
  intro h
  exact quadraticOrder_polynomial_no_ramified_two_square D h hD hm

theorem quadraticOrderRootCount_ramified_odd_power (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hp2 : p ≠ 2) (hpd : (p : ℤ) ∣ D) (hk : 2 ≤ k) :
    quadraticOrderRootCount D (p ^ k) = 0 := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  apply quadraticOrderRootCount_zero_of_no_integral_roots
  intro h hr
  apply quadraticOrder_polynomial_no_ramified_odd_square D h p hD hm Fact.out hp2 hpd
  exact (pow_dvd_pow (p : ℤ) hk).trans (by simpa only [Nat.cast_pow] using hr)

theorem quadraticOrderRootCount_ramified_two_power (D : ℤ) (k : ℕ)
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0) (hk : 2 ≤ k) :
    quadraticOrderRootCount D (2 ^ k) = 0 := by
  let : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  apply quadraticOrderRootCount_zero_of_no_integral_roots
  intro h hr
  apply quadraticOrder_polynomial_no_ramified_two_square D h hD hm
  have hd : (4 : ℤ) ∣ (2 : ℤ) ^ k := by
    simpa only [show (2 : ℤ) ^ 2 = 4 by norm_num] using pow_dvd_pow (2 : ℤ) hk
  exact hd.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hr)

theorem quadraticOrderRootCount_two_even (D : ℤ) (hm : D % 4 = 0) :
    quadraticOrderRootCount D 2 = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : ∀ h : ZMod 2, h ^ 2 = h := ZMod.pow_card
  have hr : ∀ h : ZMod 2,
      h ^ 2 + ((D % 4 : ℤ) : ZMod 2) * h - (((D - D % 4) / 4 : ℤ) : ZMod 2) = 0 ↔
        h = (((D - D % 4) / 4 : ℤ) : ZMod 2) := by
    intro h
    rw [hs, hm]
    simp only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero]
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun x y => Subtype.ext ((hr x.val).mp x.property |>.trans
    ((hr y.val).mp y.property).symm)⟩, ?_⟩
  exact ⟨⟨_, (hr _).mpr rfl⟩⟩

theorem quadraticOrderRootCount_two_odd (D : ℤ) (hm : D % 4 = 1) :
    quadraticOrderRootCount D 2 = if D % 8 = 1 then 2 else 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : ∀ h : ZMod 2, h ^ 2 = h := ZMod.pow_card
  have hz : (((D - D % 4) / 4 : ℤ) : ZMod 2) = 0 ↔ D % 8 = 1 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  rw [hm] at hz
  have hr : ∀ h : ZMod 2,
      h ^ 2 + ((D % 4 : ℤ) : ZMod 2) * h -
        (((D - D % 4) / 4 : ℤ) : ZMod 2) = 0 ↔ D % 8 = 1 := by
    intro h
    rw [hs, hm, Int.cast_one, one_mul, CharTwo.add_self_eq_zero, zero_sub,
      neg_eq_zero, hz]
  by_cases hD8 : D % 8 = 1
  · rw [ite_eq_left hD8, quadraticOrderRootCount,
      Nat.card_congr (Equiv.subtypeUnivEquiv fun h => (hr h).mpr hD8), Nat.card_zmod]
  · rw [ite_eq_right hD8]
    let : IsEmpty {h : ZMod 2 //
        h ^ 2 + ((D % 4 : ℤ) : ZMod 2) * h -
          (((D - D % 4) / 4 : ℤ) : ZMod 2) = 0} :=
      ⟨fun h => hD8 ((hr h.val).mp h.property)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem quadraticOrder_root_derivative_coprime (D h : ℤ) (p : ℕ) (hp : p.Prime)
    (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hroot : (p : ℤ) ∣ h ^ 2 + (D % 4) * h - (D - D % 4) / 4)
    (hpd : ¬(p : ℤ) ∣ D) : IsCoprime (p : ℤ) (2 * h + D % 4) := by
  apply Int.isCoprime_iff_nat_coprime.mpr
  simp only [Int.natAbs_natCast]
  apply hp.coprime_iff_not_dvd.mpr
  intro hn
  have hb : (p : ℤ) ∣ 2 * h + D % 4 :=
    Int.natAbs_dvd_natAbs.mp (by simpa only [Int.natAbs_natCast] using hn)
  have hs : (p : ℤ) ∣ (2 * h + D % 4) ^ 2 := dvd_pow hb (by decide : 2 ≠ 0)
  have hd : (p : ℤ) ∣ (2 * h + D % 4) ^ 2 - D := by
    rw [quadraticOrder_polynomial_discriminant D h hm]
    exact dvd_mul_of_dvd_right hroot 4
  apply hpd
  simpa only [sub_sub_cancel] using dvd_sub hs hd

/-- One step of Hensel lifting for the order polynomial, proved over the integers. -/
theorem quadraticOrder_integer_root_lift (D h : ℤ) (p k : ℕ)
    (hk : 1 ≤ k)
    (hroot : (p : ℤ) ^ k ∣ h ^ 2 + (D % 4) * h - (D - D % 4) / 4)
    (hderiv : IsCoprime (p : ℤ) (2 * h + D % 4)) :
    ∃ x : ℤ, (p : ℤ) ^ (k + 1) ∣ x ^ 2 + (D % 4) * x - (D - D % 4) / 4 ∧
      (p : ℤ) ^ k ∣ x - h := by
  obtain ⟨c, hc⟩ := hroot
  obtain ⟨r, s, hrs⟩ := hderiv
  obtain ⟨b, hb⟩ := dvd_pow_self (p : ℤ) (by omega : k ≠ 0)
  let t := -s * c
  refine ⟨h + (p : ℤ) ^ k * t, ⟨r * c + b * t ^ 2, ?_⟩, ⟨t, by ring⟩⟩
  rw [pow_succ]
  dsimp [t]
  linear_combination hc - (p : ℤ) ^ k * c * hrs +
    ((p : ℤ) ^ k * (-s * c) ^ 2) * hb

theorem quadraticOrder_integer_root_lift_unique (D x y : ℤ) (p k : ℕ)
    (hp0 : p ≠ 0) (hk : 1 ≤ k)
    (hx : (p : ℤ) ^ (k + 1) ∣ x ^ 2 + (D % 4) * x - (D - D % 4) / 4)
    (hy : (p : ℤ) ^ (k + 1) ∣ y ^ 2 + (D % 4) * y - (D - D % 4) / 4)
    (hxy : (p : ℤ) ^ k ∣ x - y)
    (hderiv : IsCoprime (p : ℤ) (2 * y + D % 4)) :
    (p : ℤ) ^ (k + 1) ∣ x - y := by
  obtain ⟨t, ht⟩ := hxy
  have hxeq : x = y + (p : ℤ) ^ k * t := by linarith
  obtain ⟨w, hw⟩ := dvd_sub hx hy
  rw [hxeq, pow_succ] at hw
  have ha0 : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  have he : t * (2 * y + D % 4 + (p : ℤ) ^ k * t) = (p : ℤ) * w := by
    apply mul_left_cancel₀ ha0
    linear_combination hw
  have hprod : (p : ℤ) ∣ t * (2 * y + D % 4 + (p : ℤ) ^ k * t) := ⟨w, he⟩
  have ha : (p : ℤ) ∣ (p : ℤ) ^ k := dvd_pow_self _ (by omega : k ≠ 0)
  have hsub : (p : ℤ) ∣ t * (2 * y + D % 4) := by
    have hdiv := dvd_sub hprod (dvd_mul_of_dvd_left ha (t ^ 2))
    convert hdiv using 1
    ring
  have hpt : (p : ℤ) ∣ t := hderiv.dvd_of_dvd_mul_right hsub
  obtain ⟨u, hu⟩ := hpt
  refine ⟨u, ?_⟩
  rw [ht, hu, pow_succ]
  ring

abbrev QuadraticOrderRoot (D : ℤ) (a : ℕ) :=
  {h : ZMod a //
    h ^ 2 + ((D % 4 : ℤ) : ZMod a) * h -
      (((D - D % 4) / 4 : ℤ) : ZMod a) = 0}

def quadraticOrderRootReduction (D : ℤ) (a b : ℕ) (hab : a ∣ b) :
    QuadraticOrderRoot D b → QuadraticOrderRoot D a := fun h =>
  ⟨ZMod.castHom hab (ZMod a) h.val, by
    have he := congrArg (ZMod.castHom hab (ZMod a)) h.property
    simpa only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] using he⟩

theorem quadraticOrderRootReduction_unramified_power_bijective (D : ℤ) (p k : ℕ)
    [Fact p.Prime] (hm : D % 4 = 0 ∨ D % 4 = 1) (hpd : ¬(p : ℤ) ∣ D) (hk : 1 ≤ k) :
    Function.Bijective (quadraticOrderRootReduction D (p ^ k) (p ^ (k + 1))
      (pow_dvd_pow p (by omega))) := by
  have hp : p.Prime := Fact.out
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · intro x y hxy
    have hx := quadraticOrderRoot_int_representative D (p ^ (k + 1)) x.val x.property
    have hy := quadraticOrderRoot_int_representative D (p ^ (k + 1)) y.val y.property
    simp only [Nat.cast_pow] at hx hy
    have heq := congrArg Subtype.val hxy
    change ZMod.castHom _ (ZMod (p ^ k)) x.val =
      ZMod.castHom _ (ZMod (p ^ k)) y.val at heq
    conv_lhs at heq => rw [← ZMod.natCast_zmod_val x.val]
    conv_rhs at heq => rw [← ZMod.natCast_zmod_val y.val]
    rw [map_natCast, map_natCast] at heq
    have hdiv : (p : ℤ) ^ k ∣ (x.val.val : ℤ) - y.val.val := by
      have hz : (((x.val.val : ℤ) - y.val.val : ℤ) : ZMod (p ^ k)) = 0 := by
        push_cast
        exact sub_eq_zero.mpr heq
      simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp hz
    have hderiv := quadraticOrder_root_derivative_coprime D (y.val.val : ℤ) p hp hm
      ((dvd_pow_self (p : ℤ) (by omega : k + 1 ≠ 0)).trans hy) hpd
    have hbig := quadraticOrder_integer_root_lift_unique D (x.val.val : ℤ) (y.val.val : ℤ)
      p k hp.ne_zero hk hx hy hdiv hderiv
    have hz : (((x.val.val : ℤ) - y.val.val : ℤ) : ZMod (p ^ (k + 1))) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ (k + 1))).mpr
        (by simpa only [Nat.cast_pow] using hbig)
    push_cast at hz
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hz
    exact Subtype.ext (sub_eq_zero.mp hz)
  · intro h
    have hr := quadraticOrderRoot_int_representative D (p ^ k) h.val h.property
    simp only [Nat.cast_pow] at hr
    have hderiv := quadraticOrder_root_derivative_coprime D (h.val.val : ℤ) p hp hm
      ((dvd_pow_self (p : ℤ) (by omega : k ≠ 0)).trans hr) hpd
    obtain ⟨x, hx, hxmod⟩ := quadraticOrder_integer_root_lift D (h.val.val : ℤ) p k hk hr hderiv
    have hxroot : (x : ZMod (p ^ (k + 1))) ^ 2 +
        ((D % 4 : ℤ) : ZMod (p ^ (k + 1))) * (x : ZMod (p ^ (k + 1))) -
        (((D - D % 4) / 4 : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
      have he := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (x ^ 2 + (D % 4) * x - (D - D % 4) / 4) (p ^ (k + 1))).mpr
          (by simpa only [Nat.cast_pow] using hx)
      push_cast at he
      exact he
    refine ⟨⟨(x : ZMod (p ^ (k + 1))), hxroot⟩, Subtype.ext ?_⟩
    change ZMod.castHom _ (ZMod (p ^ k)) (x : ZMod (p ^ (k + 1))) = h.val
    rw [map_intCast]
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd ((x - h.val.val : ℤ)) (p ^ k)).mpr
      (by simpa only [Nat.cast_pow] using hxmod)
    push_cast at he
    rw [ZMod.natCast_zmod_val] at he
    exact sub_eq_zero.mp he

theorem quadraticOrderRootCount_unramified_power_step (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hm : D % 4 = 0 ∨ D % 4 = 1) (hpd : ¬(p : ℤ) ∣ D) (hk : 1 ≤ k) :
    quadraticOrderRootCount D (p ^ (k + 1)) = quadraticOrderRootCount D (p ^ k) := by
  exact Nat.card_congr (Equiv.ofBijective _
    (quadraticOrderRootReduction_unramified_power_bijective D p k hm hpd hk))

theorem quadraticOrderRootCount_unramified_power (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hm : D % 4 = 0 ∨ D % 4 = 1) (hpd : ¬(p : ℤ) ∣ D) (hk : 1 ≤ k) :
    quadraticOrderRootCount D (p ^ k) = quadraticOrderRootCount D p := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      simp
    · rw [quadraticOrderRootCount_unramified_power_step D p k hm hpd (by omega)]
      exact ih (by omega)

theorem quadraticOrderRootCount_ramified_prime (D : ℤ) (p : ℕ) [Fact p.Prime]
    (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hpd : (p : ℤ) ∣ D) : quadraticOrderRootCount D p = 1 := by
  by_cases hp2 : p = 2
  · subst p
    have hm0 : D % 4 = 0 := by omega
    exact quadraticOrderRootCount_two_even D hm0
  · have he := quadraticOrderRootCount_prime D p hp2 hm
    have hχ : legendreSym p D = 0 := (legendreSym.eq_zero_iff p D).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpd)
    rw [hχ, zero_add] at he
    exact_mod_cast he

theorem quadraticOrderRootCount_ramified_power (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hpd : (p : ℤ) ∣ D) (hk : 1 ≤ k) :
    quadraticOrderRootCount D (p ^ k) = if k = 1 then 1 else 0 := by
  by_cases hk1 : k = 1
  · rw [hk1, pow_one, ite_eq_left rfl]
    exact quadraticOrderRootCount_ramified_prime D p hm hpd
  · rw [ite_eq_right hk1]
    by_cases hp2 : p = 2
    · subst p
      exact quadraticOrderRootCount_ramified_two_power D k hD (by omega) (by omega)
    · exact quadraticOrderRootCount_ramified_odd_power D p k hD hm hp2 hpd (by omega)

/-- Complete local root-count formula for a fundamental quadratic discriminant. -/
theorem quadraticOrderRootCount_prime_power (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hD : Int.IsFundamentalDiscr D) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (quadraticOrderRootCount D (p ^ k) : ℤ) =
      if k = 0 then 1 else
        if (p : ℤ) ∣ D then (if k = 1 then 1 else 0) else
          if p = 2 then (if D % 8 = 1 then 2 else 0) else legendreSym p D + 1 := by
  by_cases hk0 : k = 0
  · subst k
    simp [quadraticOrderRootCount_one]
  · rw [ite_eq_right hk0]
    by_cases hpd : (p : ℤ) ∣ D
    · rw [ite_eq_left hpd, quadraticOrderRootCount_ramified_power D p k hD hm hpd (by omega)]
      by_cases hk1 : k = 1 <;> simp [hk1]
    · rw [ite_eq_right hpd, quadraticOrderRootCount_unramified_power D p k hm hpd (by omega)]
      by_cases hp2 : p = 2
      · subst p
        rw [ite_eq_left rfl, quadraticOrderRootCount_two_odd D (by omega)]
        by_cases hD8 : D % 8 = 1 <;> simp [hD8]
      · rw [ite_eq_right hp2]
        exact quadraticOrderRootCount_prime D p hp2 hm

/-- Contents whose square divides n. -/
def squareDivisors (n : ℕ) : Finset ℕ := n.divisors.filter fun g => g ^ 2 ∣ n

theorem mem_squareDivisors {n g : ℕ} :
    g ∈ squareDivisors n ↔ g ∣ n ∧ n ≠ 0 ∧ g ^ 2 ∣ n := by
  simp only [squareDivisors, mem_filter, Nat.mem_divisors, and_assoc]

theorem squareDivisor_pos {n g : ℕ} (hn : 0 < n) (hg : g ∈ squareDivisors n) : 0 < g :=
  Nat.pos_of_dvd_of_pos (mem_squareDivisors.mp hg).1 hn

theorem squareDivisor_quotient_pos {n g : ℕ} (hn : 0 < n) (hg : g ∈ squareDivisors n) :
    0 < n / g ^ 2 :=
  Nat.div_pos (Nat.le_of_dvd hn (mem_squareDivisors.mp hg).2.2)
    (pow_pos (squareDivisor_pos hn hg) 2)

abbrev NormQuadraticIdealParameter (D : ℤ) (n : ℕ) :=
  {p : QuadraticIdealParameter D // p.content.natAbs ^ 2 * p.coefficient.natAbs = n}

abbrev SquareDivisorRootParameter (D : ℤ) (n : ℕ) :=
  Σ g : {g : ℕ // g ∈ squareDivisors n}, QuadraticOrderRoot D (n / g.val ^ 2)

def squareDivisorRootToNormParameter (D : ℤ) (n : ℕ) (hn : 0 < n) :
    SquareDivisorRootParameter D n → NormQuadraticIdealParameter D n := fun z => by
  let g := z.fst.val
  let a := n / g ^ 2
  have hg : 0 < g := squareDivisor_pos hn z.fst.property
  have ha : 0 < a := squareDivisor_quotient_pos hn z.fst.property
  let : NeZero a := ⟨ha.ne'⟩
  refine ⟨⟨(g : ℤ), (a : ℤ), (z.snd.val.val : ℤ), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact_mod_cast hg
  · exact_mod_cast ha
  · exact Nat.cast_nonneg _
  · exact_mod_cast ZMod.val_lt z.snd.val
  · exact quadraticOrderRoot_int_representative D a z.snd.val z.snd.property
  · simpa only [Int.natAbs_natCast] using
      Nat.mul_div_cancel' (mem_squareDivisors.mp z.fst.property).2.2

theorem squareDivisorRootToNormParameter_injective (D : ℤ) (n : ℕ) (hn : 0 < n) :
    Function.Injective (squareDivisorRootToNormParameter D n hn) := by
  rintro ⟨g, h⟩ ⟨g', h'⟩ heq
  have hp := congrArg Subtype.val heq
  have hg : g = g' := by
    apply Subtype.ext
    have hc := congrArg QuadraticIdealParameter.content hp
    exact Int.natCast_inj.mp hc
  subst g'
  have ha : 0 < n / g.val ^ 2 := squareDivisor_quotient_pos hn g.property
  let : NeZero (n / g.val ^ 2) := ⟨ha.ne'⟩
  have hh : h = h' := by
    apply Subtype.ext
    apply ZMod.val_injective
    have hs := congrArg QuadraticIdealParameter.shift hp
    exact Int.natCast_inj.mp hs
  exact Sigma.ext rfl (heq_of_eq hh)

theorem squareDivisorRootToNormParameter_surjective (D : ℤ) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (squareDivisorRootToNormParameter D n hn) := by
  rintro ⟨p, hp⟩
  let g := p.content.natAbs
  have hg : 0 < g := Int.natAbs_pos.mpr p.content_pos.ne'
  have hgmem : g ∈ squareDivisors n := by
    apply mem_squareDivisors.mpr
    refine ⟨?_, hn.ne', ⟨p.coefficient.natAbs, hp.symm⟩⟩
    exact ⟨g * p.coefficient.natAbs, by rw [← hp]; dsimp [g]; ring⟩
  let a := n / g ^ 2
  have haeq : a = p.coefficient.natAbs := by
    dsimp only [a, g]
    rw [← hp, Nat.mul_div_cancel_left _ (pow_pos hg 2)]
  have ha : 0 < a := squareDivisor_quotient_pos hn hgmem
  let : NeZero a := ⟨ha.ne'⟩
  have hgcast : (g : ℤ) = p.content := by
    dsimp only [g]
    rw [Int.natCast_natAbs, abs_of_pos p.content_pos]
  have hacast : (a : ℤ) = p.coefficient := by
    rw [haeq, Int.natCast_natAbs, abs_of_pos p.coefficient_pos]
  have hscast : (p.shift.natAbs : ℤ) = p.shift := by
    rw [Int.natCast_natAbs, abs_of_nonneg p.shift_nonneg]
  have hslt : p.shift.natAbs < a := by
    have hs : (p.shift.natAbs : ℤ) < (a : ℤ) := by
      rw [hscast, hacast]
      exact p.shift_lt
    exact_mod_cast hs
  have hr : (p.shift : ZMod a) ^ 2 + ((D % 4 : ℤ) : ZMod a) * (p.shift : ZMod a) -
      (((D - D % 4) / 4 : ℤ) : ZMod a) = 0 := by
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (p.shift ^ 2 + (D % 4) * p.shift - (D - D % 4) / 4) a).mpr
        (by rw [hacast]; exact p.root)
    push_cast at he
    exact he
  have hv : (p.shift : ZMod a).val = p.shift.natAbs := by
    have he : (p.shift.natAbs : ZMod a) = (p.shift : ZMod a) := by
      simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod a)) hscast
    rw [← he]
    exact ZMod.val_natCast_of_lt hslt
  refine ⟨⟨⟨g, hgmem⟩, ⟨(p.shift : ZMod a), hr⟩⟩, Subtype.ext ?_⟩
  apply QuadraticIdealParameter.ext
  · exact hgcast
  · exact hacast
  · change ((p.shift : ZMod a).val : ℤ) = p.shift
    rw [hv]
    exact hscast

def squareDivisorRootNormParameterEquiv (D : ℤ) (n : ℕ) (hn : 0 < n) :
    SquareDivisorRootParameter D n ≃ NormQuadraticIdealParameter D n :=
  Equiv.ofBijective (squareDivisorRootToNormParameter D n hn)
    ⟨squareDivisorRootToNormParameter_injective D n hn,
      squareDivisorRootToNormParameter_surjective D n hn⟩

theorem normQuadraticIdealParameter_count (D : ℤ) (n : ℕ) (hn : 0 < n) :
    Nat.card (NormQuadraticIdealParameter D n) =
      ∑ g ∈ squareDivisors n, quadraticOrderRootCount D (n / g ^ 2) := by
  have hf : ∀ g : {g : ℕ // g ∈ squareDivisors n},
      Finite (QuadraticOrderRoot D (n / g.val ^ 2)) := by
    intro g
    let : NeZero (n / g.val ^ 2) := ⟨(squareDivisor_quotient_pos hn g.property).ne'⟩
    infer_instance
  let : ∀ g : {g : ℕ // g ∈ squareDivisors n},
      Finite (QuadraticOrderRoot D (n / g.val ^ 2)) := hf
  rw [Nat.card_congr (squareDivisorRootNormParameterEquiv D n hn).symm, Nat.card_sigma]
  change (∑ g : {g : ℕ // g ∈ squareDivisors n},
    quadraticOrderRootCount D (n / g.val ^ 2)) = _
  exact sum_coe_sort (squareDivisors n) (fun g => quadraticOrderRootCount D (n / g ^ 2))

/-- The Dedekind-zeta coefficient is the sum of quadratic roots over square contents. -/
theorem quadraticIdeal_count_eq_root_sum {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (hD : Int.IsFundamentalDiscr D)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers (DiscriminantField D)) //
      Ideal.absNorm I = n} =
      ∑ g ∈ squareDivisors n, quadraticOrderRootCount D (n / g ^ 2) := by
  rw [quadraticIdeal_count_eq_parameter_count hD n hn]
  exact normQuadraticIdealParameter_count D n hn

theorem isSquare_nat_mul_coprime_left {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (hs : IsSquare (m * n)) : IsSquare m := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  by_cases hpn : p ∣ n
  · have hpm : ¬p ∣ m := by
      intro hpm
      have hone : p ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd hpm hpn
      exact hp.not_dvd_one hone
    rw [Nat.factorization_eq_zero_of_not_dvd hpm]
    exact Even.zero
  · have he := Nat.isSquare_iff_even_factorization.mp hs p hp
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpn, add_zero] at he
    exact he

theorem isSquare_nat_mul_coprime_iff {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) : IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · intro h
    exact ⟨isSquare_nat_mul_coprime_left hm hn hcop h,
      isSquare_nat_mul_coprime_left hn hm hcop.symm (by simpa only [mul_comm] using h)⟩
  · rintro ⟨hm, hn⟩
    exact hm.mul hn

def squareIndicatorArithmetic : ArithmeticFunction ℕ := by
  classical
  exact ⟨fun n => if n = 0 then 0 else if IsSquare n then 1 else 0, by simp⟩

theorem squareIndicatorArithmetic_multiplicative : squareIndicatorArithmetic.IsMultiplicative := by
  classical
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [squareIndicatorArithmetic, IsSquare.one], ?_⟩
  intro m n hm hn hcop
  simp only [squareIndicatorArithmetic, ArithmeticFunction.coe_mk, mul_ne_zero hm hn, hm, hn, ite_false]
  simp only [isSquare_nat_mul_coprime_iff hm hn hcop]
  by_cases hs : IsSquare m <;> by_cases ht : IsSquare n <;> simp [hs, ht]

def quadraticRootArithmetic (D : ℤ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n = 0 then 0 else quadraticOrderRootCount D n, by simp⟩

theorem quadraticRootArithmetic_multiplicative (D : ℤ) : (quadraticRootArithmetic D).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [quadraticRootArithmetic, quadraticOrderRootCount_one], ?_⟩
  intro m n hm hn hcop
  simp only [quadraticRootArithmetic, ArithmeticFunction.coe_mk, mul_ne_zero hm hn, hm, hn, ite_false]
  exact quadraticOrderRootCount_mul D m n hcop


theorem isSquare_prime_power_iff_even (p k : ℕ) (hp : p.Prime) :
    IsSquare (p ^ k) ↔ Even k := by
  constructor
  · intro hs
    have he := Nat.isSquare_iff_even_factorization.mp hs p hp
    simpa only [hp.factorization_pow, Finsupp.single_eq_same] using he
  · rintro ⟨j, rfl⟩
    exact ⟨p ^ j, by rw [pow_add]⟩

theorem squareIndicatorArithmetic_prime_power (p k : ℕ) (hp : p.Prime) :
    squareIndicatorArithmetic (p ^ k) = if Even k then 1 else 0 := by
  classical
  simp only [squareIndicatorArithmetic, ArithmeticFunction.coe_mk,
    pow_ne_zero _ hp.ne_zero, ite_false, isSquare_prime_power_iff_even p k hp]

def quadraticIdealArithmetic (D : ℤ) : ArithmeticFunction ℕ :=
  squareIndicatorArithmetic * quadraticRootArithmetic D

theorem quadraticIdealArithmetic_multiplicative (D : ℤ) :
    (quadraticIdealArithmetic D).IsMultiplicative :=
  squareIndicatorArithmetic_multiplicative.mul (quadraticRootArithmetic_multiplicative D)

theorem quadraticIdealArithmetic_apply (D : ℤ) (n : ℕ) (hn : 0 < n) :
    quadraticIdealArithmetic D n =
      ∑ g ∈ squareDivisors n, quadraticOrderRootCount D (n / g ^ 2) := by
  classical
  rw [quadraticIdealArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => squareIndicatorArithmetic a * quadraticRootArithmetic D b)]
  have hsum : ∑ d ∈ n.divisors, squareIndicatorArithmetic d * quadraticRootArithmetic D (n / d) =
      ∑ d ∈ n.divisors.filter IsSquare, quadraticOrderRootCount D (n / d) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn
    have hqpos : 0 < n / d :=
      Nat.div_pos (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1) hdpos
    simp [squareIndicatorArithmetic, quadraticRootArithmetic, hdpos.ne', hqpos.ne']
  rw [hsum]
  symm
  refine sum_bij (fun g _ => g ^ 2) ?_ ?_ ?_ ?_
  · intro g hg
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(mem_squareDivisors.mp hg).2.2, hn.ne'⟩,
      ⟨g, by ring⟩⟩
  · intro g hg h hh heq
    nlinarith
  · intro d hd
    obtain ⟨hd, hs⟩ := mem_filter.mp hd
    obtain ⟨g, heq⟩ := hs
    have he : d = g ^ 2 := by simpa only [pow_two] using heq
    have hg2 : g ^ 2 ∣ n := by rw [← he]; exact (Nat.mem_divisors.mp hd).1
    refine ⟨g, mem_squareDivisors.mpr ⟨?_, hn.ne', hg2⟩, he.symm⟩
    exact (dvd_pow_self g (by decide : 2 ≠ 0)).trans hg2
  · intro g hg
    rfl

theorem quadraticIdealArithmetic_prime_power_sum (D : ℤ) (p k : ℕ) (hp : p.Prime) :
    quadraticIdealArithmetic D (p ^ k) =
      ∑ i ∈ range (k + 1), (if Even i then 1 else 0) * quadraticOrderRootCount D (p ^ (k - i)) := by
  classical
  rw [quadraticIdealArithmetic, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => squareIndicatorArithmetic a * quadraticRootArithmetic D b),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have h := mem_range.mp hi; omega
  rw [squareIndicatorArithmetic_prime_power p i hp,
    Nat.pow_div hik hp.pos]
  simp only [quadraticRootArithmetic, ArithmeticFunction.coe_mk,
    pow_ne_zero _ hp.ne_zero, ite_false]


theorem quadraticIdealArithmetic_prime (D : ℤ) (p : ℕ) (hp : p.Prime) :
    quadraticIdealArithmetic D p = quadraticOrderRootCount D p := by
  have h := quadraticIdealArithmetic_prime_power_sum D p 1 hp
  norm_num [sum_range_succ, Nat.even_iff] at h
  exact h

theorem quadraticIdealArithmetic_prime_power_recurrence (D : ℤ) (p k : ℕ) (hp : p.Prime) :
    quadraticIdealArithmetic D (p ^ (k + 2)) =
      quadraticIdealArithmetic D (p ^ k) + quadraticOrderRootCount D (p ^ (k + 2)) := by
  classical
  rw [quadraticIdealArithmetic_prime_power_sum D p (k + 2) hp,
    quadraticIdealArithmetic_prime_power_sum D p k hp]
  change (∑ i ∈ range ((k + 1) + 2),
    (if Even i then 1 else 0) * quadraticOrderRootCount D (p ^ (k + 2 - i))) = _
  rw [sum_range_succ', sum_range_succ']
  have hs : ∑ i ∈ range (k + 1),
      (if Even (i + 1 + 1) then 1 else 0) *
        quadraticOrderRootCount D (p ^ (k + 2 - (i + 1 + 1))) =
      ∑ i ∈ range (k + 1), (if Even i then 1 else 0) *
        quadraticOrderRootCount D (p ^ (k - i)) := by
    apply sum_congr rfl
    intro i hi
    have he : Even (i + 1 + 1) ↔ Even i := by simp only [Nat.even_iff]; omega
    have hn : k + 2 - (i + 1 + 1) = k - i := by omega
    simp only [he, hn]
  rw [hs]
  norm_num [Nat.even_iff]


theorem fundamentalCharacter_odd_prime (d p : ℕ) (hD : isNegativeDiscriminantAbs d)
    [Fact p.Prime] (hp2 : p ≠ 2) :
    fundamentalCharacter d p = (legendreSym p (-(d : ℤ)) : ℝ) := by
  have hp : p.Prime := Fact.out
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rw [jacobiSym.legendreSym.to_jacobiSym]
  rcases hD.2 with hd4 | hd3
  · simp [fundamentalCharacter, hd4, hpo]
  · rw [fundamentalCharacter, ite_eq_left hd3,
      jacobi_negative_three_mod_four hd3 hpo]

theorem fundamentalCharacter_two_even (d : ℕ) (hd : d % 4 = 0) :
    fundamentalCharacter d 2 = 0 := by
  simp [fundamentalCharacter, hd]

theorem fundamentalCharacter_two_odd (d : ℕ) (hd : d % 4 = 3) :
    fundamentalCharacter d 2 = if (-(d : ℤ)) % 8 = 1 then 1 else -1 := by
  have hdo : d % 2 = 1 := by omega
  simp only [fundamentalCharacter, ite_eq_left hd, Nat.cast_ofNat]
  rw [jacobiSym.at_two (Nat.odd_iff.mpr hdo),
    ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega)]
  have hmod : (-(d : ℤ)) % 8 = 1 ↔ d % 8 = 7 := by omega
  have hmod' : d % 8 = 1 ∨ d % 8 = 7 ↔ d % 8 = 7 := by omega
  simp only [hmod', hmod]
  split <;> norm_num

theorem fundamentalCharacter_prime_values (d p : ℕ) (hD : isNegativeDiscriminantAbs d)
    (hp : p.Prime) :
    fundamentalCharacter d p = 0 ∨ fundamentalCharacter d p = 1 ∨
      fundamentalCharacter d p = -1 := by
  by_cases hp2 : p = 2
  · subst p
    rcases hD.2 with hd4 | hd3
    · exact Or.inl (fundamentalCharacter_two_even d hd4)
    · rw [fundamentalCharacter_two_odd d hd3]
      split <;> simp
  · have : Fact p.Prime := ⟨hp⟩
    rw [fundamentalCharacter_odd_prime d p hD hp2]
    by_cases hzero : ((-(d : ℤ)) : ZMod p) = 0
    · left
      exact_mod_cast (legendreSym.eq_zero_iff p (-(d : ℤ))).mpr (by simpa only [Int.cast_neg, Int.cast_natCast] using hzero)
    · rcases legendreSym.eq_one_or_neg_one p (a := -(d : ℤ)) (by simpa only [Int.cast_neg, Int.cast_natCast] using hzero) with h | h
      · exact Or.inr (Or.inl (by exact_mod_cast h))
      · exact Or.inr (Or.inr (by exact_mod_cast h))

theorem fundamentalArithmetic_multiplicative (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    (fundamentalArithmetic d hD).IsMultiplicative := by
  constructor
  · exact fundamentalCharacter_one d hD
  · intro a b _
    exact fundamentalCharacter_mul d a b hD


theorem fundamentalCharacter_prime_eq_zero_iff (d p : ℕ)
    (hD : isNegativeDiscriminantAbs d) [Fact p.Prime] :
    fundamentalCharacter d p = 0 ↔ (p : ℤ) ∣ -(d : ℤ) := by
  have hp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst p
    rcases hD.2 with hd4 | hd3
    · rw [fundamentalCharacter_two_even d hd4]
      constructor
      · intro _
        omega
      · intro _
        rfl
    · rw [fundamentalCharacter_two_odd d hd3]
      have hn : ¬(2 : ℤ) ∣ -(d : ℤ) := by omega
      norm_num only [Nat.cast_ofNat]
      rw [iff_false_right hn]
      split <;> norm_num
  · rw [fundamentalCharacter_odd_prime d p hD hp2]
    rw [show ((legendreSym p (-(d : ℤ)) : ℝ) = 0) ↔
      legendreSym p (-(d : ℤ)) = 0 by exact_mod_cast Iff.rfl]
    exact (legendreSym.eq_zero_iff p (-(d : ℤ))).trans
      (ZMod.intCast_zmod_eq_zero_iff_dvd (-(d : ℤ)) p)

theorem quadraticOrderRootCount_eq_character_prime (d p : ℕ)
    (hD : isNegativeDiscriminantAbs d) [Fact p.Prime] :
    (quadraticOrderRootCount (-(d : ℤ)) p : ℝ) = 1 + fundamentalCharacter d p := by
  have hm : (-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1 := by
    rcases hD.2 with h | h <;> omega
  by_cases hp2 : p = 2
  · subst p
    rcases hD.2 with hd4 | hd3
    · rw [quadraticOrderRootCount_two_even _ (by omega), fundamentalCharacter_two_even d hd4]
      norm_num
    · rw [quadraticOrderRootCount_two_odd _ (by omega), fundamentalCharacter_two_odd d hd3]
      split <;> norm_num
  · rw [fundamentalCharacter_odd_prime d p hD hp2]
    have h := quadraticOrderRootCount_prime (-(d : ℤ)) p hp2 hm
    exact_mod_cast h.trans (add_comm _ _)

theorem quadraticOrderRootCount_character_power_step (d p k : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ)))
    [Fact p.Prime] :
    (quadraticOrderRootCount (-(d : ℤ)) (p ^ (k + 2)) : ℝ) =
      fundamentalCharacter d p ^ (k + 1) + fundamentalCharacter d p ^ (k + 2) := by
  have hm : (-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1 := hF.emod_four_eq_zero_or_one
  by_cases hpd : (p : ℤ) ∣ -(d : ℤ)
  · rw [quadraticOrderRootCount_ramified_power _ p (k + 2) hF hm hpd (by omega),
      (fundamentalCharacter_prime_eq_zero_iff d p hD).mpr hpd]
    norm_num
  · rw [quadraticOrderRootCount_unramified_power _ p (k + 2) hm hpd (by omega),
      quadraticOrderRootCount_eq_character_prime d p hD]
    rcases fundamentalCharacter_prime_values d p hD Fact.out with h | h | h
    · exact False.elim (hpd ((fundamentalCharacter_prime_eq_zero_iff d p hD).mp h))
    · simp [h]
    · rw [h, show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring


theorem fundamentalCharacter_pow (d p k : ℕ) (hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d (p ^ k) = fundamentalCharacter d p ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using fundamentalCharacter_one d hD
  | succ k ih => rw [pow_succ, fundamentalCharacter_mul d _ _ hD, ih, pow_succ]

theorem zeta_fundamental_prime_power (d p k : ℕ) (hD : isNegativeDiscriminantAbs d)
    (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * fundamentalArithmetic d hD) (p ^ k) =
      ∑ j ∈ range (k + 1), fundamentalCharacter d p ^ j := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j _
  exact fundamentalCharacter_pow d p j hD

theorem zeta_fundamental_prime_power_recurrence (d p k : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * fundamentalArithmetic d hD) (p ^ (k + 2)) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * fundamentalArithmetic d hD) (p ^ k) +
        fundamentalCharacter d p ^ (k + 1) + fundamentalCharacter d p ^ (k + 2) := by
  rw [zeta_fundamental_prime_power d p (k + 2) hD hp,
    zeta_fundamental_prime_power d p k hD hp]
  rw [show k + 2 + 1 = (k + 1) + 1 + 1 by omega, sum_range_succ, sum_range_succ]

theorem quadraticIdealArithmetic_eq_zeta_character (d : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ))) :
    (quadraticIdealArithmetic (-(d : ℤ)) : ArithmeticFunction ℝ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * fundamentalArithmetic d hD := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (quadraticIdealArithmetic_multiplicative _).natCast _
    (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      (fundamentalArithmetic_multiplicative d hD))).mpr
  intro p k hp
  have : Fact p.Prime := ⟨hp⟩
  apply Nat.twoStepInduction (motive := fun k =>
    (quadraticIdealArithmetic (-(d : ℤ)) : ArithmeticFunction ℝ) (p ^ k) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * fundamentalArithmetic d hD) (p ^ k))
      ?_ ?_ (fun k ih _ => ?_) k
  · simp only [pow_zero]
    rw [(quadraticIdealArithmetic_multiplicative _).natCast.map_one,
      (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
        (fundamentalArithmetic_multiplicative d hD)).map_one]
  · rw [pow_one, ArithmeticFunction.natCoe_apply, quadraticIdealArithmetic_prime _ p hp,
      quadraticOrderRootCount_eq_character_prime d p hD,
      ← pow_one p, zeta_fundamental_prime_power d p 1 hD hp]
    norm_num [sum_range_succ]
  · rw [ArithmeticFunction.natCoe_apply, quadraticIdealArithmetic_prime_power_recurrence _ p k hp,
      Nat.cast_add, quadraticOrderRootCount_character_power_step d p k hD hF,
      zeta_fundamental_prime_power_recurrence d p k hD hp]
    rw [ArithmeticFunction.natCoe_apply] at ih
    rw [ih]
    ring

theorem quadraticIdealArithmetic_eq_character_divisor_sum (d n : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ))) :
    (quadraticIdealArithmetic (-(d : ℤ)) n : ℝ) =
      ∑ a ∈ n.divisors, fundamentalCharacter d a := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (quadraticIdealArithmetic_eq_zeta_character d hD hF)
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.coe_zeta_mul_apply] at h
  exact h

theorem quadraticIdeal_count_eq_character_divisor_sum (d n : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1)]
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ))) (hn : 0 < n) :
    (Nat.card {I : Ideal (NumberField.RingOfIntegers (DiscriminantField (-(d : ℤ)))) //
      Ideal.absNorm I = n} : ℝ) = ∑ a ∈ n.divisors, fundamentalCharacter d a := by
  rw [quadraticIdeal_count_eq_root_sum hF n hn, ← quadraticIdealArithmetic_apply _ n hn]
  exact quadraticIdealArithmetic_eq_character_divisor_sum d n hD hF


def negativeDiscriminantComplexFunction (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (t : ZMod d) : ℂ :=
  (negativeDiscriminantCharacter d hD t : ℂ)

theorem negativeDiscriminantComplexFunction_natCast (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (a : ℕ) :
    negativeDiscriminantComplexFunction d hD (a : ZMod d) = (fundamentalCharacter d a : ℂ) := by
  simp only [negativeDiscriminantComplexFunction, negativeDiscriminantCharacter_natCast]

theorem negativeDiscriminantComplexFunction_norm_le_one (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (t : ZMod d) :
    ‖negativeDiscriminantComplexFunction d hD t‖ ≤ 1 := by
  simpa only [negativeDiscriminantComplexFunction, Complex.norm_real] using
    (negativeDiscriminantCharacter d hD).norm_le_one t

theorem negativeDiscriminantComplexFunction_odd (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) :
    Function.Odd (negativeDiscriminantComplexFunction d hD) := by
  intro t
  simpa only [negativeDiscriminantComplexFunction, Complex.ofReal_neg] using
    congrArg Complex.ofReal ((negativeDiscriminantCharacter_odd d hD).to_fun t)

theorem negativeDiscriminantComplexFunction_sum_zero (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) :
    ∑ t : ZMod d, negativeDiscriminantComplexFunction d hD t = 0 :=
  (negativeDiscriminantComplexFunction_odd d hD).sum_eq_zero

theorem negativeDiscriminantComplexFunction_LSeriesSummable (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun a : ℕ => negativeDiscriminantComplexFunction d hD (a : ZMod d)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun a _ => negativeDiscriminantComplexFunction_norm_le_one d hD a) hs

theorem negativeDiscriminantComplexFunction_continuousAt_one (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) :
    ContinuousAt (ZMod.LFunction (negativeDiscriminantComplexFunction d hD)) 1 :=
  (ZMod.differentiableAt_LFunction _ 1
    (Or.inr (negativeDiscriminantComplexFunction_sum_zero d hD))).continuousAt


theorem quadraticIdeal_coefficient_eq_convolution (d n : ℕ) [NeZero d]
    [Fact (-(d : ℤ) < 0)] [Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1)]
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ))) (hn : 0 < n) :
    (Nat.card {I : Ideal (NumberField.RingOfIntegers (DiscriminantField (-(d : ℤ)))) //
      Ideal.absNorm I = n} : ℂ) =
      LSeries.convolution
        (fun a : ℕ => negativeDiscriminantComplexFunction d hD (a : ZMod d)) 1 n := by
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal
    (fun a _ => negativeDiscriminantComplexFunction d hD (a : ZMod d))]
  simp only [negativeDiscriminantComplexFunction_natCast, ← Complex.ofReal_sum]
  exact congrArg Complex.ofReal (quadraticIdeal_count_eq_character_divisor_sum d n hD hF hn)

theorem discriminantField_dedekindZeta_factorization (d : ℕ) [NeZero d]
    [Fact (-(d : ℤ) < 0)] [Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1)]
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ)))
    {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (DiscriminantField (-(d : ℤ))) s =
      riemannZeta s * ZMod.LFunction (negativeDiscriminantComplexFunction d hD) s := by
  rw [NumberField.dedekindZeta]
  rw [LSeries_congr (fun {n} hn =>
    quadraticIdeal_coefficient_eq_convolution d n hD hF (Nat.pos_of_ne_zero hn)) s]
  rw [LSeries_convolution'
      (negativeDiscriminantComplexFunction_LSeriesSummable d hD hs)
      (LSeriesSummable_one_iff.mpr hs),
    LSeries_one_eq_riemannZeta hs, ← ZMod.LFunction_eq_LSeries _ hs, mul_comm]
theorem negative_rpow_sub_bound {x y s : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hs : 1 ≤ s) (hs2 : s ≤ 2) :
    ‖y ^ (-s) - x ^ (-s)‖ ≤ 2 / x ^ 2 * (y - x) := by
  have hx0 : 0 < x := by linarith
  have hd (t : ℝ) (ht : t ∈ Set.Icc x y) :
      HasDerivWithinAt (fun t : ℝ => t ^ (-s)) ((-s) * t ^ (-s - 1)) (Set.Icc x y) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hx0.trans_le ht.1)))).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Set.Ico x y) :
      ‖(-s) * t ^ (-s - 1)‖ ≤ 2 / x ^ 2 := by
    have ht0 : 0 < t := hx0.trans_le ht.1
    have hp : t ^ (-s - 1) ≤ x ^ (-2 : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le (hx.trans ht.1) (by linarith)).trans
        (Real.rpow_le_rpow_of_nonpos hx0 ht.1 (by norm_num : (-2 : ℝ) ≤ 0))
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith : 0 ≤ s),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hp0 : 0 ≤ t ^ (-s - 1) := Real.rpow_nonneg ht0.le _
    have h := mul_le_mul hs2 hp hp0 (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1
    rw [Real.rpow_neg hx0.le, Real.rpow_two]
    ring
  exact norm_image_sub_le_of_norm_deriv_le_segment' hd hb y (Set.right_mem_Icc.mpr hxy)


def periodicPowerBlock (d : ℕ) (f : ℕ → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ range d, f a * ((a : ℝ) + (d : ℝ) * k) ^ (-s)

theorem periodicPowerBlock_bound (d : ℕ) (hd : 0 < d) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : ∀ a < d, ‖f a‖ ≤ 1)
    (hfs : ∑ a ∈ range d, f a = 0) (s : ℝ) (hs : 1 ≤ s) (hs2 : s ≤ 2) (k : ℕ) :
    ‖periodicPowerBlock d f s k‖ ≤ 2 * (d : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  classical
  let x : ℝ := 1 + (d : ℝ) * k
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) from Nat.cast_nonneg d) (show 0 ≤ (k : ℝ) from Nat.cast_nonneg k)]
  have hx0 : 0 < x := by linarith
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hkx : (k : ℝ) + 1 ≤ x := by dsimp [x]; nlinarith [show 0 ≤ (k : ℝ) from Nat.cast_nonneg k]
  have hfs' : ∑ a ∈ (range d).erase 0, f a = 0 := by
    rw [← sum_erase_add _ _ (mem_range.mpr hd), hf0, add_zero] at hfs
    exact hfs
  have hid : periodicPowerBlock d f s k =
      ∑ a ∈ (range d).erase 0, f a *
        (((a : ℝ) + (d : ℝ) * k) ^ (-s) - x ^ (-s)) := by
    unfold periodicPowerBlock
    rw [← sum_erase_add _ _ (mem_range.mpr hd)]
    simp only [hf0, zero_mul, add_zero, mul_sub, sum_sub_distrib, ← sum_mul, hfs', zero_mul,
      sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  have hb (a : ℕ) (ha : a ∈ (range d).erase 0) :
      ‖f a * (((a : ℝ) + (d : ℝ) * k) ^ (-s) - x ^ (-s))‖ ≤
        2 * (d : ℝ) / ((k : ℝ) + 1) ^ 2 := by
    have ha0 : 0 < a := Nat.pos_of_ne_zero (mem_erase.mp ha).1
    have hal : a < d := mem_range.mp (mem_erase.mp ha).2
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have had : (a : ℝ) ≤ d := by exact_mod_cast hal.le
    have hxy : x ≤ (a : ℝ) + (d : ℝ) * k := by dsimp [x]; linarith
    have hadiff : (a : ℝ) + (d : ℝ) * k - x ≤ (d : ℝ) := by dsimp [x]; linarith
    rw [norm_mul]
    calc
      ‖f a‖ * ‖((a : ℝ) + (d : ℝ) * k) ^ (-s) - x ^ (-s)‖
          ≤ 1 * ‖((a : ℝ) + (d : ℝ) * k) ^ (-s) - x ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right (hf1 a hal) (norm_nonneg _)
      _ ≤ 2 / x ^ 2 * ((a : ℝ) + (d : ℝ) * k - x) := by
        simpa only [one_mul] using negative_rpow_sub_bound hx hxy hs hs2
      _ ≤ 2 / x ^ 2 * (d : ℝ) := by gcongr
      _ ≤ 2 * (d : ℝ) / ((k : ℝ) + 1) ^ 2 := by
        rw [div_mul_eq_mul_div]
        gcongr
  apply (sum_le_sum hb).trans
  rw [sum_const, nsmul_eq_mul]
  have hc : ((range d).erase 0).card ≤ d := by
    exact (card_le_card (erase_subset _ _)).trans (by rw [card_range])
  calc
    (((range d).erase 0).card : ℝ) * (2 * (d : ℝ) / ((k : ℝ) + 1) ^ 2)
        ≤ (d : ℝ) * (2 * (d : ℝ) / ((k : ℝ) + 1) ^ 2) := by gcongr
    _ = 2 * (d : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 := by ring


theorem periodicPowerBlock_continuousAt_one (d : ℕ) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (k : ℕ) :
    ContinuousAt (fun s : ℝ => periodicPowerBlock d f s k) 1 := by
  classical
  unfold periodicPowerBlock
  apply tendsto_finsetSum
  intro a _
  by_cases ha : a = 0
  · subst a
    simp only [hf0, zero_mul]
    exact tendsto_const_nhds
  · have hb : (a : ℝ) + (d : ℝ) * k ≠ 0 := by positivity
    exact (continuousAt_const.mul
      ((Real.continuousAt_const_rpow hb).comp continuousAt_id.neg)).tendsto

theorem periodicPowerBlock_limit_one (d : ℕ) (hd : 0 < d) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hf1 : ∀ a < d, ‖f a‖ ≤ 1)
    (hfs : ∑ a ∈ range d, f a = 0) :
    Filter.Tendsto (fun s : ℝ => ∑' k : ℕ, periodicPowerBlock d f s k)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (∑' k : ℕ, periodicPowerBlock d f 1 k)) := by
  have hsum : Summable (fun k : ℕ => 2 * (d : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2) := by
    have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h'.mul_left (2 * (d : ℝ) ^ 2)
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro k
    exact (periodicPowerBlock_continuousAt_one d f hf0 k).continuousWithinAt.tendsto
  · filter_upwards [self_mem_nhdsWithin,
      (show Set.Iio (2 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1) from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num)))] with s hs hs2
    intro k
    exact periodicPowerBlock_bound d hd f hf0 hf1 hfs s hs.le hs2.le k


theorem tsum_eq_period_blocks {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
    (d : ℕ) [NeZero d] (f : ℕ → G) (hf : Summable f) :
    ∑' n : ℕ, f n = ∑' k : ℕ, ∑ a ∈ range d, f (a + d * k) := by
  have hp : Summable (fun p : ℕ × Fin d => f (p.1 * d + p.2)) := by
    have h := (Nat.divModEquiv d).symm.summable_iff.mpr hf
    convert h using 1
    ext p
    simp only [Function.comp_apply, Nat.divModEquiv_symm_apply]
  calc
    ∑' n : ℕ, f n = ∑' p : ℕ × Fin d, f (p.1 * d + p.2) := by
      simpa only [Nat.divModEquiv_symm_apply] using ((Nat.divModEquiv d).symm.tsum_eq f).symm
    _ = ∑' k : ℕ, ∑' a : Fin d, f (k * d + a) := hp.tsum_prod
    _ = ∑' k : ℕ, ∑ a ∈ range d, f (a + d * k) := by
      apply tsum_congr
      intro k
      rw [tsum_fintype, Fin.sum_univ_eq_sum_range (fun a : ℕ => f (k * d + a)) d]
      apply sum_congr rfl
      intro a _
      rw [mul_comm k d, add_comm]


theorem negativeDiscriminantComplexFunction_term_real (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (s : ℝ) (hs : 1 < s) (n : ℕ) :
    LSeries.term (fun a : ℕ => negativeDiscriminantComplexFunction d hD (a : ZMod d)) (s : ℂ) n =
      ((fundamentalCharacter d n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero' (by exact_mod_cast (by linarith : s ≠ 0)),
    negativeDiscriminantComplexFunction_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n) s, Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]

theorem fundamentalCharacter_add_period_multiple (d a k : ℕ)
    (hD : isNegativeDiscriminantAbs d) :
    fundamentalCharacter d (a + d * k) = fundamentalCharacter d a := by
  rw [← (fundamentalCharacter_periodic d hD).map_mod_nat (a + d * k),
    ← (fundamentalCharacter_periodic d hD).map_mod_nat a]
  congr 1
  simp [Nat.add_mod]

theorem negativeDiscriminantComplexFunction_LFunction_eq_blocks (d : ℕ) [NeZero d]
    (hD : isNegativeDiscriminantAbs d) (s : ℝ) (hs : 1 < s) :
    ZMod.LFunction (negativeDiscriminantComplexFunction d hD) (s : ℂ) =
      ((∑' k : ℕ, periodicPowerBlock d (fundamentalCharacter d) s k : ℝ) : ℂ) := by
  rw [ZMod.LFunction_eq_LSeries _ (by simpa using hs), LSeries,
    tsum_eq_period_blocks d _
      (negativeDiscriminantComplexFunction_LSeriesSummable d hD (by simpa using hs)),
    Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  unfold periodicPowerBlock
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro a _
  rw [negativeDiscriminantComplexFunction_term_real d hD s hs,
    fundamentalCharacter_add_period_multiple d a k hD]
  simp only [Nat.cast_add, Nat.cast_mul]


theorem fundamentalCharacter_norm_le_one (d a : ℕ) (hD : isNegativeDiscriminantAbs d) :
    ‖fundamentalCharacter d a‖ ≤ 1 := by
  let : NeZero d := ⟨hD.1.ne'⟩
  rw [← negativeDiscriminantCharacter_natCast d hD a]
  exact (negativeDiscriminantCharacter d hD).norm_le_one _

theorem fundamentalCharacter_sum_zero (d : ℕ) (hD : isNegativeDiscriminantAbs d) :
    ∑ a ∈ range d, fundamentalCharacter d a = 0 := by
  let : NeZero d := ⟨hD.1.ne'⟩
  have hs := (negativeDiscriminantCharacter_odd d hD).to_fun.sum_eq_zero
  have he : ∑ t : ZMod d, negativeDiscriminantCharacter d hD t =
      ∑ a : Fin d, negativeDiscriminantCharacter d hD (ZMod.finEquiv d a) :=
    ((ZMod.finEquiv d).toEquiv.sum_comp _).symm
  rw [he] at hs
  have hev (a : Fin d) : (ZMod.finEquiv d a).val = (a : ℕ) := by
    cases d with
    | zero => exact Fin.elim0 a
    | succ d => rfl
  change (∑ a : Fin d, fundamentalCharacter d (ZMod.finEquiv d a).val) = 0 at hs
  simp only [hev] at hs
  rw [Fin.sum_univ_eq_sum_range] at hs
  exact hs

theorem periodicPowerBlock_one_eq_reciprocal (d : ℕ) (f : ℕ → ℝ) (k : ℕ) :
    periodicPowerBlock d f 1 k =
      ∑ a ∈ range d, f a / ((a : ℝ) + (d : ℝ) * k) := by
  unfold periodicPowerBlock
  simp only [Real.rpow_neg_one, div_eq_mul_inv]

theorem negativeDiscriminantComplexFunction_LFunction_one_eq_characterLValue (d : ℕ)
    [NeZero d] (hD : isNegativeDiscriminantAbs d) :
    ZMod.LFunction (negativeDiscriminantComplexFunction d hD) 1 =
      (characterLValue d (fundamentalCharacter d) : ℂ) := by
  have hblock := periodicPowerBlock_limit_one d hD.1 (fundamentalCharacter d)
    (fundamentalCharacter_zero d hD) (fun a _ => fundamentalCharacter_norm_le_one d a hD)
    (fundamentalCharacter_sum_zero d hD)
  have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp hblock
  have hc : Filter.Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto
  have hl := (negativeDiscriminantComplexFunction_continuousAt_one d hD).tendsto.comp hc
  have hl' : Filter.Tendsto (fun s : ℝ => ZMod.LFunction
      (negativeDiscriminantComplexFunction d hD) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((∑' k : ℕ, periodicPowerBlock d (fundamentalCharacter d) 1 k : ℝ) : ℂ)) := by
    apply hb.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (negativeDiscriminantComplexFunction_LFunction_eq_blocks d hD s hs).symm
  have he := tendsto_nhds_unique hl hl'
  simpa only [periodicPowerBlock_one_eq_reciprocal, characterLValue] using he


theorem discriminantField_LFunction_one_eq_class_number (d : ℕ) [NeZero d]
    [Fact (-(d : ℤ) < 0)] [Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1)]
    (hD : isNegativeDiscriminantAbs d) (hF : Int.IsFundamentalDiscr (-(d : ℤ))) :
    ZMod.LFunction (negativeDiscriminantComplexFunction d hD) 1 =
      ((2 * Real.pi * (orderClassNumber (-(d : ℤ)) : ℝ) /
        (orderUnitCount (-(d : ℤ)) * Real.sqrt d)) : ℂ) := by
  have hc : Filter.Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 1 {1}ᶜ) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun s hs => by simpa using ne_of_gt hs)
  have hz := riemannZeta_residue_one.comp hc
  have hc0 : Filter.Tendsto (fun s : ℝ => (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto
  have hL := (negativeDiscriminantComplexFunction_continuousAt_one d hD).tendsto.comp hc0
  have hlim : Filter.Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (DiscriminantField (-(d : ℤ))) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (ZMod.LFunction (negativeDiscriminantComplexFunction d hD) 1)) := by
    have ht := hz.mul hL
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [discriminantField_dedekindZeta_factorization d hD hF (by simpa using hs)]
    simp only [Function.comp_apply, mul_assoc]
  have hf := discriminantField_class_number_limit_forms (-(d : ℤ)) hF
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (show 0 ≤ (d : ℝ) from Nat.cast_nonneg d)] at hf
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat] using tendsto_nhds_unique hlim hf

/-- Dirichlet's class-number formula derived from Mathlib's analytic residue theorem,
the proved form/ideal correspondence, ideal counts, and period-block limit. -/
theorem fundamentalDirichletClassNumberFormula : FundamentalDirichletClassNumberFormula := by
  intro d hd hF
  have hD : isNegativeDiscriminantAbs d :=
    (negativeDiscriminantAbs_iff d).mpr ⟨by omega, hF.emod_four_eq_zero_or_one⟩
  let : NeZero d := ⟨hd.ne'⟩
  have : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
  have : Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1) :=
    ⟨hF.emod_four_eq_zero_or_one⟩
  have h := discriminantField_LFunction_one_eq_class_number d hD hF
  rw [negativeDiscriminantComplexFunction_LFunction_one_eq_characterLValue d hD] at h
  have hr : characterLValue d (fundamentalCharacter d) =
      2 * Real.pi * (orderClassNumber (-(d : ℤ)) : ℝ) /
        ((orderUnitCount (-(d : ℤ)) : ℝ) * Real.sqrt d) := by
    exact_mod_cast h
  rw [hr]
  unfold classRatio
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Assembly of the original formula from the order class-number identity. -/
theorem closed_formula_of_order_class_number (hO : OrderClassNumberFormula) :
    (residueSum n : ℝ) = (n : ℝ) * (n - squarePart n) / 2 -
      2 * n * ∑ M ∈ discriminantDivisors n,
        (orderClassNumber (-(M : ℤ)) : ℝ) / orderUnitCount (-(M : ℤ)) := by
  exact closed_formula_of_class_number_inputs fundamentalDirichletClassNumberFormula hO

def conductorOrderShift (D : ℤ) (s : ℕ) : ℤ :=
  ((D * (s : ℤ) ^ 2) % 4 - (s : ℤ) * (D % 4)) / 2

theorem conductorOrderShift_relation (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    2 * conductorOrderShift D s + (s : ℤ) * (D % 4) = (D * (s : ℤ) ^ 2) % 4 := by
  have hs : 0 ≤ (s : ℤ) % 4 := Int.emod_nonneg _ (by norm_num)
  have hs4 : (s : ℤ) % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hp : (D * (s : ℤ) ^ 2) % 4 =
      ((D % 4) * ((s : ℤ) % 4) ^ 2) % 4 := by simp only [pow_two, Int.mul_emod, Int.emod_emod]
  have he : ((D * (s : ℤ) ^ 2) % 4 - (s : ℤ) * (D % 4)) % 2 = 0 := by
    rw [hp]
    rcases hm with hm | hm <;> rw [hm] <;> interval_cases h : (s : ℤ) % 4 <;> norm_num <;> omega
  unfold conductorOrderShift
  omega

theorem conductorOrderShift_polynomial_relation (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) :
    conductorOrderShift D s ^ 2 + ((D - D % 4) / 4) * (s : ℤ) ^ 2 =
      (D * (s : ℤ) ^ 2 - (D * (s : ℤ) ^ 2) % 4) / 4 +
        (D * (s : ℤ) ^ 2) % 4 * conductorOrderShift D s := by
  have hr := conductorOrderShift_relation D s hm
  have hD := discriminantOrder_discr D hm
  have hm' : (D * (s : ℤ) ^ 2) % 4 = 0 ∨ (D * (s : ℤ) ^ 2) % 4 = 1 := by
    have hp : (D * (s : ℤ) ^ 2) % 4 =
        ((D % 4) * ((s : ℤ) % 4) ^ 2) % 4 := by simp only [pow_two, Int.mul_emod, Int.emod_emod]
    rw [hp]
    have hs : 0 ≤ (s : ℤ) % 4 := Int.emod_nonneg _ (by norm_num)
    have hs4 : (s : ℤ) % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    rcases hm with hm | hm <;> rw [hm] <;> interval_cases h : (s : ℤ) % 4 <;> norm_num
  have hDs := discriminantOrder_discr (D * (s : ℤ) ^ 2) hm'
  have hD' := congrArg (fun t : ℤ => t * (s : ℤ) ^ 2) hD
  rw [← hr] at hDs ⊢
  nlinarith

def conductorOrderEmbedding (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    DiscriminantOrder (D * (s : ℤ) ^ 2) →ₐ[ℤ] DiscriminantOrder D :=
  QuadraticAlgebra.lift ⟨⟨conductorOrderShift D s, (s : ℤ)⟩, by
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.re_smul,
        QuadraticAlgebra.re_one, smul_eq_mul, mul_one]
      change conductorOrderShift D s * conductorOrderShift D s +
        ((D - D % 4) / 4) * (s : ℤ) * (s : ℤ) =
        (D * (s : ℤ) ^ 2 - (D * (s : ℤ) ^ 2) % 4) / 4 +
          (D * (s : ℤ) ^ 2) % 4 * conductorOrderShift D s
      simpa only [pow_two, mul_assoc] using conductorOrderShift_polynomial_relation D s hm
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add, QuadraticAlgebra.im_smul,
        QuadraticAlgebra.im_one, smul_eq_mul, mul_zero, zero_add]
      change conductorOrderShift D s * (s : ℤ) +
        (s : ℤ) * conductorOrderShift D s + (D % 4) * (s : ℤ) * (s : ℤ) =
          (D * (s : ℤ) ^ 2) % 4 * (s : ℤ)
      linear_combination (s : ℤ) * conductorOrderShift_relation D s hm⟩

theorem conductorOrderEmbedding_apply (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    conductorOrderEmbedding D s hm z =
      (⟨z.re + conductorOrderShift D s * z.im, (s : ℤ) * z.im⟩ : DiscriminantOrder D) := by
  ext <;> simp [conductorOrderEmbedding, QuadraticAlgebra.lift_apply_apply] <;> ring

theorem conductorOrderEmbedding_injective (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) (hs : 0 < s) :
    Function.Injective (conductorOrderEmbedding D s hm) := by
  intro z w h
  rw [conductorOrderEmbedding_apply, conductorOrderEmbedding_apply] at h
  have hi := congrArg QuadraticAlgebra.im h
  have hr := congrArg QuadraticAlgebra.re h
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have him : z.im = w.im := mul_left_cancel₀ hs0 hi
  ext
  · change z.re + conductorOrderShift D s * z.im =
      w.re + conductorOrderShift D s * w.im at hr
    rw [him] at hr
    exact add_right_cancel hr
  · exact him

theorem conductorOrderEmbedding_range (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder D) :
    z ∈ (conductorOrderEmbedding D s hm).range ↔ (s : ℤ) ∣ z.im := by
  constructor
  · rintro ⟨w, hw⟩
    change conductorOrderEmbedding D s hm w = z at hw
    rw [conductorOrderEmbedding_apply] at hw
    have hi := congrArg QuadraticAlgebra.im hw
    exact ⟨w.im, hi.symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨⟨z.re - conductorOrderShift D s * y, y⟩, ?_⟩
    change conductorOrderEmbedding D s hm
      (⟨z.re - conductorOrderShift D s * y, y⟩ : DiscriminantOrder (D * (s : ℤ) ^ 2)) = z
    rw [conductorOrderEmbedding_apply]
    ext
    · change z.re - conductorOrderShift D s * y + conductorOrderShift D s * y = z.re
      ring
    · exact hy.symm


theorem mem_conductorOrderAdjoin (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder D) :
    z ∈ Algebra.adjoin ℤ {(⟨conductorOrderShift D s, (s : ℤ)⟩ : DiscriminantOrder D)} ↔
      (s : ℤ) ∣ z.im := by
  simpa only [conductorOrderEmbedding, QuadraticAlgebra.range_lift] using
    conductorOrderEmbedding_range D s hm z

theorem mem_conductorOrderConductor (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder D) :
    z ∈ conductor ℤ (⟨conductorOrderShift D s, (s : ℤ)⟩ : DiscriminantOrder D) ↔
      (s : ℤ) ∣ z.re ∧ (s : ℤ) ∣ z.im := by
  rw [mem_conductor_iff]
  constructor
  · intro hz
    have hi : (s : ℤ) ∣ z.im := by
      apply (mem_conductorOrderAdjoin D s hm z).mp
      simpa only [mul_one] using hz 1
    have hω : (s : ℤ) ∣ z.re + (D % 4) * z.im := by
      have h := (mem_conductorOrderAdjoin D s hm
        (z * (⟨0, 1⟩ : DiscriminantOrder D))).mp (hz _)
      simpa only [QuadraticAlgebra.im_mul, mul_one, mul_zero, add_zero] using h
    have hr : (s : ℤ) ∣ z.re := by
      have h := dvd_sub hω (dvd_mul_of_dvd_right hi (D % 4))
      simpa only [add_sub_cancel_right] using h
    exact ⟨hr, hi⟩
  · rintro ⟨hr, hi⟩ w
    apply (mem_conductorOrderAdjoin D s hm (z * w)).mpr
    rw [QuadraticAlgebra.im_mul]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left hr w.im) (dvd_mul_of_dvd_left hi w.re))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hi (D % 4)) w.im)

theorem mem_discriminantOrder_integer_ideal (D t : ℤ) (z : DiscriminantOrder D) :
    z ∈ Ideal.span {(t : DiscriminantOrder D)} ↔ t ∣ z.re ∧ t ∣ z.im := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩
    have hr := congrArg QuadraticAlgebra.re hw
    have hi := congrArg QuadraticAlgebra.im hw
    change z.re = t * w.re + ((D - D % 4) / 4) * 0 * w.im at hr
    change z.im = t * w.im + 0 * w.re + (D % 4) * 0 * w.im at hi
    exact ⟨⟨w.re, by simpa using hr⟩, ⟨w.im, by simpa using hi⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, y⟩, ?_⟩
    ext
    · change z.re = t * x + ((D - D % 4) / 4) * 0 * y
      simpa using hx
    · change z.im = t * y + 0 * x + (D % 4) * 0 * y
      simpa using hy

theorem conductorOrder_conductor_eq (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    conductor ℤ (⟨conductorOrderShift D s, (s : ℤ)⟩ : DiscriminantOrder D) =
      Ideal.span {((s : ℤ) : DiscriminantOrder D)} := by
  ext z
  rw [mem_conductorOrderConductor D s hm z, mem_discriminantOrder_integer_ideal]
abbrev ResidueDiscriminantOrder (D : ℤ) (n : ℕ) :=
  QuadraticAlgebra (ZMod n) (((D - D % 4) / 4 : ℤ) : ZMod n) ((D % 4 : ℤ) : ZMod n)

def discriminantOrderResidueMap (D : ℤ) (n : ℕ) :
    DiscriminantOrder D →+* ResidueDiscriminantOrder D n where
  toFun z := ⟨(z.re : ZMod n), (z.im : ZMod n)⟩
  map_zero' := by ext <;> simp
  map_one' := by
    ext <;> simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Int.cast_one, Int.cast_zero]
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul]

theorem discriminantOrderResidueMap_surjective (D : ℤ) (n : ℕ) :
    Function.Surjective (discriminantOrderResidueMap D n) := by
  intro z
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective z.re
  obtain ⟨y, hy⟩ := ZMod.intCast_surjective z.im
  refine ⟨⟨x, y⟩, ?_⟩
  ext <;> assumption

theorem discriminantOrderResidueMap_ker (D : ℤ) (n : ℕ) :
    RingHom.ker (discriminantOrderResidueMap D n) =
      Ideal.span {((n : ℤ) : DiscriminantOrder D)} := by
  ext z
  rw [RingHom.mem_ker, mem_discriminantOrder_integer_ideal]
  change (⟨(z.re : ZMod n), (z.im : ZMod n)⟩ : ResidueDiscriminantOrder D n) = 0 ↔ _
  rw [QuadraticAlgebra.ext_iff]
  change (z.re : ZMod n) = 0 ∧ (z.im : ZMod n) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

def discriminantOrder_integer_quotientEquiv (D : ℤ) (n : ℕ) :
    DiscriminantOrder D ⧸ Ideal.span {((n : ℤ) : DiscriminantOrder D)} ≃+*
      ResidueDiscriminantOrder D n :=
  (Ideal.quotEquivOfEq (discriminantOrderResidueMap_ker D n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (discriminantOrderResidueMap_surjective D n))

theorem residueDiscriminantOrder_card (D : ℤ) (n : ℕ) :
    Nat.card (ResidueDiscriminantOrder D n) = n ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd
      (((D - D % 4) / 4 : ℤ) : ZMod n) ((D % 4 : ℤ) : ZMod n)),
    Nat.card_prod, Nat.card_zmod, pow_two]

theorem discriminantOrder_integer_quotient_card (D : ℤ) (n : ℕ) :
    Nat.card (DiscriminantOrder D ⧸ Ideal.span {((n : ℤ) : DiscriminantOrder D)}) = n ^ 2 := by
  rw [Nat.card_congr (discriminantOrder_integer_quotientEquiv D n).toEquiv,
    residueDiscriminantOrder_card]

theorem conductorOrder_conductor_quotient_card (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) :
    Nat.card (DiscriminantOrder D ⧸
      conductor ℤ (⟨conductorOrderShift D s, (s : ℤ)⟩ : DiscriminantOrder D)) = s ^ 2 := by
  rw [conductorOrder_conductor_eq D s hm, discriminantOrder_integer_quotient_card]

theorem discriminantOrderResidueMap_norm (D : ℤ) (n : ℕ) (z : DiscriminantOrder D) :
    QuadraticAlgebra.norm (discriminantOrderResidueMap D n z) =
      ((QuadraticAlgebra.norm z : ℤ) : ZMod n) := by
  change QuadraticAlgebra.norm (⟨(z.re : ZMod n), (z.im : ZMod n)⟩ :
    ResidueDiscriminantOrder D n) = ((QuadraticAlgebra.norm z : ℤ) : ZMod n)
  simp only [QuadraticAlgebra.norm_def, Int.cast_add, Int.cast_sub, Int.cast_mul]

theorem residueDiscriminantOrder_isUnit_iff (D : ℤ) (n : ℕ)
    (z : ResidueDiscriminantOrder D n) :
    IsUnit z ↔ IsUnit (QuadraticAlgebra.norm z) :=
  QuadraticAlgebra.isUnit_iff_norm_isUnit

def residueDiscriminantUnitsEquiv (D : ℤ) (p : ℕ) [Fact p.Prime] :
    (ResidueDiscriminantOrder D p)ˣ ≃
      {z : ResidueDiscriminantOrder D p // QuadraticAlgebra.norm z ≠ 0} where
  toFun u := ⟨u, isUnit_iff_ne_zero.mp
    ((residueDiscriminantOrder_isUnit_iff D p u).mp u.isUnit)⟩
  invFun z := ((residueDiscriminantOrder_isUnit_iff D p z).mpr
    (isUnit_iff_ne_zero.mpr z.property)).unit
  left_inv u := by
    apply Units.ext
    exact IsUnit.unit_spec _
  right_inv z := by
    apply Subtype.ext
    change (((residueDiscriminantOrder_isUnit_iff D p z).mpr
      (isUnit_iff_ne_zero.mpr z.property)).unit : ResidueDiscriminantOrder D p) = z.val
    exact IsUnit.unit_spec _

theorem residueDiscriminantNorm_pair (D : ℤ) (p : ℕ) (h y : ZMod p) :
    QuadraticAlgebra.norm (⟨h * y, y⟩ : ResidueDiscriminantOrder D p) =
      y ^ 2 * (h ^ 2 + ((D % 4 : ℤ) : ZMod p) * h - (((D - D % 4) / 4 : ℤ) : ZMod p)) := by
  simp only [QuadraticAlgebra.norm_def]
  ring

theorem residueDiscriminantNorm_zero_im (D : ℤ) (p : ℕ) [Fact p.Prime]
    (z : ResidueDiscriminantOrder D p) (hz : QuadraticAlgebra.norm z = 0) (hi : z.im = 0) :
    z = 0 := by
  have hr : z.re * z.re = 0 := by simpa only [QuadraticAlgebra.norm_def, hi, mul_zero, add_zero,
    sub_zero] using hz
  have hre : z.re = 0 := (mul_self_eq_zero.mp hr)
  ext <;> assumption

theorem residueDiscriminantNorm_ratio_root (D : ℤ) (p : ℕ) [Fact p.Prime]
    (z : ResidueDiscriminantOrder D p) (hz : QuadraticAlgebra.norm z = 0) (hi : z.im ≠ 0) :
    (z.re / z.im) ^ 2 + ((D % 4 : ℤ) : ZMod p) * (z.re / z.im) -
      (((D - D % 4) / 4 : ℤ) : ZMod p) = 0 := by
  have he : (⟨(z.re / z.im) * z.im, z.im⟩ : ResidueDiscriminantOrder D p) = z := by
    ext
    · exact div_mul_cancel₀ _ hi
    · rfl
  have h := residueDiscriminantNorm_pair D p (z.re / z.im) z.im
  rw [he, hz, eq_comm] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hi)


def residueDiscriminantNormZeroEquiv (D : ℤ) (p : ℕ) [Fact p.Prime] :
    {z : ResidueDiscriminantOrder D p // QuadraticAlgebra.norm z = 0} ≃
      Option (QuadraticOrderRoot D p × (ZMod p)ˣ) where
  toFun z := if hi : z.val.im = 0 then none else
    some (⟨z.val.re / z.val.im, residueDiscriminantNorm_ratio_root D p z z.property hi⟩,
      Units.mk0 z.val.im hi)
  invFun
    | none => ⟨0, by simp [QuadraticAlgebra.norm_def]⟩
    | some (h, u) => ⟨⟨h.val * (u : ZMod p), (u : ZMod p)⟩, by
        rw [residueDiscriminantNorm_pair, h.property, mul_zero]⟩
  left_inv z := by
    by_cases hi : z.val.im = 0
    · simp only [hi, dite_true]
      apply Subtype.ext
      exact (residueDiscriminantNorm_zero_im D p z z.property hi).symm
    · simp only [hi, dite_false]
      apply Subtype.ext
      ext
      · exact div_mul_cancel₀ _ hi
      · rfl
  right_inv z := by
    cases z with
    | none => simp only [show (0 : ResidueDiscriminantOrder D p).im = 0 by rfl, dite_true]
    | some z =>
      rcases z with ⟨h, u⟩
      have hu : (u : ZMod p) ≠ 0 := u.ne_zero
      simp only [hu, dite_false]
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact mul_div_cancel_right₀ _ hu
      · apply Units.ext
        rfl


theorem residueDiscriminantNorm_zero_card (D : ℤ) (p : ℕ) [Fact p.Prime] :
    Nat.card {z : ResidueDiscriminantOrder D p // QuadraticAlgebra.norm z = 0} =
      quadraticOrderRootCount D p * (p - 1) + 1 := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_congr (residueDiscriminantNormZeroEquiv D p),
    Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, Nat.card_prod]
  have hu : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hu]
  rfl

theorem residueDiscriminant_units_add_norm_zero_card (D : ℤ) (p : ℕ) [Fact p.Prime] :
    Nat.card (ResidueDiscriminantOrder D p)ˣ +
      Nat.card {z : ResidueDiscriminantOrder D p // QuadraticAlgebra.norm z = 0} = p ^ 2 := by
  classical
  let : Fintype (ResidueDiscriminantOrder D p) :=
    Fintype.ofEquiv (ZMod p × ZMod p) (QuadraticAlgebra.equivProd _ _).symm
  have hc := Nat.card_congr (Equiv.sumCompl
    (fun z : ResidueDiscriminantOrder D p => QuadraticAlgebra.norm z = 0))
  rw [Nat.card_sum, residueDiscriminantOrder_card] at hc
  rw [Nat.card_congr (residueDiscriminantUnitsEquiv D p)]
  simpa only [ne_eq, add_comm] using hc

theorem residueDiscriminant_units_card_prime (D : ℤ) (p : ℕ) [Fact p.Prime] :
    Nat.card (ResidueDiscriminantOrder D p)ˣ =
      p ^ 2 - (quadraticOrderRootCount D p * (p - 1) + 1) := by
  have h := residueDiscriminant_units_add_norm_zero_card D p
  rw [residueDiscriminantNorm_zero_card] at h
  omega


theorem residueDiscriminant_units_prime_character (d p : ℕ) [Fact p.Prime]
    (hD : isNegativeDiscriminantAbs d) :
    (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) p)ˣ : ℝ) =
      ((p : ℝ) - 1) * ((p : ℝ) - fundamentalCharacter d p) := by
  have h := residueDiscriminant_units_add_norm_zero_card (-(d : ℤ)) p
  rw [residueDiscriminantNorm_zero_card] at h
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hr : (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) p)ˣ : ℝ) +
      (quadraticOrderRootCount (-(d : ℤ)) p : ℝ) * ((p : ℝ) - 1) + 1 = (p : ℝ) ^ 2 := by
    exact_mod_cast h
  rw [quadraticOrderRootCount_eq_character_prime d p hD] at hr
  nlinarith


def residueDiscriminantReduction (D : ℤ) (a b : ℕ) (hab : a ∣ b) :
    ResidueDiscriminantOrder D b →+* ResidueDiscriminantOrder D a where
  toFun z := ⟨ZMod.castHom hab (ZMod a) z.re, ZMod.castHom hab (ZMod a) z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by
    ext <;> simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_one, map_zero]
  map_add' z w := by
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
  map_mul' z w := by
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_intCast]

theorem residueDiscriminantReduction_surjective (D : ℤ) (a b : ℕ) (hab : a ∣ b) :
    Function.Surjective (residueDiscriminantReduction D a b hab) := by
  intro z
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hab z.re
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective hab z.im
  refine ⟨⟨x, y⟩, ?_⟩
  ext <;> assumption

theorem residueDiscriminantReduction_norm (D : ℤ) (a b : ℕ) (hab : a ∣ b)
    (z : ResidueDiscriminantOrder D b) :
    QuadraticAlgebra.norm (residueDiscriminantReduction D a b hab z) =
      ZMod.castHom hab (ZMod a) (QuadraticAlgebra.norm z) := by
  change QuadraticAlgebra.norm
    (⟨ZMod.castHom hab (ZMod a) z.re, ZMod.castHom hab (ZMod a) z.im⟩ :
      ResidueDiscriminantOrder D a) = _
  simp only [QuadraticAlgebra.norm_def, map_add, map_sub, map_mul, map_intCast]

theorem zmod_isUnit_prime_power_reduction (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (z : ZMod (p ^ k)) :
    IsUnit z ↔ IsUnit (ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) z) := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val z, map_natCast]
  rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hk]


theorem residueDiscriminant_isUnit_prime_power (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hk : 0 < k) (z : ResidueDiscriminantOrder D (p ^ k)) :
    IsUnit z ↔ IsUnit (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne') z) := by
  rw [residueDiscriminantOrder_isUnit_iff, residueDiscriminantOrder_isUnit_iff,
    residueDiscriminantReduction_norm, zmod_isUnit_prime_power_reduction p k hk]

theorem residueDiscriminant_units_reduction_surjective (D : ℤ) (p k : ℕ) [Fact p.Prime]
    (hk : 0 < k) :
    Function.Surjective (Units.map
      (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne')).toMonoidHom) := by
  intro u
  obtain ⟨z, hz⟩ := residueDiscriminantReduction_surjective D p (p ^ k)
    (dvd_pow_self p hk.ne') (u : ResidueDiscriminantOrder D p)
  have hu : IsUnit z := (residueDiscriminant_isUnit_prime_power D p k hk z).mpr
    (hz.symm ▸ u.isUnit)
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  change residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne')
    (hu.unit : ResidueDiscriminantOrder D (p ^ k)) = (u : ResidueDiscriminantOrder D p)
  rw [IsUnit.unit_spec]
  exact hz


theorem addHom_kernel_card_mul_of_surjective {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card B = Nat.card A := by
  have h := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, f.range_eq_top_of_surjective hf] at h
  simpa only [AddSubgroup.card_top] using h

theorem groupHom_kernel_card_mul_of_surjective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card B = Nat.card A := by
  have h := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf] at h
  simpa only [Subgroup.card_top] using h

def residueUnitsKernelAddKernelEquiv {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hu : ∀ z : R, IsUnit z ↔ IsUnit (f z)) :
    (Units.map f.toMonoidHom).ker ≃ f.toAddMonoidHom.ker where
  toFun u := ⟨(u.val : R) - 1, by
    change f ((u.val : R) - 1) = 0
    have h : f (u.val : R) = 1 := by
      have hv := congrArg Units.val u.property
      exact hv
    rw [map_sub, map_one, h, sub_self]⟩
  invFun w :=
    ⟨((hu (w.val + 1)).mpr (by
      have hw : f w.val = 0 := w.property
      rw [map_add, hw, map_one, zero_add]
      exact isUnit_one)).unit, by
        apply Units.ext
        change f (↑_) = 1
        rw [IsUnit.unit_spec, map_add]
        have hw : f w.val = 0 := w.property
        rw [hw, map_one, zero_add]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rw [IsUnit.unit_spec]
    exact sub_add_cancel _ _
  right_inv w := by
    apply Subtype.ext
    change (↑_ : R) - 1 = w.val
    rw [IsUnit.unit_spec]
    exact add_sub_cancel_right _ _

theorem residueDiscriminantReduction_addKernel_card (D : ℤ) (p k : ℕ)
    [Fact p.Prime] (hk : 0 < k) :
    Nat.card (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne')).toAddMonoidHom.ker =
      (p ^ (k - 1)) ^ 2 := by
  have h := addHom_kernel_card_mul_of_surjective
    (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne')).toAddMonoidHom
    (residueDiscriminantReduction_surjective D p (p ^ k) (dvd_pow_self p hk.ne'))
  rw [residueDiscriminantOrder_card, residueDiscriminantOrder_card] at h
  have he : (p ^ (k - 1)) ^ 2 * p ^ 2 = (p ^ k) ^ 2 := by
    rw [← mul_pow, ← pow_succ, show k - 1 + 1 = k by omega]
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos 2)
  rw [h, he]


theorem residueDiscriminant_units_prime_power_card (D : ℤ) (p k : ℕ)
    [Fact p.Prime] (hk : 0 < k) :
    Nat.card (ResidueDiscriminantOrder D (p ^ k))ˣ =
      (p ^ (k - 1)) ^ 2 * Nat.card (ResidueDiscriminantOrder D p)ˣ := by
  have h := groupHom_kernel_card_mul_of_surjective
    (Units.map (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne')).toMonoidHom)
    (residueDiscriminant_units_reduction_surjective D p k hk)
  rw [Nat.card_congr (residueUnitsKernelAddKernelEquiv
    (residueDiscriminantReduction D p (p ^ k) (dvd_pow_self p hk.ne'))
    (residueDiscriminant_isUnit_prime_power D p k hk)), residueDiscriminantReduction_addKernel_card D p k hk] at h
  exact h.symm


def residueDiscriminantCrtEquiv (D : ℤ) (a b : ℕ) (hab : a.Coprime b) :
    ResidueDiscriminantOrder D (a * b) ≃+*
      ResidueDiscriminantOrder D a × ResidueDiscriminantOrder D b := by
  let e := ZMod.chineseRemainder hab
  refine
    { toFun := fun z => (⟨(e z.re).1, (e z.im).1⟩, ⟨(e z.re).2, (e z.im).2⟩)
      invFun := fun z => ⟨e.symm (z.1.re, z.2.re), e.symm (z.1.im, z.2.im)⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_ }
  · intro z
    ext <;> exact e.symm_apply_apply _
  · intro z
    apply Prod.ext
    · ext
      · exact congrArg Prod.fst (e.apply_symm_apply (z.1.re, z.2.re))
      · exact congrArg Prod.fst (e.apply_symm_apply (z.1.im, z.2.im))
    · ext
      · exact congrArg Prod.snd (e.apply_symm_apply (z.1.re, z.2.re))
      · exact congrArg Prod.snd (e.apply_symm_apply (z.1.im, z.2.im))
  · intro z w
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_intCast,
      Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul, Prod.fst_intCast, Prod.snd_intCast]
  · intro z w
    ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add,
      Prod.fst_add, Prod.snd_add]

theorem residueDiscriminant_units_card_mul (D : ℤ) (a b : ℕ)
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) :
    Nat.card (ResidueDiscriminantOrder D (a * b))ˣ =
      Nat.card (ResidueDiscriminantOrder D a)ˣ * Nat.card (ResidueDiscriminantOrder D b)ˣ := by
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨hb.ne'⟩
  let : Fintype (ResidueDiscriminantOrder D a) :=
    Fintype.ofEquiv (ZMod a × ZMod a) (QuadraticAlgebra.equivProd _ _).symm
  let : Fintype (ResidueDiscriminantOrder D b) :=
    Fintype.ofEquiv (ZMod b × ZMod b) (QuadraticAlgebra.equivProd _ _).symm
  rw [Nat.card_congr (Units.mapEquiv (residueDiscriminantCrtEquiv D a b hab).toMulEquiv).toEquiv,
    Nat.card_congr MulEquiv.prodUnits.toEquiv, Nat.card_prod]

theorem residueDiscriminant_units_card_one (D : ℤ) :
    Nat.card (ResidueDiscriminantOrder D 1)ˣ = 1 := Nat.card_unique

def residueUnitsArithmetic (D : ℤ) : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else Nat.card (ResidueDiscriminantOrder D n)ˣ
  map_zero' := by simp

theorem residueUnitsArithmetic_multiplicative (D : ℤ) :
    (residueUnitsArithmetic D).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [residueUnitsArithmetic]
  · intro a b ha hb hab
    simp only [residueUnitsArithmetic, ArithmeticFunction.coe_mk, ha, hb, mul_ne_zero ha hb,
      ite_false]
    exact residueDiscriminant_units_card_mul D a b hab (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)


theorem eulerProduct_mul (d a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    eulerProduct d (a * b) = eulerProduct d a * eulerProduct d b := by
  unfold eulerProduct
  rw [Nat.primeFactors_mul ha hb, prod_union hab.disjoint_primeFactors]

theorem conductorCorrection_mul (d a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    conductorCorrection d (a * b) = conductorCorrection d a * conductorCorrection d b := by
  unfold conductorCorrection
  rw [Nat.cast_mul, eulerProduct_mul d a b ha hb hab]
  ring

theorem conductorCorrection_one (d : ℕ) : conductorCorrection d 1 = 1 := by
  simp [conductorCorrection, eulerProduct]

theorem residueDiscriminant_units_prime_power_character (d p k : ℕ) [Fact p.Prime]
    (hD : isNegativeDiscriminantAbs d) (hk : 0 < k) :
    (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) (p ^ k))ˣ : ℝ) =
      ((p ^ k).totient : ℝ) * conductorCorrection d (p ^ k) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [residueDiscriminant_units_prime_power_card _ p k hk, Nat.cast_mul, Nat.cast_pow,
    residueDiscriminant_units_prime_character d p hD, Nat.totient_prime_pow hp hk,
    Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
  unfold conductorCorrection eulerProduct
  rw [Nat.primeFactors_pow p hk.ne', hp.primeFactors, prod_singleton, Nat.cast_pow, Nat.cast_pow]
  have he : (p : ℝ) ^ k = (p : ℝ) ^ (k - 1) * p := by
    rw [← pow_succ, show k - 1 + 1 = k by omega]
  rw [he]
  field_simp

theorem residueDiscriminant_units_conductor_correction (d s : ℕ)
    (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) s)ˣ : ℝ) =
      (s.totient : ℝ) * conductorCorrection d s := by
  apply Nat.recOnPrimeCoprime (motive := fun s =>
    0 < s → (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) s)ˣ : ℝ) =
      (s.totient : ℝ) * conductorCorrection d s) ?_ ?_ ?_ s hs
  · intro h
    omega
  · intro p k hp _
    have : Fact p.Prime := ⟨hp⟩
    by_cases hk : k = 0
    · subst k
      change (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) 1)ˣ : ℝ) =
        (Nat.totient 1 : ℝ) * conductorCorrection d 1
      rw [residueDiscriminant_units_card_one, Nat.totient_one, conductorCorrection_one]
      norm_num
    · exact residueDiscriminant_units_prime_power_character d p k hD (Nat.pos_of_ne_zero hk)
  · intro a b ha hb hab hfa hfb _
    rw [residueDiscriminant_units_card_mul _ a b hab (by omega) (by omega), Nat.cast_mul,
      hfa (by omega), hfb (by omega), Nat.totient_mul hab, Nat.cast_mul,
      conductorCorrection_mul d a b (by omega) (by omega) hab]
    ring


def residueDiscriminantScalar (D : ℤ) (s : ℕ) : ZMod s →+* ResidueDiscriminantOrder D s :=
  algebraMap (ZMod s) (ResidueDiscriminantOrder D s)

theorem residueDiscriminantScalar_injective (D : ℤ) (s : ℕ) :
    Function.Injective (residueDiscriminantScalar D s) := by
  intro x y h
  exact congrArg QuadraticAlgebra.re h

def residueDiscriminantScalarUnits (D : ℤ) (s : ℕ) :
    (ZMod s)ˣ →* (ResidueDiscriminantOrder D s)ˣ :=
  Units.map (residueDiscriminantScalar D s).toMonoidHom

theorem residueDiscriminantScalarUnits_injective (D : ℤ) (s : ℕ) :
    Function.Injective (residueDiscriminantScalarUnits D s) := by
  intro u v h
  apply Units.ext
  apply residueDiscriminantScalar_injective D s
  exact congrArg Units.val h

abbrev ConductorResidueClassGroup (D : ℤ) (s : ℕ) :=
  (ResidueDiscriminantOrder D s)ˣ ⧸ (residueDiscriminantScalarUnits D s).range

theorem conductorResidueClassGroup_card (d s : ℕ) (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    (Nat.card (ConductorResidueClassGroup (-(d : ℤ)) s) : ℝ) = conductorCorrection d s := by
  let : NeZero s := ⟨hs.ne'⟩
  have he : Nat.card (residueDiscriminantScalarUnits (-(d : ℤ)) s).range = Nat.card (ZMod s)ˣ :=
    (Nat.card_congr (Equiv.ofInjective (residueDiscriminantScalarUnits (-(d : ℤ)) s)
      (residueDiscriminantScalarUnits_injective (-(d : ℤ)) s))).symm
  have hz : Nat.card (ZMod s)ˣ = s.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (residueDiscriminantScalarUnits (-(d : ℤ)) s).range
  rw [he, hz] at h
  have hc : (Nat.card (ResidueDiscriminantOrder (-(d : ℤ)) s)ˣ : ℝ) =
      (Nat.card (ConductorResidueClassGroup (-(d : ℤ)) s) : ℝ) * (s.totient : ℝ) := by
    exact_mod_cast h
  rw [residueDiscriminant_units_conductor_correction d s hD hs] at hc
  have hp : (s.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hs).ne'
  apply mul_right_cancel₀ hp
  rw [← hc]
  ring


instance residueDiscriminantOrder_finite (D : ℤ) (s : ℕ) [NeZero s] :
    Finite (ResidueDiscriminantOrder D s) := by
  let : Fintype (ResidueDiscriminantOrder D s) :=
    Fintype.ofEquiv (ZMod s × ZMod s) (QuadraticAlgebra.equivProd _ _).symm
  infer_instance

theorem conductorCorrection_pos (d s : ℕ) (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    0 < conductorCorrection d s := by
  let : NeZero s := ⟨hs.ne'⟩
  rw [← conductorResidueClassGroup_card d s hD hs]
  apply Nat.cast_pos.mpr
  apply Nat.card_pos

theorem conductorOrderEmbedding_norm (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    QuadraticAlgebra.norm (conductorOrderEmbedding D s hm z) = QuadraticAlgebra.norm z := by
  rw [conductorOrderEmbedding_apply]
  simp only [QuadraticAlgebra.norm_def]
  linear_combination
    (z.re * z.im + conductorOrderShift D s * z.im ^ 2) * conductorOrderShift_relation D s hm -
      z.im ^ 2 * conductorOrderShift_polynomial_relation D s hm

theorem conductorOrderEmbedding_isUnit (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    IsUnit (conductorOrderEmbedding D s hm z) ↔ IsUnit z := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.isUnit_iff_norm_isUnit,
    conductorOrderEmbedding_norm]

def conductorOrderUnitsEmbedding (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (DiscriminantOrder (D * (s : ℤ) ^ 2))ˣ →* (DiscriminantOrder D)ˣ :=
  Units.map (conductorOrderEmbedding D s hm).toRingHom.toMonoidHom

theorem conductorOrderUnitsEmbedding_injective (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) (hs : 0 < s) :
    Function.Injective (conductorOrderUnitsEmbedding D s hm) := by
  intro u v h
  apply Units.ext
  apply conductorOrderEmbedding_injective D s hm hs
  exact congrArg Units.val h

theorem conductorOrderUnitsEmbedding_range (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (u : (DiscriminantOrder D)ˣ) :
    u ∈ (conductorOrderUnitsEmbedding D s hm).range ↔ (s : ℤ) ∣ (u : DiscriminantOrder D).im := by
  constructor
  · rintro ⟨v, hv⟩
    apply (conductorOrderEmbedding_range D s hm u).mp
    refine ⟨(v : DiscriminantOrder (D * (s : ℤ) ^ 2)), ?_⟩
    exact congrArg Units.val hv
  · intro hu
    obtain ⟨z, hz⟩ := (conductorOrderEmbedding_range D s hm u).mpr hu
    have hi : IsUnit z := (conductorOrderEmbedding_isUnit D s hm z).mp (hz.symm ▸ u.isUnit)
    refine ⟨hi.unit, ?_⟩
    apply Units.ext
    change conductorOrderEmbedding D s hm
      (hi.unit : DiscriminantOrder (D * (s : ℤ) ^ 2)) = (u : DiscriminantOrder D)
    rw [IsUnit.unit_spec]
    exact hz


theorem residueDiscriminantScalarUnits_range (D : ℤ) (s : ℕ)
    (u : (ResidueDiscriminantOrder D s)ˣ) :
    u ∈ (residueDiscriminantScalarUnits D s).range ↔
      (u : ResidueDiscriminantOrder D s).im = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hi := congrArg (fun u : (ResidueDiscriminantOrder D s)ˣ =>
      (u : ResidueDiscriminantOrder D s).im) hv
    exact hi.symm
  · intro hi
    have hn : IsUnit (QuadraticAlgebra.norm (u : ResidueDiscriminantOrder D s)) :=
      (residueDiscriminantOrder_isUnit_iff D s _).mp u.isUnit
    have he : QuadraticAlgebra.norm (u : ResidueDiscriminantOrder D s) =
        (u : ResidueDiscriminantOrder D s).re * (u : ResidueDiscriminantOrder D s).re := by
      simp only [QuadraticAlgebra.norm_def, hi, mul_zero, add_zero, sub_zero]
    rw [he, IsUnit.mul_iff] at hn
    refine ⟨hn.1.unit, ?_⟩
    apply Units.ext
    change algebraMap (ZMod s) (ResidueDiscriminantOrder D s)
      (hn.1.unit : ZMod s) = (u : ResidueDiscriminantOrder D s)
    rw [IsUnit.unit_spec]
    ext
    · rfl
    · exact hi.symm

def maximalOrderUnitsResidueClassMap (D : ℤ) (s : ℕ) :
    (DiscriminantOrder D)ˣ →* ConductorResidueClassGroup D s :=
  (QuotientGroup.mk' (residueDiscriminantScalarUnits D s).range).comp
    (Units.map (discriminantOrderResidueMap D s).toMonoidHom)

theorem maximalOrderUnitsResidueClassMap_kernel (D : ℤ) (s : ℕ)
    (u : (DiscriminantOrder D)ˣ) :
    u ∈ (maximalOrderUnitsResidueClassMap D s).ker ↔ (s : ℤ) ∣ (u : DiscriminantOrder D).im := by
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk' (residueDiscriminantScalarUnits D s).range
    (Units.map (discriminantOrderResidueMap D s).toMonoidHom u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, residueDiscriminantScalarUnits_range]
  change ((u : DiscriminantOrder D).im : ZMod s) = 0 ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

theorem conductorOrderUnits_range_eq_kernel (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (conductorOrderUnitsEmbedding D s hm).range = (maximalOrderUnitsResidueClassMap D s).ker := by
  ext u
  rw [conductorOrderUnitsEmbedding_range, maximalOrderUnitsResidueClassMap_kernel]


theorem conductorDiscriminant_mod_four (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    (D * (s : ℤ) ^ 2) % 4 = 0 ∨ (D * (s : ℤ) ^ 2) % 4 = 1 := by
  have hp : (D * (s : ℤ) ^ 2) % 4 =
      ((D % 4) * ((s : ℤ) % 4) ^ 2) % 4 := by simp only [pow_two, Int.mul_emod, Int.emod_emod]
  rw [hp]
  have hs : 0 ≤ (s : ℤ) % 4 := Int.emod_nonneg _ (by norm_num)
  have hs4 : (s : ℤ) % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  rcases hm with hm | hm <;> rw [hm] <;> interval_cases h : (s : ℤ) % 4 <;> norm_num

theorem maximalOrderUnitsResidueClassMap_kernel_card (D : ℤ) (s : ℕ)
    (hD : D < 0) (hm : D % 4 = 0 ∨ D % 4 = 1) (hs : 0 < s) :
    Nat.card (maximalOrderUnitsResidueClassMap D s).ker = orderUnitCount (D * (s : ℤ) ^ 2) := by
  rw [← conductorOrderUnits_range_eq_kernel D s hm]
  have he : Nat.card (conductorOrderUnitsEmbedding D s hm).range =
      Nat.card (DiscriminantOrder (D * (s : ℤ) ^ 2))ˣ :=
    (Nat.card_congr (Equiv.ofInjective (conductorOrderUnitsEmbedding D s hm)
      (conductorOrderUnitsEmbedding_injective D s hm hs))).symm
  rw [he]
  exact discriminantOrder_unit_card _ (mul_neg_of_neg_of_pos hD (by
    exact_mod_cast pow_pos hs 2)) (conductorDiscriminant_mod_four D s hm)

theorem maximalOrderUnitsResidueClassMap_image_card (D : ℤ) (s : ℕ)
    (hD : D < 0) (hm : D % 4 = 0 ∨ D % 4 = 1) (hs : 0 < s) :
    (Nat.card (maximalOrderUnitsResidueClassMap D s).range : ℝ) =
      (orderUnitCount D : ℝ) / orderUnitCount (D * (s : ℤ) ^ 2) := by
  have h := Subgroup.card_mul_index (maximalOrderUnitsResidueClassMap D s).ker
  rw [Subgroup.index_ker, maximalOrderUnitsResidueClassMap_kernel_card D s hD hm hs,
    discriminantOrder_unit_card D hD hm] at h
  have hw : (orderUnitCount (D * (s : ℤ) ^ 2) : ℝ) ≠ 0 := by
    unfold orderUnitCount
    split <;> norm_num
    split <;> norm_num
  apply (eq_div_iff hw).mpr
  rw [mul_comm]
  exact_mod_cast h


abbrev ConductorKernelGroup (D : ℤ) (s : ℕ) :=
  ConductorResidueClassGroup D s ⧸ (maximalOrderUnitsResidueClassMap D s).range

theorem conductorKernelGroup_card_ratio (d s : ℕ) (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    (Nat.card (ConductorKernelGroup (-(d : ℤ)) s) : ℝ) /
        (orderUnitCount (-((d * s ^ 2 : ℕ) : ℤ)) : ℝ) =
      conductorCorrection d s / orderUnitCount (-(d : ℤ)) := by
  have hm : (-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1 := by rcases hD.2 with h | h <;> omega
  have hneg : -(d : ℤ) < 0 := by have hd := hD.1; omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (maximalOrderUnitsResidueClassMap (-(d : ℤ)) s).range
  have hc : (Nat.card (ConductorResidueClassGroup (-(d : ℤ)) s) : ℝ) =
      (Nat.card (ConductorKernelGroup (-(d : ℤ)) s) : ℝ) *
        (Nat.card (maximalOrderUnitsResidueClassMap (-(d : ℤ)) s).range : ℝ) := by exact_mod_cast h
  rw [conductorResidueClassGroup_card d s hD hs,
    maximalOrderUnitsResidueClassMap_image_card _ s hneg hm hs] at hc
  have hw : (orderUnitCount (-(d : ℤ)) : ℝ) ≠ 0 := by
    unfold orderUnitCount
    split <;> norm_num
    split <;> norm_num
  have he : -((d * s ^ 2 : ℕ) : ℤ) = -(d : ℤ) * (s : ℤ) ^ 2 := by push_cast; ring
  rw [he]
  apply (eq_div_iff hw).mpr
  rw [div_mul_eq_mul_div]
  simpa only [mul_div_assoc] using hc.symm

theorem primitiveForm_integerIdeal_mem {D : ℤ} (f : PrimitivePositiveForm D) (I : Ideal ℤ)
    (haa : f.a * f.a ∈ I) (hab : f.a * f.b ∈ I) (hac : f.a * f.c ∈ I) :
    f.a ∈ I := by
  have hg : f.a * (Int.gcd f.b f.c : ℤ) ∈ I := by
    have h := I.add_mem (I.mul_mem_left (Int.gcdA f.b f.c) hab)
      (I.mul_mem_left (Int.gcdB f.b f.c) hac)
    have he := Int.gcd_eq_gcd_ab f.b f.c
    convert h using 1
    rw [he]
    ring
  have h := I.add_mem (I.mul_mem_left (Int.gcdA f.a (Int.gcd f.b f.c : ℤ)) haa)
    (I.mul_mem_left (Int.gcdB f.a (Int.gcd f.b f.c : ℤ)) hg)
  have he := Int.gcd_eq_gcd_ab f.a (Int.gcd f.b f.c : ℤ)
  rw [f.primitive] at he
  norm_num only [Nat.cast_one] at he
  convert h using 1
  linear_combination f.a * he

theorem formOrderIdeal_eq_span {D : ℤ} (f : PrimitivePositiveForm D) :
    formOrderIdeal f =
      Ideal.span {(f.a : DiscriminantOrder D),
        (⟨formOrderShift f, 1⟩ : DiscriminantOrder D)} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, y, rfl⟩ := (formOrderIdeal_lattice f z).mp hz
    have he : (⟨f.a * x + formOrderShift f * y, y⟩ : DiscriminantOrder D) =
        (x : DiscriminantOrder D) * (f.a : DiscriminantOrder D) +
          (y : DiscriminantOrder D) * (⟨formOrderShift f, 1⟩ : DiscriminantOrder D) := by
      ext <;> simp [mul_comm]
    rw [he]
    apply Ideal.add_mem
    · apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)
    · apply Ideal.mul_mem_left
      exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact (formOrderIdeal_basis_mem f).1
    · exact (formOrderIdeal_basis_mem f).2

def conjugateFormOrderIdeal {D : ℤ} (f : PrimitivePositiveForm D) : Ideal (DiscriminantOrder D) :=
  Ideal.span {(f.a : DiscriminantOrder D),
    star (⟨formOrderShift f, 1⟩ : DiscriminantOrder D)}
theorem formOrderIdeal_mul_conjugate {D : ℤ} (f : PrimitivePositiveForm D) :
    formOrderIdeal f * conjugateFormOrderIdeal f =
      Ideal.span {(f.a : DiscriminantOrder D)} := by
  let β : DiscriminantOrder D := ⟨formOrderShift f, 1⟩
  have hb : β + star β = (f.b : DiscriminantOrder D) := by
    ext
    · change formOrderShift f + (formOrderShift f + D % 4 * 1) = f.b
      linear_combination formOrderShift_relation f
    · simp [β]
  have hn : β * star β = (f.a * f.c : ℤ) := by
    have hn0 : QuadraticAlgebra.norm β = f.a * f.c := by
      change formOrderShift f * formOrderShift f + (D % 4) * formOrderShift f * 1 -
        ((D - D % 4) / 4) * 1 * 1 = f.a * f.c
      simpa [pow_two] using formOrderShift_norm_relation f
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn0]
    simp
  have hia : (f.a : DiscriminantOrder D) ∈ formOrderIdeal f := by
    rw [mem_formOrderIdeal]
    simp
  have hca : (f.a : DiscriminantOrder D) ∈ conjugateFormOrderIdeal f :=
    Ideal.subset_span (by simp)
  have hcb : star β ∈ conjugateFormOrderIdeal f :=
    Ideal.subset_span (by simp [β])
  let P := formOrderIdeal f * conjugateFormOrderIdeal f
  have ha : (f.a : DiscriminantOrder D) ∈ P := by
    apply primitiveForm_integerIdeal_mem f (Ideal.comap (algebraMap ℤ _) P)
    · change (algebraMap ℤ (DiscriminantOrder D)) (f.a * f.a) ∈ P
      rw [map_mul]
      exact Ideal.mul_mem_mul hia hca
    · change (algebraMap ℤ (DiscriminantOrder D)) (f.a * f.b) ∈ P
      rw [map_mul]
      change (f.a * f.b : DiscriminantOrder D) ∈ P
      rw [← hb, mul_add]
      exact Ideal.add_mem P
        (by
          rw [mul_comm]
          exact Ideal.mul_mem_mul (formOrderIdeal_basis_mem f).2 hca)
        (Ideal.mul_mem_mul hia hcb)
    · change (algebraMap ℤ (DiscriminantOrder D)) (f.a * f.c) ∈ P
      change ((f.a * f.c : ℤ) : DiscriminantOrder D) ∈ P
      rw [← hn]
      exact Ideal.mul_mem_mul (formOrderIdeal_basis_mem f).2 hcb
  apply le_antisymm
  · rw [formOrderIdeal_eq_span, conjugateFormOrderIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · change β * star β ∈ Ideal.span {(f.a : DiscriminantOrder D)}
      rw [hn, Int.cast_mul, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ha
theorem ideal_isUnit_of_mul_eq_span {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : Ideal R) {a : R} (ha : a ≠ 0) (h : I * J = Ideal.span {a}) :
    IsUnit (I : FractionalIdeal (nonZeroDivisors R) K) := by
  have haK : algebraMap R K a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha)
  have hp : IsUnit ((I : FractionalIdeal (nonZeroDivisors R) K) *
      (J : FractionalIdeal (nonZeroDivisors R) K)) := by
    rw [← FractionalIdeal.coeIdeal_mul, h, FractionalIdeal.coeIdeal_span_singleton]
    exact ⟨toPrincipalIdeal R K (Units.mk0 (algebraMap R K a) haK), by simp⟩
  exact (IsUnit.mul_iff.mp hp).1
theorem formOrderIdeal_isUnit {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f : PrimitivePositiveForm D) :
    IsUnit (formOrderIdeal f :
      FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)) := by
  apply ideal_isUnit_of_mul_eq_span (formOrderIdeal f) (conjugateFormOrderIdeal f)
      (a := (f.a : DiscriminantOrder D))
  · intro h
    have hr := congrArg QuadraticAlgebra.re h
    exact f.positive.ne' (by simpa using hr)
  · exact formOrderIdeal_mul_conjugate f

def generalFormIdealUnit {D : ℤ} [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (f : PrimitivePositiveForm D) :
    (FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D))ˣ :=
  (formOrderIdeal_isUnit f).unit

theorem generalFormIdealUnit_val {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f : PrimitivePositiveForm D) :
    (generalFormIdealUnit f :
      FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)) =
      formOrderIdeal f := IsUnit.unit_spec _

def generalFormIdealClass {D : ℤ} [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)]
    (f : PrimitivePositiveForm D) : ClassGroup (DiscriminantOrder D) :=
  ClassGroup.mk (DiscriminantField D) (generalFormIdealUnit f)

theorem classGroup_unit_eq_iff_scalar {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔ ∃ z : K, z ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors R) z * (I : FractionalIdeal _ K) =
        (J : FractionalIdeal _ K) := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk, QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff,
    Units.ext_iff, Units.val_mul, FractionalIdeal.canonicalEquiv_self,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl
      simp [X.ne_zero.symm] at hX
    simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, h⟩
    refine ⟨toPrincipalIdeal R K (Units.mk0 x hx), ⟨x, by simp⟩, ?_⟩
    simpa only [coe_toPrincipalIdeal, Units.val_mk0, mul_comm] using h

theorem generalFormIdealClass_eq_iff {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (f g : PrimitivePositiveForm D) :
    generalFormIdealClass f = generalFormIdealClass g ↔ properChange f g := by
  rw [generalFormIdealClass, generalFormIdealClass, classGroup_unit_eq_iff_scalar]
  simp only [generalFormIdealUnit_val]
  constructor
  · rintro ⟨z, hz, he⟩
    exact properChange_of_ideal_fractional_eq f g z hz he
  · exact properChange_ideal_fractional_eq f g
def generalFormClassToIdealClass {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] : FormClass D → ClassGroup (DiscriminantOrder D) :=
  Quotient.lift generalFormIdealClass fun f g hfg =>
    generalFormIdealClass_eq_iff f g |>.mpr ((properChange_eqvGen_iff f g).mp hfg)

theorem generalFormClassToIdealClass_injective {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    Function.Injective (generalFormClassToIdealClass (D := D)) := by
  intro x y h
  induction x using Quotient.inductionOn with | _ f =>
    induction y using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      exact Relation.EqvGen.rel f g ((generalFormIdealClass_eq_iff f g).mp h)
theorem invertibleFractionalIdeal_multiplier_mem {R K : Type*} [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal (nonZeroDivisors R) K) (hI : IsUnit I) (z : K)
    (h : FractionalIdeal.spanSingleton (nonZeroDivisors R) z * I ≤ I) :
    z ∈ (1 : FractionalIdeal (nonZeroDivisors R) K) := by
  obtain ⟨u, rfl⟩ := hI
  have hh : (FractionalIdeal.spanSingleton (nonZeroDivisors R) z *
        (u : FractionalIdeal (nonZeroDivisors R) K)) *
        (↑(u⁻¹) : FractionalIdeal (nonZeroDivisors R) K) ≤
      (u : FractionalIdeal (nonZeroDivisors R) K) *
        (↑(u⁻¹) : FractionalIdeal (nonZeroDivisors R) K) := by
    gcongr
  apply FractionalIdeal.spanSingleton_le_iff_mem.mp
  simpa only [mul_assoc, Units.val_inv_eq_inv_val, Units.val_mul,
    Units.mul_inv, Units.val_one, mul_one] using hh
theorem normalizedIdeal_primitive_of_invertible {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] (I : Ideal (DiscriminantOrder D))
    (hI : IsUnit (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D))) (g a h c : ℤ) (ha : 0 < a)
    (hn : h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c)
    (hL : ∀ z : DiscriminantOrder D, z ∈ I ↔
      ∃ x y : ℤ, z = ⟨g * (a * x + h * y), g * y⟩) :
    Int.gcd a (Int.gcd (2 * h + D % 4) c : ℤ) = 1 := by
  let k := Int.gcd a (Int.gcd (2 * h + D % 4) c : ℤ)
  have hk : 0 < k := Int.gcd_pos_of_ne_zero_left _ ha.ne'
  have hka : (k : ℤ) ∣ a := Int.gcd_dvd_left _ _
  have hkb : (k : ℤ) ∣ 2 * h + D % 4 :=
    (Int.gcd_dvd_right a (Int.gcd (2 * h + D % 4) c : ℤ)).trans
      (Int.gcd_dvd_left _ _)
  have hkc : (k : ℤ) ∣ c :=
    (Int.gcd_dvd_right a (Int.gcd (2 * h + D % 4) c : ℤ)).trans
      (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha'⟩ := hka
  obtain ⟨b', hb'⟩ := hkb
  obtain ⟨c', hc'⟩ := hkc
  let j := algebraMap (DiscriminantOrder D) (DiscriminantField D)
  let β : DiscriminantOrder D := ⟨h, 1⟩
  let z : DiscriminantField D := j β / (k : DiscriminantField D)
  have hkF : (k : DiscriminantField D) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hv (x y : ℤ) :
      β * (⟨g * (a * x + h * y), g * y⟩ : DiscriminantOrder D) =
      (k : DiscriminantOrder D) *
        (⟨g * (a * (-c' * y) + h * (a' * x + b' * y)),
          g * (a' * x + b' * y)⟩ : DiscriminantOrder D) := by
    ext
    · simp only [β, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, mul_zero]
      linear_combination (g * x * h) * ha' + (g * h * y) * hb' -
        (g * a * y) * hc' - (g * y) * hn
    · simp only [β, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, mul_zero]
      linear_combination (g * x) * ha' + (g * y) * hb'
  have hzm : z ∈ (1 : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D)) := by
    apply invertibleFractionalIdeal_multiplier_mem _ hI
    apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
    intro w hw
    obtain ⟨v, hvI, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    obtain ⟨x, y, rfl⟩ := (hL v).mp hvI
    let v' : DiscriminantOrder D :=
      ⟨g * (a * (-c' * y) + h * (a' * x + b' * y)), g * (a' * x + b' * y)⟩
    have he : z * j (⟨g * (a * x + h * y), g * y⟩ : DiscriminantOrder D) = j v' := by
      apply (div_mul_eq_mul_div _ _ _).trans
      apply (div_eq_iff hkF).mpr
      have hh := congrArg j (hv x y)
      rw [map_mul, map_mul, map_natCast] at hh
      simpa only [v', mul_comm] using hh
    rw [he]
    exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨v', (hL v').mpr ⟨-c' * y,
      a' * x + b' * y, rfl⟩, rfl⟩
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).mp hzm
  have he : (k : ℚ) * (v.im : ℚ) = 1 := by
    have hh := congrArg QuadraticAlgebra.im ((eq_div_iff hkF).mp hv)
    change (v.re : ℚ) * 0 + (v.im : ℚ) * (k : ℚ) +
      ((D % 4 : ℤ) : ℚ) * (v.im : ℚ) * 0 = 1 at hh
    simpa [mul_comm] using hh
  have heZ : (k : ℤ) * v.im = 1 := by exact_mod_cast he
  have hkZ : 0 < (k : ℤ) := Nat.cast_pos.mpr hk
  have hvpos : 0 < v.im := by
    by_contra hv0
    have hh := mul_nonpos_of_nonneg_of_nonpos hkZ.le (le_of_not_gt hv0)
    omega
  have hkle : (k : ℤ) ≤ 1 := by
    calc
      (k : ℤ) = (k : ℤ) * 1 := by ring
      _ ≤ (k : ℤ) * v.im := mul_le_mul_of_nonneg_left (by omega) hkZ.le
      _ = 1 := heZ
  have hk1 : (k : ℤ) = 1 := by omega
  exact_mod_cast hk1
def formOfPrimitiveNormalizedIdeal (D a h c : ℤ) (ha : 0 < a)
    (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hn : h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c)
    (hp : Int.gcd a (Int.gcd (2 * h + D % 4) c : ℤ) = 1) :
    PrimitivePositiveForm D where
  a := a
  b := 2 * h + D % 4
  c := c
  positive := ha
  discriminant := by
    have hd := discriminantOrder_discr D hm
    nlinarith [hn]
  primitive := hp

theorem formOfPrimitiveNormalizedIdeal_shift (D a h c : ℤ)
    (ha : 0 < a) (hm : D % 4 = 0 ∨ D % 4 = 1)
    (hn : h ^ 2 + (D % 4) * h - (D - D % 4) / 4 = a * c)
    (hp : Int.gcd a (Int.gcd (2 * h + D % 4) c : ℤ) = 1) :
    formOrderShift (formOfPrimitiveNormalizedIdeal D a h c ha hm hn hp) = h := by
  simp [formOrderShift, formOfPrimitiveNormalizedIdeal]

theorem invertibleDiscriminantIdeal_eq_scaled_form {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] 
    (I : Ideal (DiscriminantOrder D)) (hI : I ≠ ⊥)
    (hInv : IsUnit (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D))) :
    ∃ f : PrimitivePositiveForm D, ∃ g : ℤ, 0 < g ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (DiscriminantOrder D))
        (g : DiscriminantField D) *
        (formOrderIdeal f : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
          (DiscriminantField D)) =
      (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
        (DiscriminantField D)) := by
  obtain ⟨g, a, h, c, hg, ha, hn, hL⟩ := discriminantIdeal_normalized_basis I hI
  have hp := normalizedIdeal_primitive_of_invertible I hInv g a h c ha hn hL
  let f := formOfPrimitiveNormalizedIdeal D a h c ha Fact.out hn hp
  let j := algebraMap (DiscriminantOrder D) (DiscriminantField D)
  have hfa : f.a = a := rfl
  have hfh : formOrderShift f = h :=
    formOfPrimitiveNormalizedIdeal_shift D a h c ha Fact.out hn hp
  have hv : ∀ v : Fin 2 → ℤ,
      (g : DiscriminantOrder D) * formOrderVector f v =
        ⟨g * (a * v 0 + h * v 1), g * v 1⟩ := by
    intro v
    apply QuadraticAlgebra.ext <;> simp [formOrderVector, hfa, hfh]
  refine ⟨f, g, hg, ?_⟩
  symm
  apply FractionalIdeal.eq_spanSingleton_mul.mpr
  constructor
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨u, v, rfl⟩ := (hL x).mp hx
    refine ⟨j (formOrderVector f ![u, v]),
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, formOrderVector_mem f _, rfl⟩, ?_⟩
    rw [← map_intCast j g, ← map_mul, hv]
    rfl
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨v, rfl⟩ := formOrderVector_surjective f x hx
    refine (FractionalIdeal.mem_coeIdeal _).mpr
      ⟨(g : DiscriminantOrder D) * formOrderVector f v,
        (hL _).mpr ⟨v 0, v 1, hv v⟩, ?_⟩
    rw [map_mul, map_intCast]

theorem invertibleFractionalIdeal_num_isUnit {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (U : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    IsUnit ((U : FractionalIdeal (nonZeroDivisors R) K).num :
      FractionalIdeal (nonZeroDivisors R) K) := by
  let δ : K := algebraMap R K (U : FractionalIdeal (nonZeroDivisors R) K).den
  have hδ : δ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (U : FractionalIdeal (nonZeroDivisors R) K).den.prop
  have hp : IsUnit (FractionalIdeal.spanSingleton (nonZeroDivisors R) δ) :=
    ⟨toPrincipalIdeal R K (Units.mk0 δ hδ), by simp⟩
  rw [← FractionalIdeal.den_mul_self_eq_num']
  exact hp.mul U.isUnit

theorem generalFormClassToIdealClass_surjective {D : ℤ} [Fact (D < 0)]
      [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
    Function.Surjective (generalFormClassToIdealClass (D := D)) := by
  intro C
  refine ClassGroup.induction (R := DiscriminantOrder D) (DiscriminantField D) ?_ C
  intro U
  let I : Ideal (DiscriminantOrder D) :=
    (U : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)).num
  have hI : I ≠ ⊥ := by
    change (U : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D)).num ≠ 0
    exact mt FractionalIdeal.num_eq_zero_iff.mp U.ne_zero
  have hInv : IsUnit (I : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D)) := invertibleFractionalIdeal_num_isUnit U
  obtain ⟨f, g, hg, heq⟩ := invertibleDiscriminantIdeal_eq_scaled_form I hI hInv
  refine ⟨Quotient.mk _ f, ?_⟩
  change generalFormIdealClass f = ClassGroup.mk (DiscriminantField D) U
  have hFI : generalFormIdealClass f =
      ClassGroup.mk (DiscriminantField D) hInv.unit :=
    (classGroup_unit_eq_iff_scalar (generalFormIdealUnit f) hInv.unit).mpr
      ⟨(g : DiscriminantField D), Int.cast_ne_zero.mpr hg.ne', by
        simpa only [generalFormIdealUnit_val, IsUnit.unit_spec] using heq⟩
  rw [hFI]
  symm
  apply (classGroup_unit_eq_iff_scalar U hInv.unit).mpr
  let δ := algebraMap (DiscriminantOrder D) (DiscriminantField D)
    (U : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D)) (DiscriminantField D)).den
  refine ⟨δ, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (U : FractionalIdeal (nonZeroDivisors (DiscriminantOrder D))
      (DiscriminantField D)).den.prop, ?_⟩
  rw [IsUnit.unit_spec]
  exact FractionalIdeal.den_mul_self_eq_num' _ _ U.val

def generalFormClassEquivIdealClass {D : ℤ} [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] : FormClass D ≃ ClassGroup (DiscriminantOrder D) :=
  Equiv.ofBijective generalFormClassToIdealClass
    ⟨generalFormClassToIdealClass_injective, generalFormClassToIdealClass_surjective⟩

theorem orderClassNumber_eq_orderIdealClassNumber (D : ℤ) [Fact (D < 0)]
    [Fact (D % 4 = 0 ∨ D % 4 = 1)] :
  orderClassNumber D = Nat.card (ClassGroup (DiscriminantOrder D)) :=
  Nat.card_congr generalFormClassEquivIdealClass
def classGroupExtension {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) :
    ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom' (FractionRing B)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map hf (α : FractionRing A)) (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0, IsFractionRing.map] using
        (FractionalIdeal.extended_spanSingleton (FractionRing B) _ _).symm)

theorem classGroupExtension_quotientMk {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f)
    (U : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ) :
    classGroupExtension f hf (QuotientGroup.mk U) = QuotientGroup.mk
      (Units.map (FractionalIdeal.extendedHom' (FractionRing B)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom U) := rfl

theorem classGroupExtension_mk {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f)
    (U : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ) :
    classGroupExtension f hf (ClassGroup.mk (FractionRing A) U) =
      ClassGroup.mk (FractionRing B)
        (Units.map (FractionalIdeal.extendedHom' (FractionRing B)
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom U) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  rfl
def conductorFieldEmbedding (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) :
    DiscriminantField (D * (s : ℤ) ^ 2) →ₐ[ℚ] DiscriminantField D :=
  QuadraticAlgebra.lift ⟨⟨(conductorOrderShift D s : ℚ), (s : ℚ)⟩, by
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_smul, QuadraticAlgebra.re_one, smul_eq_mul, mul_one]
      change (conductorOrderShift D s : ℚ) * conductorOrderShift D s +
        (((D - D % 4) / 4 : ℤ) : ℚ) * (s : ℚ) * s =
        (((D * (s : ℤ) ^ 2 - (D * (s : ℤ) ^ 2) % 4) / 4 : ℤ) : ℚ) +
          (((D * (s : ℤ) ^ 2) % 4 : ℤ) : ℚ) * conductorOrderShift D s
      have he := conductorOrderShift_polynomial_relation D s hm
      exact_mod_cast (by simpa only [pow_two, mul_assoc, Nat.cast_mul] using he)
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_smul, QuadraticAlgebra.im_one, smul_eq_mul, mul_zero, zero_add]
      change (conductorOrderShift D s : ℚ) * s +
        (s : ℚ) * conductorOrderShift D s + (D % 4 : ℤ) * (s : ℚ) * s =
          (((D * (s : ℤ) ^ 2) % 4 : ℤ) : ℚ) * s
      have he : conductorOrderShift D s * (s : ℤ) +
          (s : ℤ) * conductorOrderShift D s + (D % 4) * (s : ℤ) * s =
          (D * (s : ℤ) ^ 2) % 4 * s := by
        linear_combination (s : ℤ) * conductorOrderShift_relation D s hm
      exact_mod_cast he⟩

theorem conductorFieldEmbedding_apply (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) (z : DiscriminantField (D * (s : ℤ) ^ 2)) :
    conductorFieldEmbedding D s hm z =
      (⟨z.re + (conductorOrderShift D s : ℚ) * z.im, (s : ℚ) * z.im⟩ :
        DiscriminantField D) := by
  ext <;> simp [conductorFieldEmbedding, QuadraticAlgebra.lift_apply_apply,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring

def conductorFieldEquiv (D : ℤ) (s : ℕ) (hm : D % 4 = 0 ∨ D % 4 = 1) (hs : 0 < s) :
    DiscriminantField (D * (s : ℤ) ^ 2) ≃ₐ[ℚ] DiscriminantField D :=
  AlgEquiv.ofBijective (conductorFieldEmbedding D s hm) (by
    have hsQ : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    constructor
    · intro z w he
      rw [conductorFieldEmbedding_apply, conductorFieldEmbedding_apply] at he
      have hi := congrArg QuadraticAlgebra.im he
      have hr := congrArg QuadraticAlgebra.re he
      have him : z.im = w.im := mul_left_cancel₀ hsQ hi
      ext
      · change z.re + (conductorOrderShift D s : ℚ) * z.im =
          w.re + (conductorOrderShift D s : ℚ) * w.im at hr
        rw [him] at hr
        exact add_right_cancel hr
      · exact him
    · intro z
      refine ⟨⟨z.re - (conductorOrderShift D s : ℚ) * (z.im / s), z.im / s⟩, ?_⟩
      rw [conductorFieldEmbedding_apply]
      ext
      · simp
      · simp [div_eq_mul_inv, mul_left_comm, hsQ])

theorem conductorFieldEmbedding_order (D : ℤ) (s : ℕ)
    (hm : D % 4 = 0 ∨ D % 4 = 1) (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    conductorFieldEmbedding D s hm
        (integralQuadraticOrderEmbedding _ _ z) =
      integralQuadraticOrderEmbedding _ _ (conductorOrderEmbedding D s hm z) := by
  rw [conductorFieldEmbedding_apply, conductorOrderEmbedding_apply]
  ext <;> simp [integralQuadraticOrderEmbedding]
section ConductorClassSequence

variable (D : ℤ) (s : ℕ) [Fact (D < 0)]
  [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

local instance conductorOrderNegativeDiscriminant : Fact (D * (s : ℤ) ^ 2 < 0) := by
  constructor
  have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
  exact mul_neg_of_neg_of_pos Fact.out (sq_pos_of_ne_zero hs)

local instance conductorOrderDiscriminantModFour :
    Fact ((D * (s : ℤ) ^ 2) % 4 = 0 ∨ (D * (s : ℤ) ^ 2) % 4 = 1) :=
  ⟨conductorDiscriminant_mod_four D s Fact.out⟩

def conductorClassGroupMap :
    ClassGroup (DiscriminantOrder (D * (s : ℤ) ^ 2)) →*
      ClassGroup (DiscriminantOrder D) :=
  classGroupExtension (conductorOrderEmbedding D s Fact.out).toRingHom
    (conductorOrderEmbedding_injective D s Fact.out (Nat.pos_of_ne_zero (NeZero.ne s)))

local instance conductorOrderMaximalFieldAlgebra :
    Algebra (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantField D) :=
  ((integralQuadraticOrderEmbedding _ _).comp
    (conductorOrderEmbedding D s Fact.out).toRingHom).toAlgebra

local instance conductorOrderMaximalFieldFaithful :
    FaithfulSMul (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantField D) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((integralQuadraticOrderEmbedding_injective _ _).comp
      (conductorOrderEmbedding_injective D s Fact.out (Nat.pos_of_ne_zero (NeZero.ne s))))

omit [Fact (D < 0)] [NeZero s] in
theorem conductorOrderMaximalField_algebraMap
    (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantField D) z =
      conductorFieldEmbedding D s Fact.out
        (integralQuadraticOrderEmbedding _ _ z) :=
  (conductorFieldEmbedding_order D s Fact.out z).symm

local instance conductorOrderMaximalFieldFractionRing :
    IsFractionRing (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantField D) :=
  IsFractionRing.of_field _ _ fun z => by
    let e := conductorFieldEquiv D s Fact.out (Nat.pos_of_ne_zero (NeZero.ne s))
    obtain ⟨x, y, hy, hz⟩ := integralQuadraticOrder_clear_denominators _ _ (e.symm z)
    refine ⟨x, y, ?_⟩
    apply (eq_div_iff ?_).mpr
    · have hh := congrArg e hz
      change e (e.symm z * integralQuadraticOrderEmbedding _ _ y) =
        e (integralQuadraticOrderEmbedding _ _ x) at hh
      rw [map_mul, e.apply_symm_apply] at hh
      change z * conductorFieldEmbedding D s Fact.out
          (integralQuadraticOrderEmbedding _ _ y) =
        conductorFieldEmbedding D s Fact.out
          (integralQuadraticOrderEmbedding _ _ x) at hh
      simpa only [conductorOrderMaximalField_algebraMap] using hh
    · intro h
      exact hy ((FaithfulSMul.algebraMap_injective
        (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantField D))
          (by simpa only [map_zero] using h))

end ConductorClassSequence
def conductorPatchModule {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] (q : B →+* C) (u : Cˣ) : Submodule A B where
  carrier := {z | ∃ a : A, q z = (u : C) * q (algebraMap A B a)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simp [ha, hb, mul_add]⟩
  smul_mem' := by
    rintro a z ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp only [Algebra.smul_def, map_mul, hb]
    ring

theorem conductorPatchModule_mem {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] (q : B →+* C) (u : Cˣ) (z : B) :
    z ∈ conductorPatchModule (A := A) q u ↔ ∃ a : A,
      q z = (u : C) * q (algebraMap A B a) := Iff.rfl

theorem conductorPatchModule_mem_of_ker {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (u : Cˣ) {z : B} (hz : q z = 0) :
    z ∈ conductorPatchModule (A := A) q u := ⟨0, by simp [hz]⟩

theorem conductorPatchModule_mem_of_lift {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (u : Cˣ) {z : B}
    (hz : q z = (u : C)) : z ∈ conductorPatchModule (A := A) q u := ⟨1, by simp [hz]⟩

theorem conductorPatchModule_mul_le {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (u v : Cˣ) :
    conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v ≤ conductorPatchModule (A := A) q (u * v) := by
  apply Submodule.mul_le.mpr
  rintro x ⟨a, ha⟩ y ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  simp only [map_mul, ha, hb, Units.val_mul]
  ring

theorem conductorPatchModule_ker_le_mul {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (hq : Function.Surjective q) (u v : Cˣ) :
    ∀ z : B, q z = 0 → z ∈ conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v := by
  obtain ⟨x, hx⟩ := hq (u : C)
  obtain ⟨y, hy⟩ := hq (u⁻¹ : Cˣ)
  have hxU := conductorPatchModule_mem_of_lift (A := A) q u hx
  have hf : q (1 - x * y) = 0 := by simp [hx, hy]
  intro z hz
  have hzy : q (z * y) = 0 := by simp [hz]
  have h₁ : x * (z * y) ∈ conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v :=
    Submodule.mul_mem_mul hxU (conductorPatchModule_mem_of_ker (A := A) q v hzy)
  have h₂ : z * (1 - x * y) ∈ conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v :=
    Submodule.mul_mem_mul (conductorPatchModule_mem_of_ker (A := A) q u hz)
      (conductorPatchModule_mem_of_ker (A := A) q v hf)
  have he : z = x * (z * y) + z * (1 - x * y) := by ring
  rw [he]
  exact Submodule.add_mem _ h₁ h₂

theorem conductorPatchModule_mul {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (hq : Function.Surjective q) (u v : Cˣ) :
    conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v = conductorPatchModule (A := A) q (u * v) := by
  apply le_antisymm (conductorPatchModule_mul_le (A := A) q u v)
  obtain ⟨x, hx⟩ := hq (u : C)
  obtain ⟨y, hy⟩ := hq (v : C)
  have hxy := Submodule.mul_mem_mul (conductorPatchModule_mem_of_lift (A := A) q u hx)
    (conductorPatchModule_mem_of_lift (A := A) q v hy)
  rintro z ⟨a, ha⟩
  have hdiff : q (z - algebraMap A B a * (x * y)) = 0 := by
    simp only [map_sub, map_mul, hx, hy, ha, Units.val_mul]
    ring
  have hm : algebraMap A B a * (x * y) ∈
      conductorPatchModule (A := A) q u * conductorPatchModule (A := A) q v := by
    simpa only [Algebra.smul_def] using Submodule.smul_mem _ a hxy
  have hd := conductorPatchModule_ker_le_mul (A := A) q hq u v _ hdiff
  have he : z = (z - algebraMap A B a * (x * y)) + algebraMap A B a * (x * y) := by ring
  rw [he]
  exact Submodule.add_mem _ hd hm

theorem conductorPatchModule_one {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) :
    conductorPatchModule (A := A) q 1 = 1 := by
  ext z
  rw [conductorPatchModule_mem, Submodule.mem_one]
  constructor
  · rintro ⟨a, ha⟩
    have hh : q (z - algebraMap A B a) = 0 := by simp [map_sub, ha]
    obtain ⟨b, hb⟩ := hker _ hh
    refine ⟨a + b, ?_⟩
    rw [map_add, hb]
    ring
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

def conductorPatchUnit {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (hq : Function.Surjective q)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) (u : Cˣ) :
    (Submodule A B)ˣ where
  val := conductorPatchModule (A := A) q u
  inv := conductorPatchModule (A := A) q u⁻¹
  val_inv := by rw [conductorPatchModule_mul (A := A) q hq, mul_inv_cancel, conductorPatchModule_one (A := A) q hker]
  inv_val := by rw [conductorPatchModule_mul (A := A) q hq, inv_mul_cancel, conductorPatchModule_one (A := A) q hker]

def conductorPatchUnitHom {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C) (hq : Function.Surjective q)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) :
    Cˣ →* (Submodule A B)ˣ where
  toFun := conductorPatchUnit q hq hker
  map_one' := by
    apply Units.ext
    exact conductorPatchModule_one (A := A) q hker
  map_mul' u v := by
    apply Units.ext
    exact (conductorPatchModule_mul (A := A) q hq u v).symm
theorem conductorPatchModule_of_unit {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) (v : Bˣ) :
    conductorPatchModule (A := A) q (Units.map q.toMonoidHom v) =
      Submodule.spanSingleton A (v : B) := by
  ext z
  rw [conductorPatchModule_mem, Submodule.spanSingleton_apply,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    have hh : q ((v⁻¹ : Bˣ) * z - algebraMap A B a) = 0 := by
      simp only [map_sub, map_mul] 
      change q (↑(v⁻¹) : B) * q z - q (algebraMap A B a) = 0
      change q z = q (v : B) * q (algebraMap A B a) at ha
      rw [ha, ← mul_assoc, ← map_mul]
      simp
    obtain ⟨b, hb⟩ := hker _ hh
    refine ⟨a + b, ?_⟩
    rw [Algebra.smul_def, map_add, hb]
    simp only [add_sub_cancel]
    calc
      (↑(v⁻¹) : B) * z * v = z * ((↑(v⁻¹) : B) * v) := by ring
      _ = z := by rw [Units.inv_mul, mul_one]
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [Algebra.smul_def, map_mul, Units.coe_map]
    change q (algebraMap A B a) * q (v : B) = q (v : B) * q (algebraMap A B a)
    ring

def conductorPatchPicHom {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [FaithfulSMul A B] (q : B →+* C) (hq : Function.Surjective q)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) :
    Cˣ →* CommRing.Pic A :=
  (Submodule.unitsToPic A B).comp (conductorPatchUnitHom q hq hker)

theorem conductorPatchPicHom_unit {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [FaithfulSMul A B] (q : B →+* C) (hq : Function.Surjective q)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) (v : Bˣ) :
    conductorPatchPicHom q hq hker (Units.map q.toMonoidHom v) = 1 := by
  change conductorPatchUnit q hq hker (Units.map q.toMonoidHom v) ∈
    (Submodule.unitsToPic A B).ker
  rw [Submodule.ker_unitsToPic]
  refine ⟨v, ?_⟩
  apply Units.ext
  exact (conductorPatchModule_of_unit q hker v).symm
theorem discriminantOrderResidueMap_apply (D : ℤ) (s : ℕ) (z : DiscriminantOrder D) :
    discriminantOrderResidueMap D s z = ⟨(z.re : ZMod s), (z.im : ZMod s)⟩ := rfl

theorem residueDiscriminantScalarUnits_val (D : ℤ) (s : ℕ) (v : (ZMod s)ˣ) :
    (residueDiscriminantScalarUnits D s v : ResidueDiscriminantOrder D s) =
      ⟨(v : ZMod s), 0⟩ := by
  change algebraMap (ZMod s) (ResidueDiscriminantOrder D s) (v : ZMod s) = _
  exact QuadraticAlgebra.algebraMap_eq _
  
section ConductorPatch

variable (D : ℤ) (s : ℕ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

local instance conductorOrderMaximalOrderAlgebra :
    Algebra (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) :=
  (conductorOrderEmbedding D s Fact.out).toRingHom.toAlgebra

omit [NeZero s] in
theorem conductorOrderMaximalOrder_algebraMap
    (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) z =
      conductorOrderEmbedding D s Fact.out z := rfl

local instance conductorOrderMaximalOrderFaithful :
    FaithfulSMul (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (conductorOrderEmbedding_injective D s Fact.out (Nat.pos_of_ne_zero (NeZero.ne s)))

omit [NeZero s] in
theorem conductorResidue_kernel_in_order (z : DiscriminantOrder D)
    (hz : discriminantOrderResidueMap D s z = 0) :
    ∃ a : DiscriminantOrder (D * (s : ℤ) ^ 2),
      algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) a = z := by
  have hi := congrArg QuadraticAlgebra.im hz
  change (z.im : ZMod s) = 0 at hi
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z.im s).mp hi
  exact (conductorOrderEmbedding_range D s Fact.out z).mpr hd

def conductorResiduePicMap :
    (ResidueDiscriminantOrder D s)ˣ →*
      CommRing.Pic (DiscriminantOrder (D * (s : ℤ) ^ 2)) :=
  conductorPatchPicHom (discriminantOrderResidueMap D s)
    (discriminantOrderResidueMap_surjective D s) (conductorResidue_kernel_in_order D s)

theorem conductorResiduePicMap_order_unit (v : (DiscriminantOrder D)ˣ) :
    conductorResiduePicMap D s (Units.map (discriminantOrderResidueMap D s).toMonoidHom v) = 1 :=
  conductorPatchPicHom_unit _ _ _ v

omit [NeZero s] in
theorem conductorPatchModule_scalar (v : (ZMod s)ˣ) :
    conductorPatchModule (A := DiscriminantOrder (D * (s : ℤ) ^ 2))
      (discriminantOrderResidueMap D s) (residueDiscriminantScalarUnits D s v) = 1 := by
  ext z
  rw [conductorPatchModule_mem, Submodule.mem_one]
  constructor
  · rintro ⟨a, ha⟩
    rw [residueDiscriminantScalarUnits_val, conductorOrderMaximalOrder_algebraMap,
      conductorOrderEmbedding_apply] at ha
    have hi := congrArg QuadraticAlgebra.im ha
    change (z.im : ZMod s) = (v : ZMod s) *
      (((s : ℤ) * a.im : ℤ) : ZMod s) + 0 *
      (((a.re + conductorOrderShift D s * a.im : ℤ) : ZMod s)) +
      ((D % 4 : ℤ) : ZMod s) * 0 * (((s : ℤ) * a.im : ℤ) : ZMod s) at hi
    simp at hi
    exact (conductorOrderEmbedding_range D s Fact.out z).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd z.im s).mp hi)
  · rintro ⟨a, ha⟩
    have hi : (z.im : ZMod s) = 0 := by
      rw [conductorOrderMaximalOrder_algebraMap, conductorOrderEmbedding_apply] at ha
      have hh := congrArg QuadraticAlgebra.im ha
      change (s : ℤ) * a.im = z.im at hh
      rw [← hh]
      simp
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective ((↑(v⁻¹) : ZMod s) * (z.re : ZMod s))
    refine ⟨(⟨k, 0⟩ : DiscriminantOrder (D * (s : ℤ) ^ 2)), ?_⟩
    rw [residueDiscriminantScalarUnits_val, conductorOrderMaximalOrder_algebraMap,
      conductorOrderEmbedding_apply]
    simp only [mul_zero, add_zero]
    rw [discriminantOrderResidueMap_apply, discriminantOrderResidueMap_apply]
    ext
    · simp only [QuadraticAlgebra.re_mul, Int.cast_zero, mul_zero, add_zero]
      rw [hk, ← mul_assoc, Units.mul_inv, one_mul]
    · simpa only [QuadraticAlgebra.im_mul, mul_zero, zero_mul, Int.cast_zero,
        zero_add, add_zero] using hi

theorem conductorResiduePicMap_scalar (v : (ZMod s)ˣ) :
    conductorResiduePicMap D s (residueDiscriminantScalarUnits D s v) = 1 := by
  change (Submodule.unitsToPic _ _)
    (conductorPatchUnit (discriminantOrderResidueMap D s)
      (discriminantOrderResidueMap_surjective D s)
      (conductorResidue_kernel_in_order D s) (residueDiscriminantScalarUnits D s v)) = 1
  have he : conductorPatchUnit (A := DiscriminantOrder (D * (s : ℤ) ^ 2))
      (discriminantOrderResidueMap D s) (discriminantOrderResidueMap_surjective D s)
      (conductorResidue_kernel_in_order D s) (residueDiscriminantScalarUnits D s v) = 1 := by
    apply Units.ext
    exact conductorPatchModule_scalar D s v
  rw [he, map_one]

def conductorResidueClassPicMap :
    ConductorResidueClassGroup D s →*
      CommRing.Pic (DiscriminantOrder (D * (s : ℤ) ^ 2)) :=
  QuotientGroup.lift _ (conductorResiduePicMap D s) (by
    rintro _ ⟨v, rfl⟩
    exact conductorResiduePicMap_scalar D s v)

end ConductorPatch
section ConductorPatchKernel

variable (D : ℤ) (s : ℕ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

attribute [local instance] conductorOrderMaximalOrderAlgebra conductorOrderMaximalOrderFaithful

local instance conductorPatchUnitImageNormal :
    (maximalOrderUnitsResidueClassMap D s).range.Normal :=
  letI : CommGroup (ConductorResidueClassGroup D s) := inferInstance
  Subgroup.normal_of_isMulCommutative _

theorem conductorResidueClassPicMap_order_unit (v : (DiscriminantOrder D)ˣ) :
    conductorResidueClassPicMap D s (maximalOrderUnitsResidueClassMap D s v) = 1 := by
  change conductorResiduePicMap D s
    (Units.map (discriminantOrderResidueMap D s).toMonoidHom v) = 1
  exact conductorResiduePicMap_order_unit D s v

theorem conductorResidueClassPicMap_kernel :
    (conductorResidueClassPicMap D s).ker = (maximalOrderUnitsResidueClassMap D s).range := by
  ext x
  constructor
  · intro hx
    induction x using QuotientGroup.induction_on with
    | H u =>
      change conductorResiduePicMap D s u = 1 at hx
      have hk : conductorPatchUnit (A := DiscriminantOrder (D * (s : ℤ) ^ 2))
          (discriminantOrderResidueMap D s) (discriminantOrderResidueMap_surjective D s)
          (conductorResidue_kernel_in_order D s) u ∈
          (Submodule.unitsToPic (DiscriminantOrder (D * (s : ℤ) ^ 2))
            (DiscriminantOrder D)).ker := hx
      rw [Submodule.ker_unitsToPic] at hk
      obtain ⟨v, hv⟩ := hk
      have hL := congrArg Units.val hv
      change Submodule.spanSingleton (DiscriminantOrder (D * (s : ℤ) ^ 2))
          (v : DiscriminantOrder D) =
        conductorPatchModule (A := DiscriminantOrder (D * (s : ℤ) ^ 2))
          (discriminantOrderResidueMap D s) u at hL
      obtain ⟨z, hz⟩ := discriminantOrderResidueMap_surjective D s (u : ResidueDiscriminantOrder D s)
      have hzL := conductorPatchModule_mem_of_lift
        (A := DiscriminantOrder (D * (s : ℤ) ^ 2)) _ u hz
      rw [← hL, Submodule.spanSingleton_apply, Submodule.mem_span_singleton] at hzL
      obtain ⟨a, ha⟩ := hzL
      have he : (u : ResidueDiscriminantOrder D s) =
          discriminantOrderResidueMap D s
            (algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) a) *
          discriminantOrderResidueMap D s (v : DiscriminantOrder D) := by
        rw [← hz, ← ha, Algebra.smul_def, map_mul]
      let w : (ResidueDiscriminantOrder D s)ˣ :=
        u * (Units.map (discriminantOrderResidueMap D s).toMonoidHom v)⁻¹
      have hw : (w : ResidueDiscriminantOrder D s) =
          discriminantOrderResidueMap D s
            (algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) a) := by
        change (u : ResidueDiscriminantOrder D s) *
          (↑((Units.map (discriminantOrderResidueMap D s).toMonoidHom v)⁻¹) :
            ResidueDiscriminantOrder D s) = _
        have hqu : discriminantOrderResidueMap D s (v : DiscriminantOrder D) =
            (Units.map (discriminantOrderResidueMap D s).toMonoidHom v :
              ResidueDiscriminantOrder D s) := rfl
        rw [he, hqu, mul_assoc, Units.mul_inv, mul_one]
      have hwi : (w : ResidueDiscriminantOrder D s).im = 0 := by
        rw [hw, conductorOrderMaximalOrder_algebraMap, conductorOrderEmbedding_apply,
          discriminantOrderResidueMap_apply]
        change (((s : ℤ) * a.im : ℤ) : ZMod s) = 0
        simp
      have hwm := (residueDiscriminantScalarUnits_range D s w).mpr hwi
      let π := QuotientGroup.mk' (residueDiscriminantScalarUnits D s).range
      have hπ : π w = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hwm
      change π u * (π (Units.map (discriminantOrderResidueMap D s).toMonoidHom v))⁻¹ = 1 at hπ
      refine ⟨v, ?_⟩
      exact (mul_inv_eq_one.mp hπ).symm
  · rintro ⟨v, rfl⟩
    exact conductorResidueClassPicMap_order_unit D s v
def conductorKernelPicMap :
    ConductorKernelGroup D s →*
      CommRing.Pic (DiscriminantOrder (D * (s : ℤ) ^ 2)) :=
  QuotientGroup.lift _ (conductorResidueClassPicMap D s) (by
    rw [conductorResidueClassPicMap_kernel])

theorem conductorKernelPicMap_injective :
    Function.Injective (conductorKernelPicMap D s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [conductorKernelPicMap, QuotientGroup.ker_lift, conductorResidueClassPicMap_kernel]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change QuotientGroup.mk' (maximalOrderUnitsResidueClassMap D s).range y = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  · intro hx
    change x = 1 at hx
    subst x
    exact ⟨1, Subgroup.one_mem _, map_one _⟩

end ConductorPatchKernel
section PatchReduction

variable {A B S C : Type*} [CommRing A] [CommRing B] [CommRing S] [CommRing C]
  [Algebra A B] [Algebra S C] (α : A →+* S) (hα : Function.Surjective α)
  (q : B →+* C) (hqα : ∀ a : A, q (algebraMap A B a) = algebraMap S C (α a))

def patchReductionLinear : B →ₛₗ[α] C where
  toFun := q
  map_add' := map_add q
  map_smul' a z := by
    simp only [Algebra.smul_def, map_mul, hqα]

def patchReductionSubmodule (I : Submodule A B) : Submodule S C :=
  letI : RingHomSurjective α := ⟨hα⟩
  I.map (patchReductionLinear α q hqα)

theorem patchReductionSubmodule_mem (I : Submodule A B) (z : C) :
    z ∈ patchReductionSubmodule α hα q hqα I ↔ ∃ b ∈ I, q b = z := by
  have : RingHomSurjective α := ⟨hα⟩
  exact Submodule.mem_map

theorem patchReductionSubmodule_mul (I J : Submodule A B) :
    patchReductionSubmodule α hα q hqα (I * J) =
      patchReductionSubmodule α hα q hqα I * patchReductionSubmodule α hα q hqα J := by
  have : RingHomSurjective α := ⟨hα⟩
  apply le_antisymm
  · rw [patchReductionSubmodule, Submodule.map_le_iff_le_comap]
    apply Submodule.mul_le.mpr
    intro x hx y hy
    change q (x * y) ∈ patchReductionSubmodule α hα q hqα I *
      patchReductionSubmodule α hα q hqα J
    rw [map_mul]
    exact Submodule.mul_mem_mul
      ((patchReductionSubmodule_mem α hα q hqα I _).mpr ⟨x, hx, rfl⟩)
      ((patchReductionSubmodule_mem α hα q hqα J _).mpr ⟨y, hy, rfl⟩)
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (patchReductionSubmodule_mem α hα q hqα I x).mp hx
    obtain ⟨b, hb, rfl⟩ := (patchReductionSubmodule_mem α hα q hqα J y).mp hy
    exact (patchReductionSubmodule_mem α hα q hqα (I * J) _).mpr
      ⟨a * b, Submodule.mul_mem_mul ha hb, map_mul q a b⟩

theorem patchReductionSubmodule_one :
    patchReductionSubmodule α hα q hqα (1 : Submodule A B) = 1 := by
  ext z
  rw [patchReductionSubmodule_mem, Submodule.mem_one]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hb
    exact ⟨α a, (hqα a).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := hα c
    exact ⟨algebraMap A B a, Submodule.mem_one.mpr ⟨a, rfl⟩, hqα a⟩

def patchReductionSubmoduleHom : Submodule A B →* Submodule S C where
  toFun := patchReductionSubmodule α hα q hqα
  map_one' := patchReductionSubmodule_one α hα q hqα
  map_mul' := patchReductionSubmodule_mul α hα q hqα

end PatchReduction

theorem invertibleSubmodule_ker_mem {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (q : B →+* C)
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z)
    (I : (Submodule A B)ˣ) {z : B} (hz : q z = 0) : z ∈ (I : Submodule A B) := by
  have h : Submodule.spanSingleton A z * (↑(I⁻¹) : Submodule A B) ≤ 1 := by
    apply Submodule.mul_le.mpr
    intro x hx y _
    rw [Submodule.spanSingleton_apply, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    apply Submodule.mem_one.mpr
    apply hker
    simp [Algebra.smul_def, map_mul, hz]
  have hh : (Submodule.spanSingleton A z * (↑(I⁻¹) : Submodule A B)) *
        (I : Submodule A B) ≤ 1 * (I : Submodule A B) := by
    gcongr
  have hs : Submodule.spanSingleton A z ≤ (I : Submodule A B) := by
    simpa only [mul_assoc, Units.inv_mul, mul_one, one_mul] using hh
  exact hs (by
    rw [Submodule.spanSingleton_apply, Submodule.mem_span_singleton]
    exact ⟨1, one_smul _ _⟩)
theorem conductorPatchUnitHom_surjective {A B S C : Type*}
    [CommRing A] [CommRing B] [CommRing S] [CommRing C]
    [Algebra A B] [Algebra S C] [FaithfulSMul S C] [Subsingleton (CommRing.Pic S)]
    (α : A →+* S) (hα : Function.Surjective α)
    (q : B →+* C) (hq : Function.Surjective q)
    (hqα : ∀ a : A, q (algebraMap A B a) = algebraMap S C (α a))
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) :
    Function.Surjective (conductorPatchUnitHom q hq hker) := by
  intro I
  let J : (Submodule S C)ˣ :=
    Units.map (patchReductionSubmoduleHom α hα q hqα) I
  have hJ : J ∈ (Submodule.unitsToPic S C).ker := by
    exact Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hJ
  obtain ⟨u, hu⟩ := hJ
  have hL := congrArg Units.val hu
  change Submodule.spanSingleton S (u : C) =
    patchReductionSubmodule α hα q hqα (I : Submodule A B) at hL
  refine ⟨u, ?_⟩
  apply Units.ext
  ext z
  change (∃ a : A, q z = (u : C) * q (algebraMap A B a)) ↔ z ∈ (I : Submodule A B)
  constructor
  · rintro ⟨a, ha⟩
    have hm : q z ∈ patchReductionSubmodule α hα q hqα (I : Submodule A B) := by
      rw [← hL, Submodule.spanSingleton_apply, Submodule.mem_span_singleton]
      refine ⟨α a, ?_⟩
      rw [Algebra.smul_def, ← hqα, ha, mul_comm]
    obtain ⟨b, hb, he⟩ := (patchReductionSubmodule_mem α hα q hqα _ _).mp hm
    have hd : q (z - b) = 0 := by rw [map_sub, he, sub_self]
    have hzI := invertibleSubmodule_ker_mem q hker I hd
    have hh := Submodule.add_mem (I : Submodule A B) hzI hb
    simpa only [sub_add_cancel] using hh
  · intro hz
    have hm := (patchReductionSubmodule_mem α hα q hqα (I : Submodule A B) _).mpr
      ⟨z, hz, rfl⟩
    rw [← hL, Submodule.spanSingleton_apply, Submodule.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    obtain ⟨a, rfl⟩ := hα c
    refine ⟨a, ?_⟩
    rw [hqα, ← hc, Algebra.smul_def, mul_comm]

theorem conductorPatchPicHom_range {A B S C : Type*}
    [CommRing A] [CommRing B] [CommRing S] [CommRing C]
    [Algebra A B] [FaithfulSMul A B] [Algebra S C] [FaithfulSMul S C]
    [Subsingleton (CommRing.Pic S)] (α : A →+* S) (hα : Function.Surjective α)
    (q : B →+* C) (hq : Function.Surjective q)
    (hqα : ∀ a : A, q (algebraMap A B a) = algebraMap S C (α a))
    (hker : ∀ z : B, q z = 0 → ∃ a : A, algebraMap A B a = z) :
    (conductorPatchPicHom q hq hker).range = CommRing.relPic A B := by
  have he : (conductorPatchUnitHom q hq hker).range = ⊤ :=
    (conductorPatchUnitHom q hq hker).range_eq_top_of_surjective
      (conductorPatchUnitHom_surjective α hα q hq hqα hker)
  rw [conductorPatchPicHom, MonoidHom.range_comp, he,
    Subgroup.map_top, Submodule.range_unitsToPic]

section ConductorPatchImage

variable (D : ℤ) (s : ℕ) [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

attribute [local instance] conductorOrderMaximalOrderAlgebra conductorOrderMaximalOrderFaithful
  conductorPatchUnitImageNormal

def conductorOrderScalarResidue :
    DiscriminantOrder (D * (s : ℤ) ^ 2) →+* ZMod s :=
  (QuadraticAlgebra.lift
    (⟨(conductorOrderShift D s : ZMod s), by
      simp only [zsmul_eq_mul, mul_one]
      have h := congrArg (fun z : ℤ => (z : ZMod s))
        (conductorOrderShift_polynomial_relation D s Fact.out)
      push_cast at h
      simpa only [pow_two, ZMod.natCast_self, zero_mul, mul_zero, add_zero] using h⟩ :
        {r : ZMod s // r * r =
          ((D * (s : ℤ) ^ 2 - (D * (s : ℤ) ^ 2) % 4) / 4) • 1 +
            ((D * (s : ℤ) ^ 2) % 4) • r}) :
      DiscriminantOrder (D * (s : ℤ) ^ 2) →ₐ[ℤ] ZMod s).toRingHom

omit [NeZero s] in
theorem conductorOrderScalarResidue_apply (z : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    conductorOrderScalarResidue D s z =
      (z.re : ZMod s) + (conductorOrderShift D s : ZMod s) * (z.im : ZMod s) := by
  simp [conductorOrderScalarResidue, QuadraticAlgebra.lift_apply_apply,
    zsmul_eq_mul, mul_comm]

omit [NeZero s] in
theorem conductorOrderScalarResidue_surjective :
    Function.Surjective (conductorOrderScalarResidue D s) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨⟨k, 0⟩, ?_⟩
  rw [conductorOrderScalarResidue_apply]
  simp

omit [NeZero s] in
theorem conductorOrderScalarResidue_compat
    (a : DiscriminantOrder (D * (s : ℤ) ^ 2)) :
    discriminantOrderResidueMap D s
      (algebraMap (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) a) =
      algebraMap (ZMod s) (ResidueDiscriminantOrder D s) (conductorOrderScalarResidue D s a) := by
  rw [conductorOrderMaximalOrder_algebraMap, conductorOrderEmbedding_apply,
    discriminantOrderResidueMap_apply, QuadraticAlgebra.algebraMap_eq,
    conductorOrderScalarResidue_apply]
  ext
  · simp
  · change (((s : ℤ) * a.im : ℤ) : ZMod s) = 0
    simp

theorem conductorResiduePicMap_range :
    (conductorResiduePicMap D s).range =
      CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) := by
  have : FaithfulSMul (ZMod s) (ResidueDiscriminantOrder D s) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (by intro x y h; exact congrArg QuadraticAlgebra.re h)
  exact conductorPatchPicHom_range (conductorOrderScalarResidue D s)
    (conductorOrderScalarResidue_surjective D s) (discriminantOrderResidueMap D s)
    (discriminantOrderResidueMap_surjective D s) (conductorOrderScalarResidue_compat D s)
    (conductorResidue_kernel_in_order D s)

theorem conductorResidueClassPicMap_range :
    (conductorResidueClassPicMap D s).range =
      CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) := by
  have he : (conductorResiduePicMap D s).range =
      (conductorResidueClassPicMap D s).range := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      exact ⟨QuotientGroup.mk' (residueDiscriminantScalarUnits D s).range u, rfl⟩
    · rintro x ⟨u, rfl⟩
      induction u using QuotientGroup.induction_on with
      | H v => exact ⟨v, rfl⟩
  rw [← he, conductorResiduePicMap_range]
theorem conductorKernelPicMap_range :
    (conductorKernelPicMap D s).range =
      CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) := by
  have he : (conductorResidueClassPicMap D s).range =
      (conductorKernelPicMap D s).range := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      exact ⟨QuotientGroup.mk' (maximalOrderUnitsResidueClassMap D s).range u, rfl⟩
    · rintro x ⟨u, rfl⟩
      induction u using QuotientGroup.induction_on with
      | H v => exact ⟨v, rfl⟩
  rw [← he, conductorResidueClassPicMap_range]

def conductorKernelRelPicHom :
    ConductorKernelGroup D s →*
      CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) :=
  (conductorKernelPicMap D s).codRestrict _ (by
    intro u
    rw [← conductorKernelPicMap_range]
    exact ⟨u, rfl⟩)

def conductorKernelEquivRelPic :
    ConductorKernelGroup D s ≃*
      CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D) :=
  MulEquiv.ofBijective (conductorKernelRelPicHom D s) (by
    constructor
    · intro x y h
      exact conductorKernelPicMap_injective D s (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      rw [← conductorKernelPicMap_range] at hx
      obtain ⟨u, hu⟩ := hx
      exact ⟨u, Subtype.ext hu⟩)

theorem conductorExtensionPicKernel_card :
    Nat.card (CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2))
      (DiscriminantOrder D)) = Nat.card (ConductorKernelGroup D s) :=
  (Nat.card_congr (conductorKernelEquivRelPic D s).toEquiv).symm

end ConductorPatchImage
theorem primitiveForm_not_all_dvd {D : ℤ} (f : PrimitivePositiveForm D)
    {p : ℕ} (hp : p.Prime) :
    ¬ ((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) := by
  rintro ⟨ha, hb, hc⟩
  have hd : (p : ℤ) ∣ (Int.gcd f.a (Int.gcd f.b f.c : ℤ) : ℤ) :=
    Int.dvd_coe_gcd ha (Int.dvd_coe_gcd hb hc)
  rw [f.primitive] at hd
  have hdn : p ∣ 1 := by exact_mod_cast hd
  exact hp.not_dvd_one hdn

theorem primitiveForm_odd_leading_representative {D : ℤ} (hD : D < 0)
    (f : PrimitivePositiveForm D) :
    ∃ g : PrimitivePositiveForm D, properChange g f ∧ ¬ (2 : ℤ) ∣ g.a := by
  by_cases ha : (2 : ℤ) ∣ f.a
  · by_cases hc : (2 : ℤ) ∣ f.c
    · have hb : ¬ (2 : ℤ) ∣ f.b := by
        intro hb
        exact primitiveForm_not_all_dvd f (by decide : Nat.Prime 2) ⟨ha, hb, hc⟩
      let g := (f.shear 1).swap hD
      refine ⟨g, properChange_trans (properChange_swap hD _) (properChange_shear f 1), ?_⟩
      intro hg
      change (2 : ℤ) ∣ f.a * 1 ^ 2 + f.b * 1 + f.c at hg
      apply hb
      have hh := (hg.sub ha).sub hc
      convert hh using 1
      ring
    · exact ⟨f.swap hD, properChange_swap hD f, hc⟩
  · exact ⟨f, properChange_refl f, ha⟩

theorem primitiveForm_prime_nonzero_value {D : ℤ} (f : PrimitivePositiveForm D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ k : ℕ, k ≤ 2 ∧ ¬ (p : ℤ) ∣ f.eval ![2 * (k : ℤ) + 1, 2] := by
  by_contra hh
  push Not at hh
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hcast : ((2 : ℤ) : ZMod p) = 0 := by simpa using h
    have hdi : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hcast
    have hd : p ∣ 2 := by exact_mod_cast hdi
    have hple := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hpge := hp.two_le
    omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have h8 : (8 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1
    norm_num
  have he (k : ℕ) (hk : k ≤ 2) :
      (f.a : ZMod p) * (2 * (k : ZMod p) + 1) ^ 2 +
        (f.b : ZMod p) * (2 * (k : ZMod p) + 1) * 2 + (f.c : ZMod p) * 2 ^ 2 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (f.eval ![2 * (k : ℤ) + 1, 2]) p).mpr (hh k hk)
    norm_num [PrimitivePositiveForm.eval] at h ⊢
    exact h
  have h₀ := he 0 (by decide)
  have h₁ := he 1 (by decide)
  have h₂ := he 2 (by decide)
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_mul, zero_add] at h₀ h₁ h₂
  have ha : (f.a : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (8 : ZMod p) * (f.a : ZMod p) = 0 from ?_)).resolve_left h8
    linear_combination h₂ - 2 * h₁ + h₀
  have hb : (f.b : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (4 : ZMod p) * (f.b : ZMod p) = 0 from ?_)).resolve_left h4
    linear_combination h₁ - h₀ - 8 * ha
  have hc : (f.c : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show (4 : ZMod p) * (f.c : ZMod p) = 0 from ?_)).resolve_left h4
    linear_combination h₀ - ha - 2 * hb
  exact primitiveForm_not_all_dvd f hp ⟨
    (ZMod.intCast_zmod_eq_zero_iff_dvd f.a p).mp ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd f.b p).mp hb,
    (ZMod.intCast_zmod_eq_zero_iff_dvd f.c p).mp hc⟩
def PrimitivePositiveForm.coprimeLeadingChange {D : ℤ} (hD : D < 0)
    (f : PrimitivePositiveForm D) (k : ℕ) : PrimitivePositiveForm D :=
  (((f.shear (k : ℤ)).swap hD).shear (-2)).swap hD

theorem coprimeLeadingChange_proper {D : ℤ} (hD : D < 0)
    (f : PrimitivePositiveForm D) (k : ℕ) :
    properChange (f.coprimeLeadingChange hD k) f := by
  exact properChange_trans (properChange_swap hD _)
    (properChange_trans (properChange_shear _ _)
      (properChange_trans (properChange_swap hD _) (properChange_shear f _)))

theorem coprimeLeadingChange_leading {D : ℤ} (hD : D < 0)
    (f : PrimitivePositiveForm D) (k : ℕ) :
    (f.coprimeLeadingChange hD k).a = f.eval ![2 * (k : ℤ) + 1, 2] := by
  simp only [PrimitivePositiveForm.coprimeLeadingChange, PrimitivePositiveForm.shear,
    PrimitivePositiveForm.swap, PrimitivePositiveForm.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem primitiveForm_coprime_leading_representative {D : ℤ} (hD : D < 0)
    (f : PrimitivePositiveForm D) (s : ℕ) (hs : 0 < s) :
    ∃ g : PrimitivePositiveForm D, properChange g f ∧ g.a.natAbs.Coprime s := by
  classical
  obtain ⟨f₀, hf₀, ha₂⟩ := primitiveForm_odd_leading_representative hD f
  have hlocal : ∀ p ∈ s.primeFactors, ∃ k : ℕ,
      ¬ (p : ℤ) ∣ f₀.eval ![2 * (k : ℤ) + 1, 2] := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    by_cases hp2 : p = 2
    · subst p
      refine ⟨0, ?_⟩
      intro h
      apply ha₂
      have hb : (2 : ℤ) ∣ f₀.b * 1 * 2 := dvd_mul_left _ _
      have hc : (2 : ℤ) ∣ f₀.c * 2 ^ 2 :=
        dvd_mul_of_dvd_right (by norm_num : (2 : ℤ) ∣ (2 : ℤ) ^ 2) _
      simp only [PrimitivePositiveForm.eval, Nat.cast_zero, mul_zero, zero_add,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h
      convert (h.sub hc).sub hb using 1
      ring
    · obtain ⟨k, _, hk⟩ := primitiveForm_prime_nonzero_value f₀ hpp hp2
      exact ⟨k, hk⟩
  let k : ℕ → ℕ := fun p => if hp : p ∈ s.primeFactors then (hlocal p hp).choose else 0
  have hk : ∀ p ∈ s.primeFactors, ¬ (p : ℤ) ∣ f₀.eval ![2 * (k p : ℤ) + 1, 2] := by
    intro p hp
    dsimp only [k]
    rw [dite_eq_left hp]
    exact (hlocal p hp).choose_spec
  have hpair : (s.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
      (Nat.mem_primeFactors.mp hq).1).mpr hpq
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset k id s.primeFactors
    (by intro p hp; exact (Nat.mem_primeFactors.mp hp).1.ne_zero) hpair
  let g := f₀.coprimeLeadingChange hD r
  refine ⟨g, properChange_trans (coprimeLeadingChange_proper hD f₀ r) hf₀, ?_⟩
  by_contra hcop
  have hg : g.a.natAbs.gcd s ≠ 1 := hcop
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpa := hpg.trans (Nat.gcd_dvd_left g.a.natAbs s)
  have hps := hpg.trans (Nat.gcd_dvd_right g.a.natAbs s)
  have hpS : p ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps, hs.ne'⟩
  have he : (r : ZMod p) = (k p : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff r (k p) p).mpr (hr p hpS)
  have hdiv : (p : ℤ) ∣ g.a := Int.natCast_dvd.mpr hpa
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd g.a p).mpr hdiv
  rw [show g.a = f₀.eval ![2 * (r : ℤ) + 1, 2] from coprimeLeadingChange_leading hD f₀ r] at hz
  simp only [PrimitivePositiveForm.eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one,
    Int.cast_ofNat] at hz
  rw [he] at hz
  have hd : (p : ℤ) ∣ f₀.eval ![2 * (k p : ℤ) + 1, 2] := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [PrimitivePositiveForm.eval, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one,
      Int.cast_ofNat] using hz
  exact hk p hpS hd
def PrimitivePositiveForm.conductorLift {D : ℤ} (f : PrimitivePositiveForm D) (s : ℕ)
    (hcop : IsCoprime f.a (s : ℤ)) : PrimitivePositiveForm (D * (s : ℤ) ^ 2) where
  a := f.a
  b := (s : ℤ) * f.b
  c := (s : ℤ) ^ 2 * f.c
  positive := f.positive
  discriminant := by
    calc
      ((s : ℤ) * f.b) ^ 2 - 4 * f.a * ((s : ℤ) ^ 2 * f.c) =
          (f.b ^ 2 - 4 * f.a * f.c) * (s : ℤ) ^ 2 := by ring
      _ = _ := by rw [f.discriminant]
  primitive := primitive_coefficients_transfer f _ _ _ (by
    intro z hza hzb hzc
    have hc : IsCoprime z (s : ℤ) := by
      obtain ⟨u, hu⟩ := hza
      obtain ⟨x, y, hxy⟩ := hcop
      refine ⟨x * u, y, ?_⟩
      rw [hu] at hxy
      linear_combination hxy
    exact ⟨hza, hc.dvd_of_dvd_mul_left hzb, (hc.pow_right (n := 2)).dvd_of_dvd_mul_left hzc⟩)

theorem conductorLift_shift {D : ℤ} (f : PrimitivePositiveForm D) (s : ℕ)
    (hcop : IsCoprime f.a (s : ℤ)) :
    formOrderShift (f.conductorLift s hcop) + conductorOrderShift D s =
      (s : ℤ) * formOrderShift f := by
  have h₁ := formOrderShift_relation (f.conductorLift s hcop)
  have h₂ := conductorOrderShift_relation D s f.discriminant_is_discriminant
  have h₃ := formOrderShift_relation f
  change 2 * formOrderShift (f.conductorLift s hcop) +
    (D * (s : ℤ) ^ 2) % 4 = (s : ℤ) * f.b at h₁
  have hh : 2 * (formOrderShift (f.conductorLift s hcop) + conductorOrderShift D s -
      (s : ℤ) * formOrderShift f) = 0 := by
    linear_combination h₁ + h₂ - (s : ℤ) * h₃
  linarith

theorem conductorLift_ideal_map {D : ℤ} (f : PrimitivePositiveForm D) (s : ℕ)
    (hcop : IsCoprime f.a (s : ℤ)) :
    (formOrderIdeal (f.conductorLift s hcop)).map
      (conductorOrderEmbedding D s f.discriminant_is_discriminant).toRingHom =
        formOrderIdeal f := by
  rw [formOrderIdeal_eq_span, formOrderIdeal_eq_span, Ideal.map_span]
  have he : (conductorOrderEmbedding D s f.discriminant_is_discriminant)
      (⟨formOrderShift (f.conductorLift s hcop), 1⟩ :
        DiscriminantOrder (D * (s : ℤ) ^ 2)) =
      (s : DiscriminantOrder D) * (⟨formOrderShift f, 1⟩ : DiscriminantOrder D) := by
    rw [conductorOrderEmbedding_apply]
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_natCast,
        QuadraticAlgebra.im_natCast, mul_zero, add_zero, mul_one]
      exact conductorLift_shift f s hcop
    · simp
  have ha : (conductorOrderEmbedding D s f.discriminant_is_discriminant)
      ((f.conductorLift s hcop).a : DiscriminantOrder (D * (s : ℤ) ^ 2)) =
      (f.a : DiscriminantOrder D) := by
    exact map_intCast _ _
  simp only [Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {(conductorOrderEmbedding D s f.discriminant_is_discriminant)
      ((f.conductorLift s hcop).a : DiscriminantOrder (D * (s : ℤ) ^ 2)),
      (conductorOrderEmbedding D s f.discriminant_is_discriminant)
        (⟨formOrderShift (f.conductorLift s hcop), 1⟩ :
          DiscriminantOrder (D * (s : ℤ) ^ 2))} =
    Ideal.span {(f.a : DiscriminantOrder D),
      (⟨formOrderShift f, 1⟩ : DiscriminantOrder D)}
  rw [ha, he]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · let x : ℤ := hcop.choose
      let y : ℤ := hcop.choose_spec.choose
      have hxy : x * f.a + y * (s : ℤ) = 1 := hcop.choose_spec.choose_spec
      let β : DiscriminantOrder D := ⟨formOrderShift f, 1⟩
      have hh : β =
          (x : DiscriminantOrder D) * β * (f.a : DiscriminantOrder D) +
          (y : DiscriminantOrder D) * ((s : DiscriminantOrder D) * β) := by
        have hc := congrArg (fun z : ℤ => (z : DiscriminantOrder D)) hxy
        push_cast at hc
        linear_combination -β * hc
      change β ∈ Ideal.span {(f.a : DiscriminantOrder D), (s : DiscriminantOrder D) * β}
      have hm : (x : DiscriminantOrder D) * β * (f.a : DiscriminantOrder D) +
          (y : DiscriminantOrder D) * ((s : DiscriminantOrder D) * β) ∈
          Ideal.span {(f.a : DiscriminantOrder D), (s : DiscriminantOrder D) * β} :=
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      exact (congrArg (fun z : DiscriminantOrder D =>
        z ∈ Ideal.span {(f.a : DiscriminantOrder D), (s : DiscriminantOrder D) * β}) hh).mpr hm


theorem classGroupExtension_integralUnits {A B KA KB : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field KA] [Field KB] [Algebra A KA] [IsFractionRing A KA]
    [Algebra B KB] [IsFractionRing B KB]
    (f : A →+* B) (hf : Function.Injective f)
    (U : (FractionalIdeal (nonZeroDivisors A) KA)ˣ)
    (V : (FractionalIdeal (nonZeroDivisors B) KB)ˣ)
    (I : Ideal A) (J : Ideal B)
    (hU : (U : FractionalIdeal (nonZeroDivisors A) KA) = I)
    (hV : (V : FractionalIdeal (nonZeroDivisors B) KB) = J) (hIJ : I.map f = J) :
    classGroupExtension f hf (ClassGroup.mk KA U) = ClassGroup.mk KB V := by
  let U' : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ :=
    Units.map (FractionalIdeal.canonicalEquiv (nonZeroDivisors A) KA (FractionRing A)) U
  let V' : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ :=
    Units.map (FractionalIdeal.canonicalEquiv (nonZeroDivisors B) KB (FractionRing B)) V
  have hU' : (U' : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) = I := by
    change FractionalIdeal.canonicalEquiv (nonZeroDivisors A) KA (FractionRing A) U.val = _
    rw [hU, FractionalIdeal.canonicalEquiv_coeIdeal]
  have hV' : (V' : FractionalIdeal (nonZeroDivisors B) (FractionRing B)) = J := by
    change FractionalIdeal.canonicalEquiv (nonZeroDivisors B) KB (FractionRing B) V.val = _
    rw [hV, FractionalIdeal.canonicalEquiv_coeIdeal]
  have hmkU : ClassGroup.mk (FractionRing A) U' = ClassGroup.mk KA U :=
    ClassGroup.mk_canonicalEquiv KA (FractionRing A) U
  have hmkV : ClassGroup.mk (FractionRing B) V' = ClassGroup.mk KB V :=
    ClassGroup.mk_canonicalEquiv KB (FractionRing B) V
  have he : Units.map (FractionalIdeal.extendedHom' (FractionRing B)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom U' = V' := by
    apply Units.ext
    change FractionalIdeal.extended (FractionRing B)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)
      (U' : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) =
        (V' : FractionalIdeal (nonZeroDivisors B) (FractionRing B))
    rw [hU', hV', FractionalIdeal.extended_coeIdeal_eq_map, hIJ]
  rw [← hmkU, ← hmkV, classGroupExtension_mk, he]


section ConductorClassSurjectivity

variable (D : ℤ) (s : ℕ) [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

attribute [local instance] conductorOrderNegativeDiscriminant conductorOrderDiscriminantModFour

theorem conductorClassGroupMap_surjective :
    Function.Surjective (conductorClassGroupMap D s) := by
  intro C
  obtain ⟨q, rfl⟩ := generalFormClassToIdealClass_surjective C
  induction q using Quotient.inductionOn with
  | _ f =>
    obtain ⟨g, hgf, hcopNat⟩ := primitiveForm_coprime_leading_representative
      (Fact.out : D < 0) f s (Nat.pos_of_ne_zero (NeZero.ne s))
    have hcop : IsCoprime g.a (s : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcopNat)
    refine ⟨generalFormIdealClass (g.conductorLift s hcop), ?_⟩
    change conductorClassGroupMap D s (generalFormIdealClass (g.conductorLift s hcop)) =
      generalFormIdealClass f
    calc
      _ = generalFormIdealClass g := by
        apply classGroupExtension_integralUnits
          (conductorOrderEmbedding D s Fact.out).toRingHom
          (conductorOrderEmbedding_injective D s Fact.out
            (Nat.pos_of_ne_zero (NeZero.ne s)))
          (generalFormIdealUnit (g.conductorLift s hcop)) (generalFormIdealUnit g)
          (formOrderIdeal (g.conductorLift s hcop)) (formOrderIdeal g)
        · exact generalFormIdealUnit_val _
        · exact generalFormIdealUnit_val _
        · exact conductorLift_ideal_map g s hcop
      _ = _ := (generalFormIdealClass_eq_iff g f).mpr hgf

end ConductorClassSurjectivity


open LinearMap Submodule TensorProduct in
theorem invertibleSubmodule_tensorMul_bijective {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [FaithfulSMul R K] (I : (Submodule R K)ˣ) :
    Function.Bijective (LinearMap.mul' R K ∘ₗ I.1.subtype.lTensor K) := by
  obtain ⟨T, T', hT, hT', one_mem⟩ :=
    mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul, ← Finset.coe_image₂, mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S => Finset.mem_image₂.mp i.2
  let f : I →ₗ[R] S → R := .pi fun i =>
    (LinearEquiv.ofInjective (Algebra.linearMap R K)
      (FaithfulSMul.algebraMap_injective R K)).symm.comp
      (restrict (mulRight R (r i • a i)) fun x hx => by
        rw [← one_eq_range, ← I.mul_inv]
        exact mul_mem_mul hx (I⁻¹.1.smul_mem _ (hT (ha i))))
  have hf (x : I.1) (i : S) : algebraMap R K (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
  let g : (S → R) →ₗ[R] I := .lsum _ _ ℕ fun i =>
    .toSpanSingleton _ _ ⟨b i, hT' (hb i)⟩
  have hgf : g ∘ₗ f = .id := LinearMap.ext fun x => Subtype.ext (by
    simp only [g, lsum_apply, comp_apply, LinearMap.sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply])
  set m := mul' R K ∘ₗ I.1.subtype.lTensor K
  have he : (piScalarRight R R K S).toLinearMap ∘ₗ f.lTensor K =
      (.pi fun i : S => mulRight R (r i • a i)) ∘ₗ m := by
    ext
    simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
  have hi := (piScalarRight R R K S).injective.comp
    (injective_of_comp_eq_id (f.lTensor K) (g.lTensor K)
      (by rw [← lTensor_comp, hgf, lTensor_id]))
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp, he, coe_comp] at hi
  refine ⟨.of_comp hi, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl,
    range_comp, LinearEquiv.range, Submodule.map_top, mulMap_range,
    top_mul_eq_top_of_mul_eq_one I.inv_mul]

section SubmoduleExtension

variable {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
  [FaithfulSMul R K] [FaithfulSMul B K] (I : (Submodule R K)ˣ)

def invertibleSubmodule_extensionMulR : TensorProduct R B ↥(I : Submodule R K) →ₗ[R] K :=
  (LinearMap.mul' R K ∘ₗ I.1.subtype.lTensor K).comp
    ((IsScalarTower.toAlgHom R B K).toLinearMap.rTensor (I : Submodule R K))

omit [FaithfulSMul R K] [FaithfulSMul B K] in
theorem invertibleSubmodule_extensionMulR_tmul (b : B) (i : (I : Submodule R K)) :
    invertibleSubmodule_extensionMulR (B := B) I (TensorProduct.tmul R b i) =
      algebraMap B K b * (i : K) := rfl

def invertibleSubmodule_extensionMul : TensorProduct R B ↥(I : Submodule R K) →ₗ[B] K where
  toFun := invertibleSubmodule_extensionMulR (B := B) I
  map_add' := (invertibleSubmodule_extensionMulR (B := B) I).map_add
  map_smul' b z := by
    induction z using TensorProduct.inductionOn with
    | tmul c i =>
      rw [TensorProduct.smul_tmul', invertibleSubmodule_extensionMulR_tmul,
        invertibleSubmodule_extensionMulR_tmul]
      simp only [smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc, RingHom.id_apply]
    | add x y hx hy =>
      simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy

theorem invertibleSubmodule_extensionMul_injective :
    Function.Injective (invertibleSubmodule_extensionMul (B := B) I) := by
  change Function.Injective (invertibleSubmodule_extensionMulR (B := B) I)
  exact (invertibleSubmodule_tensorMul_bijective I).1.comp
    (Module.Flat.rTensor_preserves_injective_linearMap
      (IsScalarTower.toAlgHom R B K).toLinearMap
      (FaithfulSMul.algebraMap_injective B K))

omit [FaithfulSMul R K] [FaithfulSMul B K] in
theorem invertibleSubmodule_extensionMul_range :
    (invertibleSubmodule_extensionMul (B := B) I).range = Submodule.span B (I : Set K) := by
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul b i =>
      change algebraMap B K b * (i : K) ∈ _
      simpa only [Algebra.smul_def] using
        (Submodule.span B (I : Set K)).smul_mem b (Submodule.subset_span i.prop)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    intro z hz
    exact ⟨TensorProduct.tmul R (1 : B) (⟨z, hz⟩ : (I : Submodule R K)), by
      change algebraMap B K 1 * z = z
      rw [map_one, one_mul]⟩

def invertibleSubmodule_extensionTensorEquiv :
    TensorProduct R B ↥(I : Submodule R K) ≃ₗ[B] Submodule.span B (I : Set K) :=
  (LinearEquiv.ofInjective (invertibleSubmodule_extensionMul (B := B) I)
    (invertibleSubmodule_extensionMul_injective (B := B) I)).trans
      (LinearEquiv.ofEq _ _ (invertibleSubmodule_extensionMul_range (B := B) I))

end SubmoduleExtension

theorem picExtension_invertibleSubmodule {R B K : Type*} [CommRing R] [CommRing B]
    [CommRing K] [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [FaithfulSMul R K] [FaithfulSMul B K]
    (I : (Submodule R K)ˣ) (J : (Submodule B K)ˣ)
    (hJ : (J : Submodule B K) = Submodule.span B (I : Set K)) :
    CommRing.Pic.mapAlgebra R B (Submodule.unitsToPic R K I) =
      Submodule.unitsToPic B K J := by
  rw [CommRing.Pic.mapAlgebra_apply]
  conv_rhs => rw [Submodule.unitsToPic_apply]
  apply CommRing.Pic.mk_eq_mk_iff.mpr
  exact ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (Submodule.unitsToPicEquiv I)).trans
    ((invertibleSubmodule_extensionTensorEquiv (B := B) I).trans
      (LinearEquiv.ofEq _ _ hJ.symm))⟩

theorem classGroup_equivPic_mk_fractionRing {R : Type*} [CommRing R] [IsDomain R]
    (U : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ) :
    ClassGroup.equivPic R (ClassGroup.mk (FractionRing R) U) =
      Submodule.unitsToPic R (FractionRing R) (FractionalIdeal.unitsMulEquivSubmodule U) := by
  simp only [ClassGroup.mk_def, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_monoidHom_refl, Units.map_id, MonoidHom.id_apply]
  rfl
noncomputable def idealFractionalUnitEquiv {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (I : Ideal R)
    (U : (FractionalIdeal (nonZeroDivisors R) K)ˣ)
    (hU : (U : FractionalIdeal (nonZeroDivisors R) K) = I) :
    I ≃ₗ[R] ↥(FractionalIdeal.unitsMulEquivSubmodule U : Submodule R K) :=
  (Submodule.equivMapOfInjective (Algebra.linearMap R K)
    (IsFractionRing.injective R K) I).trans
    (LinearEquiv.ofEq _ _ (congrArg (fun X : FractionalIdeal (nonZeroDivisors R) K => (X : Submodule R K)) hU).symm)

theorem classGroup_equivPic_mk_integral {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (I : Ideal R)
    (U : (FractionalIdeal (nonZeroDivisors R) K)ˣ)
    (hU : (U : FractionalIdeal (nonZeroDivisors R) K) = I) :
    ClassGroup.equivPic R (ClassGroup.mk K U) =
      Submodule.unitsToPic R K (FractionalIdeal.unitsMulEquivSubmodule U) := by
  let V := Units.map (FractionalIdeal.canonicalEquiv (nonZeroDivisors R) K
    (FractionRing R)).toMonoidHom U
  have hV : (V : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I := by
    change FractionalIdeal.canonicalEquiv (nonZeroDivisors R) K (FractionRing R)
      (U : FractionalIdeal (nonZeroDivisors R) K) = _
    rw [hU, FractionalIdeal.canonicalEquiv_coeIdeal]
  rw [← ClassGroup.mk_canonicalEquiv K (FractionRing R) U,
    classGroup_equivPic_mk_fractionRing]
  change Submodule.unitsToPic R (FractionRing R) (FractionalIdeal.unitsMulEquivSubmodule V) = _
  rw [Submodule.unitsToPic_apply, Submodule.unitsToPic_apply]
  apply CommRing.Pic.mk_eq_mk_iff.mpr
  exact ⟨(idealFractionalUnitEquiv I V hV).symm.trans
    (idealFractionalUnitEquiv I U hU)⟩

theorem integralIdeal_extension_submodule {R B K : Type*} [CommRing R] [CommRing B]
    [CommRing K] [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    (I : Ideal R) :
    IsLocalization.coeSubmodule K (I.map (algebraMap R B)) =
      Submodule.span B ((I : FractionalIdeal (nonZeroDivisors R) K) : Set K) := by
  rw [Ideal.map, IsLocalization.coeSubmodule_span, Set.image_image]
  apply congrArg (Submodule.span B)
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, IsScalarTower.algebraMap_apply R B K a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (IsScalarTower.algebraMap_apply R B K a).symm⟩

theorem classGroup_picExtension_integral {R B K : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsFractionRing R K] [IsFractionRing B K] [FaithfulSMul R B]
    (U : (FractionalIdeal (nonZeroDivisors R) K)ˣ) (I : Ideal R)
    (hU : (U : FractionalIdeal (nonZeroDivisors R) K) = I) :
    ClassGroup.equivPic B
        (classGroupExtension (algebraMap R B) (FaithfulSMul.algebraMap_injective R B)
          (ClassGroup.mk K U)) =
      CommRing.Pic.mapAlgebra R B (ClassGroup.equivPic R (ClassGroup.mk K U)) := by
  let hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (algebraMap R B) (FaithfulSMul.algebraMap_injective R B)
  let V := Units.map (FractionalIdeal.extendedHom' K hf).toMonoidHom U
  have hV : (V : FractionalIdeal (nonZeroDivisors B) K) = I.map (algebraMap R B) := by
    change FractionalIdeal.extended K hf (U : FractionalIdeal (nonZeroDivisors R) K) = _
    rw [hU, FractionalIdeal.extended_coeIdeal_eq_map]
  rw [classGroupExtension_integralUnits _ _ U V I _ hU hV rfl,
    classGroup_equivPic_mk_integral _ V hV, classGroup_equivPic_mk_integral I U hU]
  apply (picExtension_invertibleSubmodule _ _ ?_).symm
  change (V : FractionalIdeal (nonZeroDivisors B) K).1 =
    Submodule.span B ((U : FractionalIdeal (nonZeroDivisors R) K) : Set K)
  rw [hV, hU]
  exact integralIdeal_extension_submodule I


section ConductorPicNaturality

variable (D : ℤ) (s : ℕ) [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

attribute [local instance] conductorOrderNegativeDiscriminant conductorOrderDiscriminantModFour
  conductorOrderMaximalFieldAlgebra conductorOrderMaximalFieldFaithful
  conductorOrderMaximalFieldFractionRing conductorOrderMaximalOrderAlgebra
  conductorOrderMaximalOrderFaithful

local instance conductorOrderFieldTower :
    IsScalarTower (DiscriminantOrder (D * (s : ℤ) ^ 2))
      (DiscriminantOrder D) (DiscriminantField D) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem conductorClassGroupMap_pic
    (C : ClassGroup (DiscriminantOrder (D * (s : ℤ) ^ 2))) :
    ClassGroup.equivPic (DiscriminantOrder D) (conductorClassGroupMap D s C) =
      CommRing.Pic.mapAlgebra (DiscriminantOrder (D * (s : ℤ) ^ 2))
        (DiscriminantOrder D) (ClassGroup.equivPic _ C) := by
  obtain ⟨q, rfl⟩ := generalFormClassToIdealClass_surjective C
  induction q using Quotient.inductionOn with
  | _ f =>
    let U := Units.map (FractionalIdeal.canonicalEquiv
      (nonZeroDivisors (DiscriminantOrder (D * (s : ℤ) ^ 2)))
      (DiscriminantField (D * (s : ℤ) ^ 2)) (DiscriminantField D)).toMonoidHom
        (generalFormIdealUnit f)
    have hU : (U : FractionalIdeal
        (nonZeroDivisors (DiscriminantOrder (D * (s : ℤ) ^ 2))) (DiscriminantField D)) =
        formOrderIdeal f := by
      change FractionalIdeal.canonicalEquiv _ _ _ (generalFormIdealUnit f).val = _
      rw [generalFormIdealUnit_val, FractionalIdeal.canonicalEquiv_coeIdeal]
    have hmk : ClassGroup.mk (DiscriminantField D) U = generalFormIdealClass f :=
      ClassGroup.mk_canonicalEquiv (DiscriminantField (D * (s : ℤ) ^ 2))
        (DiscriminantField D) (generalFormIdealUnit f)
    change ClassGroup.equivPic _ (conductorClassGroupMap D s (generalFormIdealClass f)) =
      CommRing.Pic.mapAlgebra (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D)
        (ClassGroup.equivPic _ (generalFormIdealClass f))
    rw [← hmk]
    exact classGroup_picExtension_integral (B := DiscriminantOrder D) U (formOrderIdeal f) hU

theorem conductorPicMap_surjective :
    Function.Surjective (CommRing.Pic.mapAlgebra (DiscriminantOrder (D * (s : ℤ) ^ 2))
      (DiscriminantOrder D)) := by
  intro C
  obtain ⟨q, hq⟩ := (ClassGroup.equivPic (DiscriminantOrder D)).surjective C
  obtain ⟨a, ha⟩ := conductorClassGroupMap_surjective D s q
  refine ⟨ClassGroup.equivPic _ a, ?_⟩
  rw [← conductorClassGroupMap_pic D s a, ha, hq]

end ConductorPicNaturality



section ConductorCardinality

variable (D : ℤ) (s : ℕ) [Fact (D < 0)] [Fact (D % 4 = 0 ∨ D % 4 = 1)] [NeZero s]

attribute [local instance] conductorOrderNegativeDiscriminant conductorOrderDiscriminantModFour
  conductorOrderMaximalOrderAlgebra conductorOrderMaximalOrderFaithful
  conductorPatchUnitImageNormal

theorem orderClassNumber_eq_picCard :
    orderClassNumber D = Nat.card (CommRing.Pic (DiscriminantOrder D)) :=
  (orderClassNumber_eq_orderIdealClassNumber D).trans
    (Nat.card_congr (ClassGroup.equivPic (DiscriminantOrder D)).toEquiv)

theorem conductorOrderClassNumber_card :
    orderClassNumber (D * (s : ℤ) ^ 2) =
      Nat.card (ConductorKernelGroup D s) * orderClassNumber D := by
  have h := groupHom_kernel_card_mul_of_surjective
    (CommRing.Pic.mapAlgebra (DiscriminantOrder (D * (s : ℤ) ^ 2)) (DiscriminantOrder D))
    (conductorPicMap_surjective D s)
  change Nat.card (CommRing.relPic (DiscriminantOrder (D * (s : ℤ) ^ 2))
      (DiscriminantOrder D)) * Nat.card (CommRing.Pic (DiscriminantOrder D)) =
        Nat.card (CommRing.Pic (DiscriminantOrder (D * (s : ℤ) ^ 2))) at h
  rw [conductorExtensionPicKernel_card D s, ← orderClassNumber_eq_picCard D,
    ← orderClassNumber_eq_picCard (D * (s : ℤ) ^ 2)] at h
  exact h.symm

end ConductorCardinality

/-- The conductor class-number formula, including the exceptional unit counts. -/
theorem orderClassNumber_conductor (d s : ℕ) (hD : isNegativeDiscriminantAbs d) (hs : 0 < s) :
    classRatio (-((d * s ^ 2 : ℕ) : ℤ)) =
      classRatio (-(d : ℤ)) * conductorCorrection d s := by
  have hd := (negativeDiscriminantAbs_iff d).mp hD
  have : Fact (-(d : ℤ) < 0) := ⟨hd.1⟩
  have : Fact ((-(d : ℤ)) % 4 = 0 ∨ (-(d : ℤ)) % 4 = 1) := ⟨hd.2⟩
  have : NeZero s := ⟨hs.ne'⟩
  have he : -((d * s ^ 2 : ℕ) : ℤ) = -(d : ℤ) * (s : ℤ) ^ 2 := by push_cast; ring
  have hc : (orderClassNumber (-((d * s ^ 2 : ℕ) : ℤ)) : ℝ) =
      (Nat.card (ConductorKernelGroup (-(d : ℤ)) s) : ℝ) *
        (orderClassNumber (-(d : ℤ)) : ℝ) := by
    rw [he]
    exact_mod_cast conductorOrderClassNumber_card (-(d : ℤ)) s
  unfold classRatio
  rw [hc, mul_div_right_comm, conductorKernelGroup_card_ratio d s hD hs]
  ring

theorem orderClassNumberFormula : OrderClassNumberFormula := by
  intro d s hd hs hF
  exact orderClassNumber_conductor d s
    ((negativeDiscriminantAbs_iff d).mpr ⟨by omega, hF.emod_four_eq_zero_or_one⟩) hs

/-- The unconditional formula from proof.tex. -/
theorem closed_formula (n : ℕ) [NeZero n] :
    ↑(residueSum n) =
      (↑n * (↑n - ↑(squarePart n)) / 2 -
        2 * ↑n * ∑ M ∈ discriminantDivisors n,
          classRatio (-(M : ℤ)) : ℝ) :=
  closed_formula_of_order_class_number orderClassNumberFormula

end
end SquareResidue

