/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt'' : 0 < x*(-t) :=
    calc
      0 < -x*t := by addarith[hxt]
      _ = x * (-t) := by ring
    cancel x at hxt''
    have hxt''' : t < 0 := by addarith[hxt'']
    apply ne_of_lt
    apply hxt'''

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor

  calc
    p = (p + p)/2 := by ring
    _ < (p + q)/2 := by rel[h]

  calc
      (p + q)/2
    _ < (q + q)/2 := by rel[h]
    _ = q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1
  calc
      (x + 1)^2
    _ = (x^2 + x + 1) + x := by ring
    _ = (x + 1/2)^2 + 3/4 + x := by ring
    _ > (x + 1/2)^2 + x := by extra
    _ >= 0 + x := by extra
    _ = x := by ring


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hx⟩ := h
  have h' : (x - 1)*(t - 1) < 0 :=
    calc
        (x - 1)*(t - 1)
      _ = (x*t + 1) - x - t := by ring
      _ < x + t - x - t := by rel[hx]
      _ = 0 := by ring

  have H := le_or_gt x 1
  obtain hx1 | hx1 := H
  · have hx1': -(x - 1) >= 0 := by addarith[hx1]
    have h1' : -(x - 1)*(t - 1) > 0 := by addarith[h']
    cancel -(x - 1) at h1'
    have h2' : t > 1 := by addarith[h1']
    · apply ne_of_gt
      calc
          t
        _ > 1 := by addarith[h1']

  · have hx1'' : (x - 1) > 0 := by addarith[hx1]
    have h1' : (x - 1)*-(t - 1) > 0 :=
      calc
          (x - 1)*-(t - 1)
        _ = -(x-1) * (t-1) := by ring
        _ > 0 := by addarith[h']
    cancel (x - 1) at h1'
    apply ne_of_lt
    addarith[h1']

/-
example {a m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hx⟩ := h
  have H := le_or_gt x 2
  obtain hx1 | hx1 := H

  · apply ne_of_lt
    calc
        m
      _ = 2*x := by rw[hx]
      _ <= 2*2 := by rel[hx1]
      _ < 5 := by numbers

  · have H' := le_or_gt x 3
    obtain hx1' | hx1' := H'
    · apply ne_of_gt
      calc
          m
        _ = 2*x := by rw[hx]
        _ = 2*3 := by rel[hx1, hx1']
        _ = 6 := by numbers
        _ > 5 := by numbers

    · apply ne_of_gt
      calc
          m
        _ = 2*x := by rw[hx]
        _ > 2*3 := by rel[hx1']
        _ = 6 := by numbers
        _ > 5 := by numbers
-/


--- example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
---   sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a)/2, (a + c - b)/2, (a + b - c)/2

  constructor
  calc
      (b + c - a)/2
    _ >= 0/2 := by addarith[ha]
    _ = 0 := by ring

  constructor
  calc
      (a + c - b)/2
    _ >= 0/2 := by addarith[hb]
    _ = 0 := by ring

  constructor
  calc
      (a + b - c)/2
    _ >= 0/2 := by addarith [hc]
    _ = 0 := by ring

  constructor
  ring
  constructor
  ring
  ring
