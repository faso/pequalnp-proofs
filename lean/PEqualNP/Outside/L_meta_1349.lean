import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

def level (h i : ℕ) : ℕ :=
  if i = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1
  else if i = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (i - 1) - 2 ^ h

def weight (h i : ℕ) : ℕ :=
  if i = h + 2 then 2 ^ h else 2 ^ (i - 1) - 1

def game (h : ℕ) (P : Finset ℕ) : ℕ :=
  ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
    (fun uv => (level h uv.1 - level h uv.2) * weight h uv.2)

lemma middle (h i : ℕ) (hi : 1 ≤ i) (hh : i ≤ h + 1) :
    level h i = (2 ^ h + 1) * 2 ^ (h + 1 - i) - 2 ^ h := by
  have hf : (2 : ℕ) ^ h = 2 ^ (h + 1 - i) * 2 ^ (i - 1) := by
    rw [← pow_add]; congr 1; omega
  unfold level
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  conv_lhs => lhs; lhs; lhs; rw [hf]
  rw [show 2 ^ (h + 1 - i) * 2 ^ (i - 1) * (2 ^ h + 1) =
    (2 ^ h + 1) * 2 ^ (h + 1 - i) * 2 ^ (i - 1) by ring,
    Nat.mul_div_cancel _ (by positivity)]

lemma start_level (h a : ℕ) (ha : a ≤ h + 1) :
    (2 ^ h + 1) * 2 ^ (h + 1 - max 1 a) - 2 ^ h ≤ level h a := by
  cases a with
  | zero =>
    calc
      _ ≤ (2 ^ h + 1) * 2 ^ h := by simp
      _ ≤ level h 0 := by simp [level, Nat.add_mul]
  | succ a => rw [middle h _ (by omega) ha, max_eq_right (by omega)]

lemma half_sq (h : ℕ) (hh : 1 ≤ h) : 2 ^ h * 2 ^ h / 2 = 2 ^ h * 2 ^ (h - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  simp [Nat.pow_succ, ← Nat.mul_assoc]

lemma interval (h a b : ℕ) (hh : 1 ≤ h) (hab : a ≤ b) (he : b ≤ h + 2) :
    2 ^ h * 2 ^ h / 2 * (2 ^ (b - a - 1) - 1) ≤
      (level h a - level h b) * weight h b := by
  by_cases hs : b ≤ a + 1
  · simp [show b - a - 1 = 0 by omega]
  have ha : a ≤ h + 1 := by omega
  have hq : 0 < (2 : ℕ) ^ h := by positivity
  have hslev := start_level h a ha
  by_cases hend : b = h + 2
  · subst b
    rw [show weight h (h + 2) = 2 ^ h by simp [weight],
      show level h (h + 2) = 0 by simp [level], Nat.sub_zero]
    by_cases hz : a = 0
    · subst a
      rw [show level h 0 = 2 ^ h * 2 ^ h + 2 ^ h + 1 by simp [level], Nat.sub_zero]
      rw [show h + 2 - 1 = h + 1 by omega, pow_succ]
      have hhalf := Nat.div_mul_le_self (2 ^ h * 2 ^ h) 2
      have := Nat.mul_le_mul_right (2 ^ h) hhalf
      have hle : 2 ^ h * 2 - 1 ≤ 2 ^ h * 2 := Nat.sub_le _ _
      calc
        _ ≤ (2 ^ h * 2 ^ h / 2) * (2 ^ h * 2) := Nat.mul_le_mul_left _ hle
        _ = (2 ^ h * 2 ^ h / 2 * 2) * 2 ^ h := by ac_rfl
        _ ≤ (2 ^ h * 2 ^ h) * 2 ^ h := this
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · rw [max_eq_right (by omega : 1 ≤ a)] at hslev
      rw [show h + 2 - a - 1 = h + 1 - a by omega]
      have hp : 0 < (2 : ℕ) ^ (h + 1 - a) := by positivity
      have heq : 2 ^ (h + 1 - a) - 1 + 1 = 2 ^ (h + 1 - a) := by omega
      have hmul := congrArg (fun x : ℕ => 2 ^ h * x) heq
      have hlev : 2 ^ h * (2 ^ (h + 1 - a) - 1) ≤ level h a := by
        change 2 ^ h * (2 ^ (h + 1 - a) - 1 + 1) = 2 ^ h * 2 ^ (h + 1 - a) at hmul
        rw [Nat.mul_add, Nat.mul_one] at hmul
        rw [Nat.add_mul, Nat.one_mul] at hslev
        omega
      calc
        _ ≤ (2 ^ h * 2 ^ h) * (2 ^ (h + 1 - a) - 1) :=
          Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        _ = (2 ^ h * (2 ^ (h + 1 - a) - 1)) * 2 ^ h := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ hlev
  · have hb : 2 ≤ b := by omega
    have hbh : b ≤ h + 1 := by omega
    let R := 2 ^ (h + 1 - b)
    let S := 2 ^ (b - max 1 a)
    have hr : 0 < R := by dsimp [R]; positivity
    have hS : 0 < S := by dsimp [S]; positivity
    have hex : 2 ^ (h + 1 - max 1 a) = R * S := by
      dsimp [R,S]; rw [← pow_add]; congr 1; omega
    rw [hex] at hslev
    have hleR : 2 ^ h ≤ (2 ^ h + 1) * R := by nlinarith
    have hsR : (2 ^ h + 1) * R ≤ (2 ^ h + 1) * (R * S) := by
      calc
        _ ≤ ((2 ^ h + 1) * R) * S := Nat.le_mul_of_pos_right _ hS
        _ = _ := by ring
    have hge := Nat.sub_add_cancel (hleR.trans hsR)
    have hge' := Nat.sub_add_cancel hleR
    have hd : (2 ^ h + 1) * R * (S - 1) ≤ level h a - level h b := by
      rw [middle h b (by omega) hbh]
      change _ ≤ level h a - ((2 ^ h + 1) * R - 2 ^ h)
      have hm : (2 ^ h + 1) * R * (S - 1) + (2 ^ h + 1) * R =
          (2 ^ h + 1) * (R * S) := by
        rw [← Nat.mul_succ, show (S - 1).succ = S by omega]; ring
      omega
    have hw : 2 ^ (b - 2) ≤ weight h b := by
      unfold weight; rw [ite_eq_right hend, show b - 1 = (b - 2) + 1 by omega, pow_succ]
      have hp : 0 < (2 : ℕ) ^ (b - 2) := by positivity
      omega
    have hprod : R * 2 ^ (b - 2) = 2 ^ (h - 1) := by
      dsimp [R]; rw [← pow_add]; congr 1; omega
    have hsmall : (2 : ℕ) ^ (b - a - 1) - 1 ≤ S - 1 := by
      apply Nat.sub_le_sub_right
      apply Nat.pow_le_pow_right (by decide)
      omega
    rw [half_sq h hh, ← hprod]
    calc
      _ ≤ (2 ^ h + 1) * (R * 2 ^ (b - 2)) * (S - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ _)) hsmall
      _ = ((2 ^ h + 1) * R * (S - 1)) * 2 ^ (b - 2) := by ring
      _ ≤ _ := Nat.mul_le_mul hd hw

lemma score (h K : ℕ) (hh : 1 ≤ h) (P : Finset ℕ)
    (hc : P.card + 1 ≤ K) :
    2 ^ h * 2 ^ h / 2 * (2 ^ ((h + 2) / K - 1) - 1) ≤ game h P := by
  let d := (h + 2) / K
  change 2 ^ h * 2 ^ h / 2 * (2 ^ (d - 1) - 1) ≤ _
  by_cases hz : d = 0
  · simp [hz]
  have hd : 0 < d := Nat.pos_of_ne_zero hz
  obtain ⟨i, hi, hfree⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (P.image (fun w => (w - 1) / d)).card < (Finset.range K).card from
      lt_of_le_of_lt Finset.card_image_le (by rw [Finset.card_range]; omega))
  have hiK := Finset.mem_range.mp hi
  have hend : (i + 1) * d ≤ h + 2 := calc
    _ ≤ K * d := Nat.mul_le_mul_right _ (by omega)
    _ = d * K := Nat.mul_comm _ _
    _ ≤ _ := Nat.div_mul_le_self _ _
  have hlen : (i + 1) * d = i * d + d := Nat.succ_mul i d
  have hs : i * d ≤ (i + 1) * d := by omega
  have hgood : ∀ w ∈ P, ¬ (i * d < w ∧ w ≤ (i + 1) * d) := by
    rintro w hw ⟨hl,hr⟩
    apply hfree
    exact Finset.mem_image.mpr ⟨w, hw, Nat.div_eq_of_lt_le (by omega) (by omega)⟩
  have hmem : (i * d, (i + 1) * d) ∈
      (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      hs, hgood⟩
  have h := interval h (i * d) ((i + 1) * d) hh hs hend
  rw [show (i + 1) * d - i * d = d by omega] at h
  exact h.trans (Finset.le_sup (f := fun uv => (level _ uv.1 - level _ uv.2) * weight _ uv.2) hmem)

lemma total (h K : ℕ) (hh : 1 ≤ h) (hk : 0 < K) :
    2 ^ h * 2 ^ h / 2 * (2 ^ ((h + 3 + K - 1) / K - 1 - 1) - 1) ≤
    WithTop.untopD 0 ((((Finset.range (h + 3)).powerset.filter
      (fun P : Finset ℕ => P.card + 1 ≤ K)).image (game h)).min) := by
  let sets := (Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ K)
  have hemp : ∅ ∈ sets := by simp [sets]; omega
  obtain ⟨m, hm⟩ := Finset.min_of_mem (Finset.mem_image_of_mem (game h) hemp)
  change _ ≤ WithTop.untopD 0 ((sets.image (game h)).min)
  rw [hm, WithTop.untopD_coe]
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
  have hc := (Finset.mem_filter.mp hP).2
  rw [show h + 3 + K - 1 = h + 2 + K by omega, Nat.add_div_right _ hk]
  simpa using score h K hh P hc

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  exact PEqualNP.Outside.L_meta_1349.total h (2 ^ t) hh (by positivity)
