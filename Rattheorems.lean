import MyProject.Rationals
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
--import Mathlib.Tactic
--import Std.Classes.BEq
import Mathlib.Data.Rat.Sqrt
--import Mathlib.SetTheory.ZFC.Basic
--import Mathlib.Init.Data.Int.Order
--import Mathlib.Data.Real.Basic

open ratproof
open Nat
open Finset

--- do pflfp

lemma linesfrom_p1_subset (p : Point) (S F : Finset Point) (hS : S ⊆ F) : linesfrom_p1 S p ⊆ linesfrom_p1 F p :=
by
  unfold linesfrom_p1 -- expand the definition
  apply biUnion_subset_biUnion_of_subset_left -- applying the subset relation on the right side of biUnion
  exact hS

lemma biunion_linesfrom_p1 (S F : Finset Point ) (h : S ⊆ F): Finset.biUnion S (linesfrom_p1 S) ⊆ Finset.biUnion F (linesfrom_p1 F):= by
  intros l hl
  simp only [Finset.mem_biUnion] at hl
  obtain ⟨p, hpS, hpL⟩ := hl -- l is a line in the set linesfrom_p1 S p, where p ∈ S

  -- Since p ∈ S and S ⊆ F, it follows that p ∈ F
  have hpF := h hpS

  -- Apply the subset lemma for linesfrom_p1 to find that linesfrom_p1 S p ⊆ linesfrom_p1 F p
  have hLines : linesfrom_p1 S p ⊆ linesfrom_p1 F p := linesfrom_p1_subset p S F h

  -- Since l is in the smaller set (linesfrom_p1 S p), it must be in the larger set (linesfrom_p1 F p)
  have hpFL : l ∈ linesfrom_p1 F p := hLines hpL

  -- Finally, show that l is in the union over F
  simp only [Finset.mem_biUnion]
  use p

lemma linesfrom_points_subset (S F : Finset Point) (h : S ⊆ F) : linesfrom_points S ⊆ linesfrom_points F :=
by
  unfold linesfrom_points
  exact biunion_linesfrom_p1 S F h

lemma pointsfrom_l1_subset (l : Line) (S F : Finset Line) (hS : S ⊆ F) : pointsfrom_l1 S l ⊆ pointsfrom_l1 F l :=
by
  unfold pointsfrom_l1
  apply biUnion_subset_biUnion_of_subset_left
  exact hS

lemma biunion_pointsfrom_l1 (S F : Finset Line) (h : S ⊆ F) :  Finset.biUnion S (pointsfrom_l1 S) ⊆ Finset.biUnion F (pointsfrom_l1 F) :=
by
  intros p hp
  simp only [Finset.mem_biUnion] at hp
  obtain ⟨l, hlS, hlP⟩ := hp
  have hlF := h hlS
  have hPoints := pointsfrom_l1_subset l S F h
  have hlFL := hPoints hlP
  simp only [mem_biUnion]
  use l

lemma pointsfrom_lines_subset (S F : Finset Line) (h: S ⊆ F) : pointsfrom_lines S ⊆ pointsfrom_lines F:=
by
  unfold pointsfrom_lines
  exact biunion_pointsfrom_l1 S F h

theorem points_from_lines_from_points_subset (S F : Finset Point) (h : S ⊆ F) : points_from_lines_from_points S ⊆ points_from_lines_from_points F :=
  by
  unfold points_from_lines_from_points
  have hlfp : linesfrom_points S ⊆ linesfrom_points F := linesfrom_points_subset S F h
  exact pointsfrom_lines_subset (linesfrom_points S) (linesfrom_points F) hlfp

--- now to pfcfp

lemma circlesfrom_p1_subset (p : Point) (S F : Finset Point) (hS : S ⊆ F) : circlesfrom_p1 S p ⊆ circlesfrom_p1 F p :=
by
  unfold circlesfrom_p1 -- expand the definition
  apply biUnion_subset_biUnion_of_subset_left -- applying the subset relation on the right side of biUnion
  exact hS

lemma biunion_circlesfrom_p1 (S F : Finset Point ) (h : S ⊆ F): Finset.biUnion S (circlesfrom_p1 S) ⊆ Finset.biUnion F (circlesfrom_p1 F):= by
  intros l hl
  simp only [Finset.mem_biUnion] at hl
  obtain ⟨p, hpS, hpL⟩ := hl -- l is a line in the set linesfrom_p1 S p, where p ∈ S

  -- Since p ∈ S and S ⊆ F, it follows that p ∈ F
  have hpF := h hpS

  -- Apply the subset lemma for linesfrom_p1 to find that linesfrom_p1 S p ⊆ linesfrom_p1 F p
  have hLines : circlesfrom_p1 S p ⊆ circlesfrom_p1 F p := circlesfrom_p1_subset p S F h

  -- Since l is in the smaller set (linesfrom_p1 S p), it must be in the larger set (linesfrom_p1 F p)
  have hpFL : l ∈ circlesfrom_p1 F p := hLines hpL

  -- Finally, show that l is in the union over F
  simp only [Finset.mem_biUnion]
  use p

lemma circlesfrom_points_subset (S F : Finset Point) (h : S ⊆ F) : circlesfrom_points S ⊆ circlesfrom_points F :=
by
  unfold circlesfrom_points
  exact biunion_circlesfrom_p1 S F h

lemma pointsfrom_c1_subset (c : Circle) (S F : Finset Circle) (hS : S ⊆ F) : pointsfrom_c1 S c ⊆ pointsfrom_c1 F c :=
by
  unfold pointsfrom_c1
  apply biUnion_subset_biUnion_of_subset_left
  exact hS

lemma biunion_pointsfrom_c1 (S F : Finset Circle) (h : S ⊆ F) :  Finset.biUnion S (pointsfrom_c1 S) ⊆ Finset.biUnion F (pointsfrom_c1 F) :=
by
  intros p hp
  simp only [Finset.mem_biUnion] at hp
  obtain ⟨c, hlS, hlP⟩ := hp
  have hlF := h hlS
  have hPoints := pointsfrom_c1_subset c S F h
  have hlFL := hPoints hlP
  simp only [mem_biUnion]
  use c

lemma pointsfrom_circles_subset (S F : Finset Circle) (h : S ⊆ F) : pointsfrom_circles S ⊆ pointsfrom_circles F :=
by
  unfold pointsfrom_circles
  exact biunion_pointsfrom_c1 S F h

theorem points_from_circles_from_points_subset (S F : Finset Point) (h : S ⊆ F) : points_from_circles_from_points S ⊆ points_from_circles_from_points F :=
  by
  unfold points_from_circles_from_points
  have hlfp : circlesfrom_points S ⊆ circlesfrom_points F := circlesfrom_points_subset S F h
  exact pointsfrom_circles_subset (circlesfrom_points S) (circlesfrom_points F) hlfp

--- now prove pflxcfp

lemma pointsfrom_l1xcs_subset (l : Line) (C D : Finset Circle) (H2 : C ⊆ D) : pointsfrom_l1xcs C l ⊆ pointsfrom_l1xcs D l :=
  by
  unfold pointsfrom_l1xcs
  apply biUnion_subset_biUnion_of_subset_left
  exact H2

lemma biunion_pointsfrom_l1xcs (L J : Finset Line) (C D : Finset Circle) (H1 : L ⊆ J) (H2 : C ⊆ D) :  Finset.biUnion L (pointsfrom_l1xcs C) ⊆ Finset.biUnion J (pointsfrom_l1xcs D) :=
  by
  intros p hp
  simp only [Finset.mem_biUnion] at hp
  obtain ⟨l, hlS, hlP⟩ := hp
  have hlF := H1 hlS

  have hPoints := pointsfrom_l1xcs_subset l C D H2
  have hlFL := hPoints hlP
  simp only [mem_biUnion]
  use l

lemma pointsfrom_lsxcs_subset (L J : Finset Line) (C D : Finset Circle) (H1 : L ⊆ J) (H2 : C ⊆ D): pointsfrom_lsxcs (L) (C) ⊆ pointsfrom_lsxcs (J) (D) :=
  by
  unfold pointsfrom_lsxcs
  exact biunion_pointsfrom_l1xcs L J C D H1 H2

theorem points_from_linexcircle_from_points_subset (S F : Finset Point) (h : S ⊆ F) : points_from_linexcircle_from_points S ⊆ points_from_linexcircle_from_points F :=
  by
  unfold points_from_linexcircle_from_points
  let lfp_s := linesfrom_points S
  let lfp_f := linesfrom_points F

  let cfp_s := circlesfrom_points S
  let cfp_f := circlesfrom_points F

  have lfp_sub : lfp_s ⊆ lfp_f := linesfrom_points_subset S F h
  have cfp_sub : cfp_s ⊆ cfp_f := circlesfrom_points_subset S F h

  have hh : pointsfrom_lsxcs (linesfrom_points S) (circlesfrom_points S) ⊆
  pointsfrom_lsxcs (linesfrom_points F) (circlesfrom_points F) := pointsfrom_lsxcs_subset lfp_s lfp_f cfp_s cfp_f lfp_sub cfp_sub
  exact hh

--- now comnime and show for o_s_c

theorem one_step_construction_subset (S F : Finset Point) (h : S ⊆ F) : one_step_construction S ⊆ one_step_construction F :=
  by
  unfold one_step_construction
  apply Finset.union_subset_union
  apply Finset.union_subset_union
  apply Finset.union_subset_union
  {
    exact h
  }
  {
    exact points_from_lines_from_points_subset S F h
  }
  {
    exact points_from_circles_from_points_subset S F h
  }
  {
    exact points_from_linexcircle_from_points_subset S F h
  }

lemma p_in_k_step_then_in_k1 (p: Point) : p ∈ n_step_construction (n) → p ∈ n_step_construction (succ n) :=
  by
  intro h
  unfold n_step_construction

  unfold one_step_construction
  rewrite [Finset.union_assoc,Finset.union_assoc]
  apply Finset.subset_union_left
  exact h

lemma p_q_in_union_in (p q : Point) (F: Finset Point) (H1 : p ∈ F) (H2 : q ∈ F):  {p,q} ⊆ F :=
by

  rw [subset_iff]
  intro x
  rw [mem_insert]
  intro hx
  cases' hx with c hc
  { rw  [ c]
    exact H1 }
  { rw [mem_singleton] at hc
    rw [ hc]
    exact H2 }

lemma k3_in_o_s_c : { x := ↑k + 1 + 1 + 1, y := 0 } ∈ one_step_construction {{ x := ↑k + 1, y := 0 }, { x := ↑k + 1 + 1, y := 0 }} :=
  by {
    unfold one_step_construction
    simp [points_from_linexcircle_from_points,circlesfrom_points, circlesfrom_p1, circled, BEq.beq]
    simp [distancepp,Rat.sqrt, Int.sqrt]
    ring_nf
    right
    right
    right
    simp [linesfrom_points,linesfrom_p1,lined,pointsfrom_lsxcs]
    simp [pointsfrom_l1xcs,linexcircle,discriminant,quad_formula_pos,quad_formula_neg]
    ring_nf
    simp [Rat.sqrt,Int.sqrt,sqrt,sqrt.iter,IsSquare]
    ring_nf
    right
    split_ifs with h1 h2
    {
      have h3 : ¬ (16: ℚ) < 12 := by {tauto}
      exfalso
      apply h3
      exact h2
    }
    {
      simp
    }
    {
      exfalso
      apply h1
      use 2
      rfl
    }
  }


lemma nat_constructable  (n : ℕ ) : {x := n + 1 , y := 0 : Point} ∈ n_step_construction (n):=
  by
  induction' n using Nat.twoStepInduction with k IH1 IH2
  --proof by induction from k1 and k2
  native_decide
  native_decide

  simp at IH2
  simp
  apply p_in_k_step_then_in_k1 at IH1

  have k1_k2_in_k1_steps : ({{ x := ↑k + 1, y := 0 }, { x := ↑k + 1 + 1, y := 0 }  } : Finset Point ) ⊆ n_step_construction (succ k) :=
    by { --{k1,k2} ∈ n_step_cons (k1)
      exact p_q_in_union_in ({ x := ↑k + 1, y := 0 }) ({ x := ↑k + 1 + 1, y := 0 }) (n_step_construction (succ k)) IH1 IH2
    }

  have o_s_c_subset : one_step_construction {{ x := ↑k + 1, y := 0 }, { x := ↑k + 1 + 1, y := 0 }} ⊆ n_step_construction (succ (succ k)) :=
    by { -- o_s_c {k1,k2} ⊆ n_s_c (k2)
      unfold n_step_construction
      have H := one_step_construction_subset {{ x := ↑k + 1, y := 0 }, { x := ↑k + 1 + 1, y := 0 }} (n_step_construction (succ k)) k1_k2_in_k1_steps
      exact H

    }
  have f := o_s_c_subset k3_in_o_s_c
  exact f


theorem n_constructable (n : ℕ) : constructable (n) := by {
  unfold constructable
  cases' n with h
  {
    use 0
    simp [n_step_construction, S]
    left
    native_decide
  }
  {
    simp
    use h
    exact nat_constructable h
  }
}
