import topology.metric_space.basic

open metric

variables (α : Type) [metric_space α] (x : α) (ε : ℝ)

theorem small_ball_big_ball : ∀ p ∈ ball x ε, ∃ δ, ball p δ ⊆ ball x ε :=
begin
    intros,
    -- simp at *,
    unfold ball,
    use (ε - dist p x),
    norm_num,
    intros a ha,
    have ha' : dist a p + dist p x < ε, by linarith,
    have ha'' : dist a x ≤ dist a p + dist p x, by exact dist_triangle a p x,
    exact gt_of_gt_of_ge ha' ha'',
end

theorem for_closed_balls : 
∀ p ∈ closed_ball x ε, 
∃ δ, closed_ball p δ ⊆ closed_ball x ε :=
begin
    intros,
    simp at *,
    unfold closed_ball,
    use (ε - dist p x),
    norm_num,
    intros a ha,
    have ha' : dist a p + dist p x ≤ ε, by linarith,
    have ha'' : dist a x ≤ dist a p + dist p x, by exact dist_triangle a p x,
    exact ge_trans ha' ha'',
end

theorem small_ball_big_ball_fixed : ∀ p ∈ ball x ε, ∃δ>0, ball p δ ⊆ ball x ε :=
begin -- this is the same theorem as `exists_ball_subset_ball` in mathlib.
    intros,
    simp at *,
    unfold ball,
    use (ε - dist p x),
    norm_num,
    split,
    {exact H},
    {
        intros a ha,
        have ha' : dist a p + dist p x < ε, by linarith,
        have ha'' : dist a x ≤ dist a p + dist p x, by exact dist_triangle a p x,
        exact gt_of_gt_of_ge ha' ha'',
    },
end

theorem for_closed_balls_fixed : -- I tried the same proof but it fails.
∀ p ∈ closed_ball x ε, 
∃δ>0, closed_ball p δ ⊆ closed_ball x ε :=
begin
    intros,
    simp at *,
    unfold closed_ball,
    -- we will use this as the radius of the ball around p.
    let Δ := (ε - dist p x),
    have h1 : 0 ≤ Δ, by simp only [sub_nonneg, H],
    use Δ,
    split,
    {   
        /-
        proof impossible with the provided information
        -/
        sorry
    },
    {   -- this part contains proof that for the used Δ, which the previous part 
        -- tries to show is > 0, it holds that closed_ball p δ ⊆ closed_ball x ε.
        intros a ha,
        norm_num at *,
        have ha' : dist a p + dist p x ≤ ε, {
            change Δ with (ε - dist p x) at ha,
            linarith,
        },
        have ha'' : dist a x ≤ dist a p + dist p x, by exact dist_triangle a p x,
        exact ge_trans ha' ha'',
    }
end

/--
Given a δ sphere around y, this defines the set of points on the sphere that are as far 
away as possible from a reference point x.
-/
def far_point (y : α) {δ : ℝ} (x : α) : set α := {p ∈ sphere y δ | ∀ z ∈ sphere y δ, dist y x ≥ dist z x}

/--
This shows that the set given by far_point is actually single element.
-/
theorem far_point_unique (y : α) {δ : ℝ} (x : α) : 

lemma exists_point_outside_sphere (p : α) (hp : p ∈ sphere x ε) : 
∀δ>0, ∃q∈sphere p δ, dist q x > ε :=
begin
    --     x  x 
    --  x       -x-
    -- x      /   x \
    -- x      \   x /
    --  x       -x- 
    --     x  x
    intros δ hδ,
    simp only [exists_prop, gt_iff_lt, mem_closed_ball],
    unfold sphere at *,
    simp at *,

    sorry
end

theorem point_outside_ball_2 (p : α) (hp : dist p x = ε) : 
¬∃δ>0, closed_ball p δ ⊆ closed_ball x ε :=
begin
    --     x  x 
    --  x       -x-
    -- x      /   x \
    -- x      \   x /
    --  x       -x- 
    --     x  x
    unfold closed_ball,
    norm_num at *,
    intros δ hδ, -- great, we now just need to provide such point!
    -- take a point q on the metric space,
    -- such that it is a distance δ away from the point p,
    -- let δ_sphere_around_p := {y:α | dist y p = δ},
    -- and such that it is as far away as possible from the point x.
    let far_from_x := {y ∈ sphere p δ | ∀ z ∈ sphere p δ, dist y x ≥ dist z x},
    
    sorry
end

-- STRATEGY FOR FINDING OUT WHETHER SOMETHING EXISTS: TRY TO PROVE BOTH CASES

/-
A thing either exists: There exists a non-zero open ball with only one element.
-/
theorem exists_singleton_ball : ∃ ε > 0, ∃ p, ball x ε = {p} :=
begin
    simp only [exists_prop, gt_iff_lt],
    
end

/-
Or does not exist: There does not exist a non-zero open ball with only one element.
-/
theorem not_exists_singleton_ball : ¬∃ ε > 0, ∃ p, ball x ε = {p} :=
begin
    simp only [not_exists, exists_prop, not_and, ge_iff_le],
    intros ε hε p,
    intro H,
    unfold ball at H,
    simp at *,
    -- it's all about the cardinality: The important thing that hypothesis H
    -- implies is that there does not exist an element q ≠ p such that `dist q x < ε`.
    -- If we can extract a false from this we would be done.

    sorry
end

theorem not_exists_singleton_ball' : ¬∃ {p}, ∃ ε > 0, ball x ε = {p} :=
begin
    simp,
    intros p ε hε,
    intro H,
    unfold ball at H,
    -- same state as above.

    sorry
end

lemma tmpo_false : ∀ ε > 0, ¬ ∃ p ∈ ball x ε, p = x → false :=
begin
    intros ε hε,
    simp,
    intros p hpx,
    /-
    proof impossible.
    -/
    sorry
end

/-
Is the statement true?
-/
lemma tmpo_true : ∀ ε > 0, ¬ ∃ p ∈ ball x ε, p = x → true :=
begin
    intros ε hε,
    simp,
    intro p,
    /-
    proof impossible.
    -/
    sorry
end

/-
May be the way we stated it was wrong.
-/
lemma tmpo_true_2 : ∀ ε > 0, ∃ p ∈ ball x ε, p ≠ x :=
begin
    intros ε hε,
    simp only [exists_prop, mem_ball, ne.def],
    
    sorry
end

/-
Open balls are not enumerable sets.
-/
theorem openness_of_open_balls : ∀ ε > 0, ∃ p ≠ x, p ∈ ball x ε := 
begin
    intros ε hε,
    simp,
    -- use the p for which dist x p = ε/2,
    -- Proof that p ≠ x : dist p x ≠ 0,
    -- Proof that dist p x < ε: dist p x = ε / 2,
end

theorem openness_of_open_balls''' : ∀ ε > 0, ∃ p, dist x p > 0 ∧ dist x p < ε := 
begin
    intros ε hε,
    simp,
    -- use the p for which dist x p = ε/2,
end

theorem openness_of_open_balls' : ∀ ε > 0, ∀ p₁ ∈ ball x ε, ∃ p₂, dist x p₂ > dist x p₁ := 
begin
    intros ε hε p₁ hp₁,
    unfold ball at hp₁, simp at hp₁,
    -- use the p₂ for which dist x p₂ = ε - dist x p₁,
end 

theorem openness_of_open_balls'' : ∀ ε > 0, ∀ p₁ ∈ ball x ε, ∃ p₂, dist x p₂ > dist x p₁ := 
begin
    intros ε hε p₁ hp₁,
    unfold ball at hp₁, simp at hp₁,
    -- use the p₂ for which dist x p₂ = ε - dist x p₁,
end 
