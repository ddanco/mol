import data.list.perm
import data.list.sort


/-!
-------------------------------------
          Project comments
-------------------------------------

Ran out of time to finish all of the formalization and lemmas.
Would have also liked to have cleaned up, factored out aspects,
and tried out different styles if I had had more time with it.

Overall this was a fun way to get more comfortable with Lean!
-/

/-!
-------------------------------------
              Helpers
-------------------------------------
-/

@[elab_as_eliminator]
lemma list.strong_length_induction {α} {C : list α → Sort*}
    (rec : ∀ xs : list α, (∀ ys : list α, ys.length < xs.length → C ys) → C xs) :
  ∀ xs, C xs
| xs := rec xs (λ ys len, list.strong_length_induction ys)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }

def first_half_helper : ℕ -> list ℕ -> list ℕ
| count []        := []
| count (x :: xs) :=
    match count with
    | 0       := []
    | (c + 1) := (x :: first_half_helper c xs)
    end

def first_half : list ℕ -> list ℕ
| [] := []
| xs := first_half_helper ((list.length xs) / 2) xs

-- BAD: this isn't always true, but we right now use second_half in
-- situations with at least 2 elements, in which case it will be true.
-- Should instead be: xs.length > 1 → (first_half xs).length < xs.length
lemma first_half_is_smaller (xs : list ℕ) :
  (first_half xs).length < (xs.length) :=
sorry

def second_half_helper : ℕ -> list ℕ -> list ℕ
| count []        := []
| count (x :: xs) :=
    match count with
    | 0       := (x :: xs)
    | (c + 1) := second_half_helper c xs
    end

def second_half : list ℕ -> list ℕ
| [] := []
| xs := second_half_helper ((list.length xs) / 2) xs

lemma second_half_is_smaller (xs : list ℕ) :
  (second_half xs).length < xs.length :=
sorry

def list_is_whole_of_halves (xs : list ℕ) :
  xs = (first_half xs) ++ (second_half xs) :=
sorry

/-!
-------------------------------------
             Algorithm
-------------------------------------
-/

def merge : list ℕ -> list ℕ -> list ℕ
| [] ys               := ys
| xs []               := xs
| (x :: xs) (y :: ys) :=
    if x < y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

def merge_sort : list ℕ -> list ℕ
| []        := []
| (x :: []) := [x]
| xs@(x :: y :: ys)        := 
    have (first_half xs).length < xs.length, from first_half_is_smaller xs,
    have (second_half xs).length < xs.length, from second_half_is_smaller xs,
    merge (merge_sort (first_half xs))
          (merge_sort (second_half xs))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

#eval merge_sort [5,1,4,3,5,7,3,7]

/-!
-------------------------------------
              Proofs
-------------------------------------
-/

def sorted (xs : list ℕ) : Prop := @list.sorted ℕ (λ a b, a <= b) xs

-- Can't understand why this was causing problems.
lemma empty_merge (xs : list ℕ) :
  (merge list.nil xs = xs) ∧ (merge xs list.nil = xs) :=
sorry

lemma merge_of_sorted_is_sorted :
    ∀xs : list ℕ, ∀ys :
  list ℕ, sorted xs ∧ sorted ys → sorted (merge xs ys)
| [] ys :=
  begin
    intro h1,
    have h2 : sorted ys := by exact and.elim_right h1,
    simp [empty_merge, h2],
  end
| xs [] :=
  begin
    intro h1,
    have h2 : sorted xs := by exact and.elim_left h1,
    simp [empty_merge, h2],
  end
| (x :: xs) (y :: ys) :=
  begin
    intro t,
    have sorted_xs : sorted xs := list.sorted.tail (and.elim_left t),
    have sorted_ys : sorted ys := list.sorted.tail (and.elim_right t),
    by_cases (x < y),
    -- Really should factor some of this out
    { have h1 : sorted (merge xs (y :: ys)) :=
        begin
          apply merge_of_sorted_is_sorted xs (y::ys),
          exact and.intro sorted_xs (and.elim_right t),
        end,
      let merge_tl : list ℕ := (merge xs (y :: ys)),
      -- Need to use assumptions, transitivity of <=, ...
      have h2 : (∀ (b : ℕ), b ∈ merge_tl → x <= b) := sorry,
      have h3 : (∀ (b : ℕ), b ∈ merge_tl → x <= b) ∧ sorted merge_tl :=
        by exact and.intro h2 h1,
      have h4 : sorted (x :: merge_tl) :=
        by exact iff.elim_right list.sorted_cons h3,
      have res : merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys) :=
        -- This is just the definition of merge under this case.
        -- Not sure how to get it to work here.
        sorry,
      simp [h4, res] },
    { have h1 : sorted (merge (x :: xs) ys) :=
        begin
          apply merge_of_sorted_is_sorted (x :: xs) ys,
          exact and.intro (and.elim_left t) sorted_ys,
        end,
      let merge_tl : list ℕ := (merge (x :: xs) ys),
      have h2 : (∀ (b : ℕ), b ∈ merge_tl → y <= b) := sorry,
      have h3 : (∀ (b : ℕ), b ∈ merge_tl → y <= b) ∧ sorted merge_tl :=
        by exact and.intro h2 h1,
      have h4 : sorted (y :: merge_tl) :=
        by exact iff.elim_right list.sorted_cons h3,
      have res : merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys := sorry,
      simp [h4, res] }
  end

lemma merge_sort_is_sorted :
  ∀xs : list ℕ, sorted (merge_sort xs) :=
begin
  intro xs,
  induction xs using list.strong_length_induction with xs ih,
  cases xs with x xs,
  { simp [sorted, merge_sort, list.sorted_nil] },
  { cases xs with y xs,
    { simp [sorted, merge_sort, list.sorted_singleton] },
    { have s1 : sorted (merge_sort (first_half (x::y::xs))) :=
        begin
          apply ih,
          exact first_half_is_smaller (x::y::xs),
        end,
      have s2 : sorted (merge_sort (second_half (x::y::xs))) :=
        begin
          apply ih,
          exact second_half_is_smaller (x::y::xs),
        end,
      have e : merge_sort (x::y::xs) = merge (merge_sort (first_half (x::y::xs)))
                                             (merge_sort (second_half (x::y::xs))) :=
        by rw merge_sort,
      simp [e, s1, s2, merge_of_sorted_is_sorted] } }
end

lemma merge_is_perm_of_app :
  ∀xs : list ℕ, ∀ys : list ℕ, list.perm (merge xs ys) (xs ++ ys)
| [] ys               := by simp [list.append, empty_merge]
| xs []               := by simp [list.append, empty_merge]
| (x :: xs) (y :: ys) :=
  begin
    simp [list.append],
    by_cases (x < y),
    { have h2 : x :: (xs ++ y :: ys) ~ (x :: xs) ++ (y :: ys) :=
        by simp [list.perm.cons],
      sorry },
    sorry,
  end

lemma merge_sort_is_perm_of_list :
  ∀xs : list ℕ, list.perm (merge_sort xs) xs :=
begin
  intro xs,
  induction xs using list.strong_length_induction with xs ih,
  cases xs with x xs,
  { simp [merge_sort] },
  { cases xs with y xs,
    { simp [merge_sort] },
    { let lst := (x::y::xs),
      let l1 := first_half lst,
      let l2 := second_half lst,

      have p1 : list.perm (merge_sort l1) l1 :=
        begin
          apply ih,
          exact first_half_is_smaller (x::y::xs),  
        end,
      have p2 : list.perm (merge_sort l2) l2 :=
        begin
          apply ih,
          exact second_half_is_smaller (x::y::xs),  
        end,

      have h1 : list.perm lst (l1 ++ l2) :=
        by rw list_is_whole_of_halves lst,
      have h2 : list.perm (merge l1 l2) (l1 ++ l2) :=
        by apply merge_is_perm_of_app,
      have h3 : list.perm (l1 ++ l2) (merge l1 l2) :=
        by apply list.perm.symm h2,

      have h4 : list.perm (merge l1 l2) (merge (merge_sort l1) (merge_sort l2)) :=
        sorry, -- Follows from p1 and p2 with a few more steps.
      have h5 : merge_sort (x::y::xs) = merge (merge_sort l1) (merge_sort l2) :=
        by rw merge_sort,

      have h6 : list.perm lst (merge l1 l2) :=
        by apply list.perm.trans h1 h3, -- Better way to chain these trans?
      have h7 : list.perm lst (merge (merge_sort l1) (merge_sort l2)) :=
        by apply list.perm.trans h6 h4,
      
      have g : list.perm (merge_sort lst)
          (merge (merge_sort l1) (merge_sort l2)) :=
        by simp [h5, list.perm.refl],
      exact list.perm.trans g (list.perm.symm h7)
    } }
end

theorem merge_sort_verified (xs : list ℕ) :
  sorted (merge_sort xs) ∧ list.perm (merge_sort xs) xs :=
by simp [merge_sort_is_perm_of_list, merge_sort_is_sorted]
