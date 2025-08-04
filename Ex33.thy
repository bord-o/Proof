theory Ex33 imports Main

begin
(*
Exercise 3.3. We could also have defined star as follows:
inductive star \<Zprime> :: "(\<Zprime>a \<Rightarrow> \<Zprime>a \<Rightarrow>bool ) \<Rightarrow> \<Zprime>a \<Rightarrow> \<Zprime>a \<Rightarrow>bool" for r where
refl \<Zprime>: "star \<Zprime> r x x" |
step \<Zprime>: "star \<Zprime> r x y= \<Rightarrow>r y z= \<Rightarrow>star \<Zprime> r x z"
The single r step is performed after rather than before the star \<Zprime> steps. Prove
star \<Zprime> r x y= \<Rightarrow>star r x y and star r x y= \<Rightarrow>star \<Zprime> r x y. You may need
lemmas. Note that rule induction fails if the assumption about the inductive
predicate is not the first assumption.
*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow>bool ) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow>bool ) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow>r y z \<Longrightarrow> star' r x z"

lemma path_one : "r x y \<Longrightarrow> star r x y"
  by (simp add: star.refl star.step)

lemma path_one' : "r x y \<Longrightarrow> star' r x y"
  by (meson refl' step')

lemma many_many: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(rule step)
   apply(simp_all)
  done

lemma many_many': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"
  apply(rule step')
   apply blast
  apply(blast)
  done

lemma tr1' : "star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z" 
  apply(induction rule:star'.induct)
   apply(simp)
  apply(rule step')
   apply(simp_all)
  done 

lemma many_many_star' : "r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply (meson path_one' tr1')
  done

lemma many_many_star : "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule:star.induct)
   apply(auto)
   apply(simp add:path_one)
  apply(simp add:many_many)
  done

lemma tr1 : "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z" 
  apply(induction rule:star.induct)
   apply(simp_all)
  apply(simp add:many_many)
  done

lemma eq1 : "star' r x y \<Longrightarrow> star r x y" 
  apply(induction rule:star'.induct)
   apply(simp add:star.refl)
  apply(simp add:many_many_star)
  done

lemma eq2 : "star r x y \<Longrightarrow> star' r x y" 
  apply(induction rule:star.induct)
   apply(simp add:refl')
  apply(simp add:many_many_star')
  done

(*
Exercise 3.4. Analogous to star, give an inductive definition of the n-fold
iteration of a relation r : iter r n x y should hold if there are x 0, . . . , x n such
that x = x 0, x n = y and r x i x i +1 for all i < n. Correct and prove the
following claim: star r x y= \<Rightarrow>iter r n x y.

*)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  zero: "iter r 0 x x" |
  succ: "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (Suc n) x z"

(* 3.4 SHould be iter \<Longrightarrow> star *)
theorem path_eq : "iter r n x y \<Longrightarrow> star r x y" 
  apply(induction rule:iter.induct)
   apply(auto simp add:many_many_star star.refl)
  done




end