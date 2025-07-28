theory Ex24 imports Main
begin

(*
Exercise 2.4. Define a recursive function snoc :: \<Zprime>a list \<Rightarrow> \<Zprime>a \<Rightarrow> \<Zprime>a list
that appends an element to the end of a list. With the help of snoc define
a recursive function reverse :: \<Zprime>a list \<Rightarrow> \<Zprime>a list that reverses a list. Prove
reverse (reverse xs) = xs.
*)

value "length []"

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count a [] = 0" |
  "count a (x#xs) = (if a = x then Suc (count a xs) else count a xs)"

theorem count_less_len : "(count a xs) \<le> (length xs)"
  apply(induction xs)
   apply(auto)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]" |
  "snoc l a = l @ [a]"

fun mrev :: "'a list \<Rightarrow> 'a list" where
  "mrev [] = []" |
  "mrev (x#xs) = snoc (mrev xs) x"


lemma snoc_append_singleton : "ys @ [a] = snoc ys a" 
  apply(induction ys)
   apply(auto)
  done

lemma snoc_append : "snoc (xs @ ys) a  = xs @ (snoc ys a)"
  apply (induction xs)
   apply (auto)
  apply(simp add: snoc_append_singleton)
  done

lemma mrev_distr [simp] : "mrev (xs @ ys) = (mrev ys) @ (mrev xs)"
  apply(induction xs)
   apply(auto)
  apply(simp add:snoc_append)
  done

lemma snoc_def : "snoc xs a = xs @ [a]"
  apply(induction xs)
   apply(auto)
  done

lemma mrev_snocced [simp] : "mrev (snoc xs a) = a # (mrev xs)"
  apply (induction xs)
   apply(simp add:snoc_append_singleton)
  apply(simp add:snoc_def)
  done

theorem mrev_mrev : "mrev (mrev xs) = xs"
  apply(induction xs)
  apply(auto)
  done

end
