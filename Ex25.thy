theory Ex25 imports Main
begin

(*
Exercise 2.5. Define a recursive function sum
_ upto :: nat \<Rightarrow>nat such that
sum
_ upto n= 0 +... + n and prove sum
_ upto n= n \<^emph>(n + 1) div 2.
*)

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = Suc n + sum_upto n"


theorem sum_prop : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done

end