theory Ex28 imports Main
begin

(*
Exercise 2.8. Define a function 

intersperse :: \<Zprime>a \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list 

such that 

intersperse a [x 1, ..., x n] = [x 1, a, x 2, a, ..., a, x n] 

Now prove that

map f (intersperse a xs) = intersperse (f a ) (map f xs).
*)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a (x#[]) = [ x]" |
  "intersperse a (x#xs) = x # a # (intersperse a xs)"

value "intersperse (99::nat) [1, 2, 3, 4]"

theorem map_eq : "map f (intersperse a xs) = intersperse (f a) (map f xs)" 
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done


end