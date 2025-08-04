theory Ex32 imports Main
begin

(*
Exercise 3.2. Formalize the following definition of palindromes
• The empty list and a singleton list are palindromes.
• If xs is a palindrome, so is a # xs @ [a].
as an inductive predicate 

palindrome :: \<Zprime>a list \<Rightarrow>bool 

and prove that 

rev xs = xs if xs is a palindrome.
*)


fun pal :: "'a list \<Rightarrow> bool" where
  "pal [] = True" |
  "pal [n] = True" |
  "pal (x#xs) = (x = last xs \<and> pal (butlast xs)) "

value "tl [(1::nat), 2, 3]"
(*
inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome []" |
  singleton: "palindrome [n]" |
  many : "((hd l) = (last l)) \<Longrightarrow> palindrome (butlast (tl l)) \<Longrightarrow> palindrome l"

value "butlast (tl [(1::nat), 2, 3, 4, 5])"
*)


inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome []" |
  singleton: "palindrome [n]" |
  many: "palindrome xs \<Longrightarrow> palindrome ((a # xs) @ [a])"

lemma "palindrome [1,2,1]" 
  using many singleton by force

lemma rev_pal : "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule:palindrome.induct)
    apply(simp_all)
  done
  
  
  
  

end