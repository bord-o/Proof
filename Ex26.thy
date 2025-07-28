theory Ex26 imports Main
begin

(*
Exercise 2.6. Starting from the type \<Zprime>a tree defined in the text, define a
function 

contents :: \<Zprime>a tree \<Rightarrow> \<Zprime>a list 

that collects all values in a tree in a list,
in any order, without removing duplicates. Then define a function 

sum_tree :: nat tree \<Rightarrow>nat 

that sums up all values in a tree of natural numbers and
prove 

sum_tree t= sum list (contents t ) 

where sum_list is predefined by
the equations 

sum_list [] = 0 and 
sum_list (x # xs) = x + sum_list xs.
*)
datatype 'a tree= Tip | Node " 'a tree" 'a " 'a tree"
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l value r) = value # (contents l) @ (contents r)"
fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l value r) =  value + sum_tree l + sum_tree r"


theorem sum_list_v_tree : "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done



end