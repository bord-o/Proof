theory Ex210 imports Main
begin
(*
Exercise 2.10. Define a datatype tree0 of binary tree skeletons which do not
store any information, neither in the inner nodes nor in the leaves. Define a
function 

nodes :: tree0 \<Rightarrow>nat 

that counts the number of all nodes (inner
nodes and leaves) in such a tree. Consider the following recursive function:

fun explode :: "nat \<Rightarrow>tree0 \<Rightarrow>tree0" where
"explode 0 t= t" |
"explode (Suc n ) t= explode n (Node t t )"

Find an equation expressing the size of a tree after exploding it 
(nodes(explode n t )) as a function of nodes t and n. Prove your equation. You
may use the usual arithmetic operators, including the exponentiation opera-
tor “^”. For example, 2^ 2= 4.

Hint: simplifying with the list of theorems algebra_simps takes care of
common algebraic properties of the arithmetic operators.
*)

datatype tree0 = Tip | Node tree0 tree0

fun explode :: "nat \<Rightarrow>tree0 \<Rightarrow>tree0" where
  "explode 0 t= t" |
  "explode (Suc n ) t= explode n (Node t t )"

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + (nodes l) + (nodes r)"

value "nodes (Node Tip (Node Tip Tip))"

theorem explode_factor : "nodes (explode n t) = ((2^(n)) * nodes t) + (2^n-1)"
  apply(induction n arbitrary:t)
   apply(auto simp add:algebra_simps)
  done
  

end