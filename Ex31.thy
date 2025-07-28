theory Ex31 imports Main

begin

(*
Exercise 3.1. Start from the data type of binary trees defined earlier:
datatype \<Zprime>a tree= Tip | Node " \<Zprime>a tree" \<Zprime>a " \<Zprime>a tree"
Define a function set :: \<Zprime>a tree \<Rightarrow> \<Zprime>a set that returns the elements in a tree
and a function ord :: int tree \<Rightarrow>bool that tests if an int tree is ordered.
Define a function ins that inserts an element into an ordered int tree
while maintaining the order of the tree. If the element is already in the tree,
the same tree should be returned. Prove correctness of ins: set (ins x t ) =
{x } \<union>set t and ord t= \<Rightarrow>ord (ins i t ).

*)


datatype 'a tree= Tip | Node " 'a tree" 'a " 'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l a r) = {a} \<union> set l \<union> set r"

value "set (Node Tip (0::int) (Node Tip 1 (Node Tip 0 Tip)))"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l a r) = (ord l \<and> ord r \<and>  (\<forall>x \<in> (set l). x < a) \<and> (\<forall>y \<in>  (set r). y > a))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins n Tip = Node Tip n Tip" |
  "ins n (Node l a r) = 
    (if a = n then (Node l n r) else 
    (if n < a then (Node (ins n l) a r) else 
    (Node l a (ins n r))))"

theorem ins_corr1: "set (ins x t ) = {x } \<union> set t "
  apply(induction t)
   apply(auto)
  done

theorem ins_corr2 : "ord t \<Longrightarrow> ord (ins i t )"
  apply(induction t)
   apply(auto simp add: ins_corr1)
  done

end

