theory Ex27 imports Main
begin

(*
Exercise 2.7. Define the two functions pre_order and post_order of type

\<Zprime>a tree \<Rightarrow> \<Zprime>a list 

that traverse a tree and collect all stored values in the
respective order in a list. Prove 

pre_order (mirror t ) = rev (post_order t ).

*)
datatype 'a tree= Tip | Node " 'a tree" 'a " 'a tree"


fun mirror :: " 'a tree => 'a tree" where
"mirror Tip= Tip" |
"mirror (Node l a r ) = Node (mirror r ) a (mirror l )"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Tip = []" |
  "pre_order (Node l a r) = a # (pre_order l @ pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Tip = []" |
  "post_order (Node l a r) = (post_order l @ post_order r) @ [a]"

theorem pre_post_corr : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply (simp_all)
  done

end
