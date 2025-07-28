theory Tutorial imports Main
begin

datatype nat = Zero | Succ nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add Zero n = n" |
  "add (Succ n) m = Succ (add n m)"

lemma add_02[simp]: "add m Zero = m"
  apply(induction m)
  apply(auto)
  done

lemma add_swap [simp]: "add (Succ n) m = add n (Succ m)"
  apply(induction n)
   apply (auto)
  done

lemma add_swap2 : "Succ (add n m) = add n (Succ m)"
  apply(induction n)
   apply (auto)
  done
theorem assoc_add [simp]: "add x (add y z) = add (add x y) z"
  apply(induction x)
   apply(auto)
  done


theorem comm_add: "add x y = add y x"
  apply(induction x)
   apply(auto)
  apply(simp add:add_swap2)
  done
 



datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list => 'a list => 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list => 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"
declare [[names_short]]

value "rev(Cons True (Cons False Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
   apply(auto)
  done

lemma app_assoc [simp] : "app xs (app ys zs) = app (app xs ys) zs"
  apply (induction xs)
   apply(auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
   apply(auto)
  done

theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply(induction xs)
   apply(auto)
  done





end
