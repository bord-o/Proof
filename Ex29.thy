theory Ex29 imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc n) m = Suc (add n m)"


fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 m = m" |
  "itadd (Suc n) m = itadd n (Suc m)"

value "add 1 0"
value "itadd 4 6"

lemma add_args : "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply(auto)
  done

theorem both_adds : "itadd m n = add m n"
  apply(induction m arbitrary:n)
   apply(simp_all add:add_args)
  done


end