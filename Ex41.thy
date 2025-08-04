theory Ex41 imports Main

begin
(*
Exercise 4.1. Give a readable, structured proof of the following lemma:
lemma assumes T : "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x −\<rightarrow>x = y"
and TA: "\<forall>x y. T x y −\<rightarrow>A x y" and "A x y"
shows "T x y"
*)

lemma assumes T : "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
  show "T x y"
    using A T TA assms(4) by blast
qed

value "length [(1::nat), 2, 3]"

(*
Exercise 4.2. Give a readable, structured proof of the following lemma:
lemma "\<exists>ys zs. xs = ys @ zs \<and>
(length ys= length zs \<or> length ys= length zs + 1)"
Hint: There are predefined functions take :: nat \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list and drop
:: nat \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list such that take k [x 1,. . .] = [x 1,. . .,x k] and drop
k [x 1,. . .] = [x k +1,. . .]. Let sledgehammer find and apply the relevant take
and drop lemmas for you.
*)
lemma "\<exists>ys zs. xs = ys @ zs \<and>
(length ys= length zs \<or> length ys= length zs + 1)"
proof 
  let ?ys = "take (length ys) ys"

end