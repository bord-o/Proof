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
lemma "ys zs. xs = ys @ zs \<and>
(length ys= length zs \<or> length ys= length zs + 1)"
Hint: There are predefined functions take :: nat \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list and drop
:: nat \<Rightarrow> \<Zprime>a list \<Rightarrow> \<Zprime>a list such that take k [x 1,. . .] = [x 1,. . .,x k] and drop
k [x 1,. . .] = [x k +1,. . .]. Let sledgehammer find and apply the relevant take
and drop lemmas for you.
*)

(*
This is essentially saying that for every list xs there exist a ys and zs
such that their lengths are equal, or zs is one item longer (there is a perfect or 
imperfect split for every list)
*)
value "(0::nat) mod (2::nat)"

lemma "\<exists>ys zs. xs = ys @ zs \<and>
(length ys= length zs \<or> length ys= length zs + 1)"
proof -
  let ?n = "length xs"
  let ?pivot_idx = "(?n + 1) div 2"
  let ?ys = "take ?pivot_idx xs"
  let ?zs = "drop ?pivot_idx xs"

  have length_cases: "length ?ys= length ?zs \<or> length ?ys= length ?zs + 1"
  proof (cases "?n mod 2 = 0")
    case True
    then show ?thesis
      by auto
  next
    case False
    then show ?thesis 
      by auto
  qed
  show ?thesis
    by (metis append_take_drop_id length_cases)
qed

  
  
end



(*
  let ?pivot_idx = "length xs div 2"
  let ?ys = "take pivot_idx xs"
  let ?zs = "drop pivot_idx xs"
  assume "length xs = 0"
  obtain ys where "ys = ?ys" by blast
  obtain zs where "zs = ?zs" by blast
  have "?pivot_idx = 0" by (simp add: \<open>length xs = 0\<close>)
  hence "length ?ys = 0" by (simp add: \<open>length xs = 0\<close>)
  hence "length ?zs = 0" by (simp add: \<open>length xs = 0\<close>)
  thus "length ?ys = length ?zs" using \<open>length (take pivot_idx xs) = 0\<close> by fastforce
*)