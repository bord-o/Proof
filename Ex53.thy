theory Ex53 imports Main

begin

(*

Exercise 5.3. Give a structured proof by rule inversion:
lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
*)
inductive ev :: "nat \<Rightarrow>bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow>bool" where
  "evn 0= True" |
  "evn (Suc 0) = False" |
  "evn (Suc(Suc n)) = evn n"

lemma assumes a : "ev (Suc(Suc n))" shows "ev n"
proof -
  from a show "ev n"
  proof cases
    case evSS
    show ?thesis 
      by (simp add:local.evSS)
  qed
qed

(*

Exercise 5.4. Give a structured proof of\<not> ev (Suc (Suc (Suc 0))) by rule
inversions.Iftherearenocasestobeprovedyoucancloseaproofimmediately
with qed.
*)

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof 
  assume "ev (Suc (Suc (Suc 0)))"
  then show False
  proof cases
    case evSS
    show False
      by (metis \<open>ev (Suc (Suc (Suc 0)))\<close> ev.cases nat.distinct(1) nat.inject)
  next
  qed
qed

(*
Exercise 5.6. Define a recursive function elems :: \<Zprime>a list \<Rightarrow>\<Zprime>a set and prove
x \<in>elems xs= \<Rightarrow>\<exists>ys zs. xs = ys @ x # zs \<and> x / \<in>elems ys.

*)
fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" | 
  "elems (x#xs) = insert x (elems xs)"

value "elems [(1::nat), 2, 2, 3, 4]"

(*
if x is a member of 'elems xs' then  xs is created 
by appending some ys with Cons x zs and x isn't in 'elems y'.

basically if x is in a set than you can split a set into the part that has x and
the part that doesn't have x
  
*)
lemma set_exclusive_concat: "x \<in> elems xs \<and> x \<notin> elems ys \<Longrightarrow> x \<in> (elems (xs @ ys))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    by (metis append_Cons append_Nil elems.simps(1,2) empty_iff insert_iff)

qed







end