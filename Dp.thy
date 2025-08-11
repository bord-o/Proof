theory Dp imports Main
begin

(* --- Types --- *)
datatype literal = 
  Pos nat
  | Neg nat

instantiation literal :: linorder
begin
fun less_literal :: "literal \<Rightarrow> literal \<Rightarrow> bool" where
  "less_literal (Pos n) (Pos m) = (n < m)" |
  "less_literal (Neg n) (Neg m) = (n < m)" |
  "less_literal (Pos n) (Neg m) = False" |     (* Pos < Neg *)
  "less_literal (Neg n) (Pos m) = True"

definition less_eq_literal :: "literal \<Rightarrow> literal \<Rightarrow> bool" where
  "less_eq_literal x y = (x < y \<or> x = y)"
instance
proof 
  fix x y z :: literal
  show " (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less_eq_literal_def less_literal.elims(2) by fastforce
next
  fix x :: literal
  show "x \<le> x"
    using less_eq_literal_def by auto
next
  fix x y z ::literal
  show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt (verit, ccfv_SIG) less_eq_literal_def less_literal.elims(1) literal.distinct(1) literal.inject(1,2) order_less_trans)
next
  fix x y :: literal
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" 
    using less_eq_literal_def less_literal.elims(2) by fastforce
next 
  fix x y ::literal
  show " x \<le> y \<or> y \<le> x" 
    using less_eq_literal_def less_literal.elims(3) literal.inject(1,2) by fastforce
    
qed
end

lemma "Neg 1 < Neg 2" by simp

(*

  apply (standard; simp add: less_eq_literal_def)
  using less_literal.elims(2) apply fastforce*)


type_synonym clause = "literal set"

type_synonym \<Phi> = "clause set"

datatype result = Sat | Unsat

type_synonym assignment = "nat \<Rightarrow> bool"

(* --- Helpers --- *)


fun eval_literal :: "assignment \<Rightarrow> literal \<Rightarrow> bool" where
  "eval_literal \<sigma> (Pos n) = \<sigma> n" |
  "eval_literal \<sigma> (Neg n) = (\<not>(\<sigma> n))"

fun eval_clause :: "assignment \<Rightarrow> clause \<Rightarrow> bool" where
  "eval_clause \<sigma> c = (\<exists>l \<in> c. eval_literal \<sigma> l)"

fun eval_formula :: "assignment \<Rightarrow> \<Phi> \<Rightarrow> bool" where
  "eval_formula \<sigma> f = (\<forall>c \<in> f. eval_clause \<sigma> c)"

definition satisfiable :: "\<Phi> \<Rightarrow> bool" where
  "satisfiable f = (\<exists>\<sigma>. eval_formula \<sigma> f)"

fun opposite_lit :: "literal \<Rightarrow> literal" where
  "opposite_lit (Pos n) = Neg n" |
  "opposite_lit (Neg n) = Pos n"

fun index_of_lit :: "literal \<Rightarrow> nat" where
  "index_of_lit (Pos n) = n" |
  "index_of_lit (Neg n) = n"

definition has_empty_clause :: "\<Phi> \<Rightarrow> bool" where 
  "has_empty_clause f = ({} \<in> f)"

value "has_empty_clause { {Pos 2}, {Pos 1}} = False"


(* --- Unit Propagation --- *)
definition is_unit_clause :: "clause \<Rightarrow> bool" where
  "is_unit_clause c = (card c = 1)"

fun  unit_literals :: "\<Phi> \<Rightarrow> literal set" where
  "unit_literals f = the_elem ` {c.  c \<in> f \<and> is_unit_clause c}"

value "unit_literals {{Pos 1, Pos 2}, {Pos 3}}"

lemma fixes f c assumes "c \<in> f \<and> card c = 1" shows "(the_elem c) \<in> unit_literals f"
  by (simp add: assms is_unit_clause_def)

lemma unit_literals_sound: 
  fixes f l 
  assumes "finite f"
  assumes "l \<in> unit_literals f" 
  shows "\<exists>c. c \<in> f \<and> card c = 1 \<and> l = the_elem c"
proof -
  show ?thesis
    using assms(2) is_unit_clause_def by auto
qed
  

definition unit_prop_step :: "\<Phi> \<Rightarrow> literal \<Rightarrow> \<Phi>" where
  "unit_prop_step f uc = (
    if card f = 0 then f else
      let pos_filt = {clause \<in> f. uc \<notin> clause} in 
      let neg_lit = opposite_lit uc in
      let neg_filt = {clause \<in> pos_filt. neg_lit \<in> clause} in 
      (pos_filt - neg_filt) \<union> {(\<lambda>c. c - {neg_lit}) clause | clause. clause \<in> neg_filt })"

(*
To prove:
  x - unit prop step will remove all clauses containing that literal
  x - unit prop step will remove the inverse of that literal from all clauses
  x - unit prop will do nothing if the literal is not in the formula
  x - unit prop will never add clauses, only remove them
  [] - unit prop preserves satisfiability
*)


lemma unit_prop_empty:
  assumes "finite f"
  shows "\<forall>l. unit_prop_step {} l = {}" 
  by (simp add: unit_prop_step_def)

lemma subset_union_card:
  fixes a b c f
  assumes "a \<subseteq> c"
  assumes "b \<subseteq> a"
  assumes "finite c"
  shows "card(a - b \<union> (f ` b)) \<le> card c"
proof -
  have "card (a - b) + card b = card a"
    using assms(2,3,1) 
    by (metis card_Diff_subset card_mono le_add_diff_inverse2 rev_finite_subset)    
  have "card (a - b \<union> (f ` b)) \<le> card (a - b) + card (f ` b)"
    by (rule card_Un_le)
  also have "... \<le> card (a - b) + card b"
    using card_image_le by (meson add_left_mono assms finite_subset order_trans)
  also have "... = card a"
    using `card (a - b) + card b = card a` by simp
  also have "... \<le> card c"
    using assms by (simp add: card_mono)
  finally show ?thesis .
qed

lemma unit_prop_no_grow: 
  fixes f l
  assumes "finite f"
  shows "card (unit_prop_step f l) \<le> card f" 
proof -
  show ?thesis
  proof (cases "card f = 0")
    case True
    then show ?thesis using unit_prop_empty assms
      by fastforce
  next
    case False
    let ?not_containing_l = "{clause \<in> f. l \<notin> clause}"
    let ?containing_opp_l = "{clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause}"
    let ?reduced_clauses = "{clause - {opposite_lit l} |clause. clause \<in> f \<and> l \<notin> clause \<and> opposite_lit l \<in> clause}"
    
    have subset1: "?containing_opp_l \<subseteq> ?not_containing_l" by blast
    have subset2: "?not_containing_l \<subseteq> f" by blast
    
    have image_form: "?reduced_clauses = (\<lambda>clause. clause - {opposite_lit l}) ` ?containing_opp_l"
      by (auto simp: setcompr_eq_image)
    
    have "unit_prop_step f l = (?not_containing_l - ?containing_opp_l) \<union> ?reduced_clauses"
      unfolding unit_prop_step_def
      apply(simp_all add:Let_def)
      using False by blast
    
    have "card (unit_prop_step f l) = card ((?not_containing_l - ?containing_opp_l) \<union> ?reduced_clauses)"
      using `unit_prop_step f l = (?not_containing_l - ?containing_opp_l) \<union> ?reduced_clauses` by simp
    also have "... = card ((?not_containing_l - ?containing_opp_l) \<union> ((\<lambda>clause. clause - {opposite_lit l}) ` ?containing_opp_l))"
      using image_form by simp
    also have "... \<le> card f"
      using subset_union_card[OF subset2 subset1 assms] by simp
    finally show ?thesis .
  qed
qed



lemma neg_lits_filtered:
  fixes f l
  assumes "finite f"
  shows "\<forall>c \<in> (unit_prop_step f l). opposite_lit l \<notin> c" 
proof -
  show ?thesis
  proof (cases "card f = 0")
    case True
    then show ?thesis 
      using unit_prop_empty assms by auto
  next
    case False
    then show ?thesis 
      unfolding unit_prop_step_def
      using assms 
      apply(simp_all add:unit_prop_empty DiffE UnE  singletonI Let_def)
      by auto
  qed
qed

lemma unit_lits_gone:
  fixes f l
  assumes "finite f"
  shows "{l} \<notin> unit_prop_step f l"
proof -
  show ?thesis
  proof (cases "card f = 0")
    case True
    then show ?thesis 
      by (simp add: assms unit_prop_step_def)
  next
    case False
    then show ?thesis 
      unfolding unit_prop_step_def
      apply(simp add:Let_def assms)
      by blast
  qed
qed

lemma literal_not_in_formula:
  fixes f l
  assumes "finite f"
  assumes "\<forall>c \<in> f. l \<notin> c \<and> opposite_lit l \<notin> c"  (* l doesn't appear at all *)
  shows "unit_prop_step f l = f"
proof -
  (* First decide about the if condition *)
  show ?thesis
  proof (cases "card f = 0")
    case True
    then show ?thesis 
      using unit_prop_step_def by auto
  next
    case False
    have 1: "{clause \<in> f. l \<notin> clause} = f"
      using assms(2) by blast
    have 2: "{clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause} = {}"  
      using assms by simp 
    have 3: "{clause \<in> f. opposite_lit l \<in> clause} = {}" 
      using assms 1 2 by blast
    have 4: "f - {clause \<in> f. opposite_lit l \<in> clause} = f" 
      using assms 1 2 3 by blast
    have 5: " {clause - {opposite_lit l} |clause. clause \<in> f \<and> opposite_lit l \<in> clause} = {}" 
      using assms 1 2 3 4 by blast
    then show ?thesis
      unfolding unit_prop_step_def
      by (simp_all add:assms 1 2 3 4 5) 
  qed
qed

value "unit_prop_step {{Pos 2, Neg 1}, {Pos 1}} (Pos 1)"

definition unit_prop :: "\<Phi> \<Rightarrow> \<Phi>" where
  "unit_prop f = (let lits = unit_literals f in if card lits = 0 then f else unit_prop_step f ( Max lits))"

value "unit_prop (unit_prop {{Pos 1, Pos 3, Neg 4}, {Pos 1, Neg 2, Neg 3, Pos 4}})"

definition  has_unit_prop :: "\<Phi> \<Rightarrow> bool" where
  "has_unit_prop f = (card (unit_literals f) \<noteq> 0 )"

lemma "is_unit_clause {Pos 0}" by (simp add: is_unit_clause_def)


(* --- Pure Literal Elimination --- *)
definition has_literal_elim :: "\<Phi> \<Rightarrow> bool" where
  "has_literal_elim _ = True"

fun all_literals :: "\<Phi> \<Rightarrow> literal set" where
  "all_literals f = Union f"

value "all_literals  (unit_prop {{Pos 1, Pos 3, Neg 4}, {Pos 1, Neg 2, Neg 3, Pos 4}})"


(* The set of literals where foreach literal l, \<not>l appears in no clauses in a formula*)
fun pure_literals :: "\<Phi> \<Rightarrow> literal set" where
  "pure_literals f = (let all = all_literals f in { l \<in> all. (opposite_lit l) \<notin> all })"

value "pure_literals  (unit_prop {{Pos 1, Pos 3, Neg 4}, {Pos 1, Neg 2, Neg 3, Pos 4}})"

fun literal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "literal_elim f = (
    let pure = pure_literals f in
    { c. c \<in> f \<and> (c - pure = c)}
  )"

value "literal_elim   {{Pos 1, Pos 3, Neg 4}, {Pos 1, Neg 2, Neg 3, Pos 4}, {Neg 1}}"

lemma
  fixes f
  assumes "finite f"
  shows "pure_literals f \<subseteq> all_literals f" by auto

lemma literal_elim_no_grow:
  fixes f
  assumes "finite f"
  shows "card (literal_elim f) \<le> card f"
proof -
  show ?thesis
  proof (cases "card f = 0")
    case False
    then show ?thesis 
      by (simp add: assms card_mono)
  next
    case True
    then show ?thesis
      by (simp add: assms)
  qed
qed
  

(* --- Non Normal Elimination --- *)
definition clause_has_non_normal :: "clause \<Rightarrow> bool" where
  "clause_has_non_normal c = ( { lit \<in> c. opposite_lit lit \<in> c } \<noteq> {})"
value "clause_has_non_normal {Pos 1, Neg 1}"

definition has_non_normal :: "\<Phi> \<Rightarrow> bool"  where
   "has_non_normal f = ( { clause \<in> f. clause_has_non_normal clause } \<noteq> {})"

(* Eliminate clauses that contain a literal and its negation *)
definition non_normal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "non_normal_elim f = {c \<in> f. \<not> (clause_has_non_normal c)} "

value "non_normal_elim {{Pos 0, Pos 1, Neg 0}, {Pos 4}, {Pos 2, Neg 2}, {Neg 3}}"

(* --- Resolution --- *)
fun resolve :: "\<Phi> \<Rightarrow> \<Phi>" where
  "resolve f = (
    let all = all_literals f in
    let pure = pure_literals f in
    let choice = Max (all - pure) in
    {}
  )"


(* DP *)
fun dp :: "\<Phi> \<Rightarrow> result" where
  "dp f = 
    (if f = {} then Sat else 
    if has_empty_clause f then Unsat else 
    if has_non_normal f then dp (non_normal_elim f) else
    if has_unit_prop f then dp (unit_prop f) else
    if has_literal_elim f then dp (literal_elim f) else
    dp (resolve f)
)"


end