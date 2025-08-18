theory Dp 
  imports Main HOL.Set
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
  "has_empty_clause f = (\<exists>c \<in> f. card c = 0)"

(* --- Unit Propagation --- *)
definition is_unit_clause :: "clause \<Rightarrow> bool" where
  "is_unit_clause c = (card c = 1)"

fun  unit_literals :: "\<Phi> \<Rightarrow> literal set" where
  "unit_literals f = the_elem ` {c.  c \<in> f \<and> is_unit_clause c}"

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

lemma unit_lits_gone:
  fixes f l
  assumes "finite f"
  assumes "{l} \<in> f"
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



lemma unit_prop_no_grow_plus: 
  fixes f l
  assumes "finite f"
  assumes "{l} \<in> f"
  shows "card (unit_prop_step f l) < card f" 
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
    also have 1: "card {clause \<in> f. l \<notin> clause} < card f"
      by (metis (no_types, lifting) assms(1,2) insertI1 mem_Collect_eq psubsetI psubset_card_mono subset2)
    also have 2: "?thesis" using assms 1
      by (metis (lifting)
          \<open>card (unit_prop_step f l) = card ({clause \<in> f. l \<notin> clause} - {clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause} \<union> {clause - {opposite_lit l} |clause. clause \<in> f \<and> l \<notin> clause \<and> opposite_lit l \<in> clause})\<close>
          \<open>card ({clause \<in> f. l \<notin> clause} - {clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause} \<union> {clause - {opposite_lit l} |clause. clause \<in> f \<and> l \<notin> clause \<and> opposite_lit l \<in> clause}) = card ({clause \<in> f. l \<notin> clause} - {clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause} \<union> (\<lambda>clause. clause - {opposite_lit l}) ` {clause \<in> f. l \<notin> clause \<and> opposite_lit l \<in> clause})\<close>
          dual_order.refl le_eq_less_or_eq linorder_not_less rev_finite_subset subset1 subset2 subset_union_card)
     show ?thesis using 2 .
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



lemma literal_not_in_formula:
  fixes f l
  assumes "finite f"
  assumes "\<forall>c \<in> f. l \<notin> c \<and> opposite_lit l \<notin> c"  (* l doesn't appear at all *)
  shows "unit_prop_step f l = f"
proof -
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


definition unit_prop :: "\<Phi> \<Rightarrow> \<Phi>" where
  "unit_prop f = (let lits = unit_literals f in if card lits = 0 then f else unit_prop_step f ( Max lits))"


definition  has_unit_prop :: "\<Phi> \<Rightarrow> bool" where
  "has_unit_prop f = (card (unit_literals f) \<noteq> 0 )"

lemma "is_unit_clause {Pos 0}" by (simp add: is_unit_clause_def)


lemma unit_prop_step_shrink_apply:
  fixes f l
  assumes "finite f"
  assumes "has_unit_prop f"
  assumes "l \<in> unit_literals f"
  shows "card (unit_prop_step f l) < card f"
proof (cases "card f = 0")
  case True
  then show ?thesis 
    using assms(1,2) has_unit_prop_def by auto
next
  case False
  then show ?thesis
  proof -
    let ?up = "unit_prop_step f l"
    have 1:  "{l} \<notin> ?up" using assms(1) unit_lits_gone[of f l] 
      by (metis One_nat_def assms(3) card_1_singleton_iff the_elem_eq unit_literals_sound)
    have 2: "{l} \<in> f " using assms(3) 
      by (metis One_nat_def assms(1) card_1_singleton_iff the_elem_eq unit_literals_sound)
    have 3: "card (f - {{l}}) < card f" 
      using "2" False by auto
    have 4: "card (?up) \<le> card f"
      using assms(1) unit_prop_no_grow[of f l] 1 by blast
    have 5: "card ?up \<noteq> card f" using unit_prop_no_grow_plus
      using "2" assms(1) nat_less_le by blast
    show ?thesis using 1 2 4 5 unit_lits_gone[of f l] unit_prop_no_grow_plus by auto
  qed    
qed

lemma unit_prop_shrink_apply:
  fixes f
  assumes "finite f"
  assumes "has_unit_prop f"
  shows "card (unit_prop f) < card f"
proof (cases "card f = 0")
  case True
  then show ?thesis 
    using assms(1,2) has_unit_prop_def by auto
next
  case False
  let ?ul = "unit_literals f"
  let ?choice = "Max ?ul"
  show ?thesis
    unfolding unit_prop_def
    using assms unit_prop_step_shrink_apply[of f choice]
    by (simp add: has_unit_prop_def unit_prop_step_shrink_apply)
qed

fun all_literals :: "\<Phi> \<Rightarrow> literal set" where
  "all_literals f = Union f"

lemma unit_prop_no_grow_lits:
  fixes f
  assumes "finite f"
  assumes "has_unit_prop f"
  assumes "\<forall>c \<in> f. finite c"
  assumes "\<not>has_empty_clause f" (* This is essential to refute the case where f has the empty set *)
  assumes "card f \<noteq> 0"
  shows "card (all_literals (unit_prop f)) \<le> card (all_literals f)"
proof -
  show ?thesis
  proof -
    let ?all = "all_literals f"
    let ?after = "all_literals (unit_prop f)"
    have 1: "\<nexists>l. l \<in> ?after \<and> l \<notin> ?all"
      using unit_prop_def  unit_prop_step_def by auto
    show ?thesis
      by (metis "1" all_literals.simps assms(1,3) card_mono finite_Union subsetI)
  qed
qed


(* --- Pure Literal Elimination --- *)

fun pure_literals :: "\<Phi> \<Rightarrow> literal set" where
  "pure_literals f = (let all = all_literals f in { l \<in> all. (opposite_lit l) \<notin> all })"


definition has_literal_elim :: "\<Phi> \<Rightarrow> bool" where
  "has_literal_elim f = (card (pure_literals f) \<noteq> 0)"


fun literal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "literal_elim f = (
    let pure = pure_literals f in
    { c. c \<in> f \<and> (disjnt c pure)}
  )"


lemma
  fixes f
  assumes "finite f"
  shows "pure_literals f \<subseteq> all_literals f" by auto


lemma form_not_empty_lits_exist:
  fixes f
  assumes "finite f"
  assumes "card f \<noteq> 0"
  assumes "\<forall>s \<in> f. finite s"
  assumes "\<not>has_empty_clause f" (* This is essential to refute the case where f has the empty set *)
  shows "card (all_literals f) \<noteq> 0"
proof -
  show ?thesis
  proof -
    have 1: "{} \<notin> f" using has_empty_clause_def assms by auto
    have 2: "finite f \<Longrightarrow> {} \<notin> f \<Longrightarrow> card f \<noteq> 0 \<Longrightarrow> card (all_literals f) \<noteq> 0"
    proof -
      have "f \<noteq> {}" using assms by (simp add: card_gt_0_iff)
      then obtain A where "A \<in> f" by blast
      have "A \<noteq> {}" using `A \<in> f` `{} \<notin> f` by blast
      have "A \<subseteq> \<Union>f" using `A \<in> f` by blast
      have "\<Union>f \<noteq> {}" using `A \<subseteq> \<Union>f` `A \<noteq> {}` by blast
      have "finite (\<Union>f)" using  assms by auto
      have "0 < card (\<Union>f)" using \<open>\<Union> f \<noteq> {}\<close> \<open>finite (\<Union> f)\<close> by auto
      show ?thesis by (simp add: \<open>0 < card (\<Union> f)\<close>)
    qed
    then show ?thesis 
      using "1" assms(1,2) by blast     
  qed
qed



lemma literal_elim_no_grow_lits:
  fixes f
  assumes "finite f"
  assumes "has_literal_elim f"
  assumes "\<forall>c \<in> f. finite c"
  assumes "\<not>has_empty_clause f" (* This is essential to refute the case where f has the empty set *)
  assumes "card f \<noteq> 0"
  shows "card (all_literals (literal_elim f)) \<le> card (all_literals f)"
proof -
  show ?thesis 
  proof -
    let ?pure = "pure_literals f"
    let ?impure_clauses = "{c \<in> f. \<not> disjnt c ?pure}"


    have 1: "card ?pure \<noteq> 0" using assms(2)
      unfolding has_literal_elim_def by simp
    have 2: "card (all_literals f) \<noteq> 0" using assms form_not_empty_lits_exist by simp
    have 4: "\<exists>c \<in> f. \<not> disjnt c ?pure" using has_literal_elim_def assms 
      by (metis (no_types, lifting) Set.set_insert all_literals.elims card_eq_0_iff disjnt_Union1 disjnt_insert2
          mem_Collect_eq obtains_Max pure_literals.simps)
    have 5: "card ?impure_clauses \<noteq> 0" using assms 4 by auto
    have 6: "literal_elim f = f - ?impure_clauses" using assms by auto
    have 7: "card ?impure_clauses \<noteq> 0 \<Longrightarrow> card (f - ?impure_clauses) < card f" using 6 assms 
      by (metis (no_types, lifting) "4" DiffD2 Diff_subset card_seteq linorder_not_le mem_Collect_eq)
    have 10: "disjnt ?pure (all_literals (f - ?impure_clauses))" using disjnt_sym by auto
    have 11: "\<exists>l \<in> ?pure. l \<notin> (all_literals (f - ?impure_clauses))"
      by (metis (lifting) "1" "10" all_not_in_conv card_eq_0_iff disjnt_iff)

    have 14: "\<nexists>l. l\<in> (all_literals (f - ?impure_clauses)) \<and> l \<notin> all_literals f" by auto
    have 15: "card (all_literals (f - ?impure_clauses)) \<le> card (all_literals f)" using 10 11 14 
      by (meson "2" card_eq_0_iff card_mono subsetI)

    show ?thesis
      using assms 15 6  by argo
  qed
qed


lemma literal_elim_shrink_apply_clauses:
  fixes f
  assumes "finite f"
  assumes "has_literal_elim f"
  assumes "card f \<noteq> 0"
  shows "card ( (literal_elim f)) < card ( f)"
proof -
  show ?thesis 
  proof -
    let ?pure = "pure_literals f"
    let ?impure_clauses = "{c \<in> f. \<not> disjnt c ?pure}"
    have 4: "\<exists>c \<in> f. \<not> disjnt c ?pure" using has_literal_elim_def assms 
      by (metis (no_types, lifting) Set.set_insert all_literals.elims card_eq_0_iff disjnt_Union1 disjnt_insert2
          mem_Collect_eq obtains_Max pure_literals.simps)
    have 5: "card ?impure_clauses \<noteq> 0" using assms 4 by auto
    have 6: "literal_elim f = f - ?impure_clauses" using assms by auto
    have 7: "card ?impure_clauses \<noteq> 0 \<Longrightarrow> card (f - ?impure_clauses) < card f" using 6 assms 
      by (metis (no_types, lifting) "4" DiffD2 Diff_subset card_seteq linorder_not_le mem_Collect_eq)
    have 8: "card (literal_elim f) < card f" using assms 5 6 7 by auto 
    show ?thesis using 8 .
  qed
qed

(* --- Non Normal Elimination --- *)
definition clause_has_non_normal :: "clause \<Rightarrow> bool" where
  "clause_has_non_normal c = ( \<exists>lit \<in> c. opposite_lit lit \<in> c)"

definition has_non_normal :: "\<Phi> \<Rightarrow> bool"  where
   "has_non_normal f = ( \<exists>clause \<in> f. clause_has_non_normal clause )"

definition non_normal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "non_normal_elim f = {c \<in> f. \<not> (clause_has_non_normal c)} "

lemma non_norm_shrink_apply:
  fixes f
  assumes "finite f"
  assumes "has_non_normal f"
  shows "card (non_normal_elim f) < card f"
  by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono_iff assms(1,2) has_non_normal_def non_normal_elim_def psubsetI
      psubset_card_mono)

lemma non_norm_elim_no_grow_lits:
  fixes f
  assumes "finite f"
  assumes "has_non_normal f"
  assumes "\<forall>c \<in> f. finite c"
  assumes "\<not>has_empty_clause f" (* This is essential to refute the case where f has the empty set *)
  assumes "card f \<noteq> 0"
  shows "card (all_literals (non_normal_elim f)) \<le> card (all_literals f)"
proof -
  
  show ?thesis
  proof -
    let ?all = "all_literals f"
    let ?after = "all_literals (non_normal_elim f)"
    have 1: "\<nexists>l. l \<in> ?after \<and> l \<notin> ?all"
      using non_normal_elim_def by fastforce
    show ?thesis
      by (meson "1" assms(3,4,5) card.infinite card_mono form_not_empty_lits_exist subsetI)
  qed
qed

(* --- Resolution --- *)
fun resolution_pairs :: "\<Phi> \<Rightarrow> literal  \<Rightarrow> (literal set * literal set) set" where
  "resolution_pairs f choice = (
    let pos_clauses = {c \<in> f. choice \<in> c} in
    let neg_clauses = {c \<in> f. (opposite_lit choice \<in> c)} in
    let res_pairs = {Pair a b | a b. a \<in> pos_clauses \<and> b \<in> neg_clauses} in
    res_pairs
  )"

fun resolve :: "\<Phi> \<Rightarrow> \<Phi>" where
  "resolve f = (
    let all = all_literals f in
    let pure = pure_literals f in
    let choice = Min (all - pure) in
    let op_choice = opposite_lit choice in
    let pairs = resolution_pairs f choice in
    let additions = { (fst p \<union> snd p) - {choice, op_choice} |p. p \<in> pairs } in
    let sans_lit = {  c. c \<in> f \<and> choice \<notin> c \<and> op_choice \<notin> c} in
    additions \<union> sans_lit
)"

lemma resolve_shrink_apply_lits:
  fixes f
  assumes "finite f"
  assumes "\<forall>c \<in> f. finite c"
  assumes "\<not>has_literal_elim f"
  assumes "\<not>has_empty_clause f"
  assumes "card f \<noteq> 0"
  shows "card (all_literals (resolve f)) < card (all_literals f)"
proof -
  show ?thesis
  proof -
    let ?all = "all_literals f "
    let ?pure = "pure_literals f "
    let ?diff = "?all - ?pure"
    let ?choice = "Min (?all - ?pure) "
    let ?op_choice = "opposite_lit ?choice "
    let ?pairs = "resolution_pairs f ?choice "
    let ?additions = "{ (fst p \<union> snd p) - {?choice, ?op_choice} |p. p \<in> ?pairs } "
    let ?sans_lit = "{  c. c \<in> f \<and> ?choice \<notin> c \<and> ?op_choice \<notin> c} "
    let ?res = "?additions \<union> ?sans_lit"

    have 1: "?choice \<notin> all_literals ?res" by auto
    have 2: "?op_choice \<notin> all_literals ?res" by auto
    have 3: "\<nexists>l. l \<in> ?pure \<and> l \<notin> ?all" by auto
    have 4: "finite ?diff" 
      by (simp add: assms(1,2))
    have 5: "card ?pure = 0" using assms unfolding has_literal_elim_def by auto
    have 6: "?choice \<in> (?all - ?pure)" 
      using assms
      unfolding has_empty_clause_def
      unfolding has_literal_elim_def 
      using assms Min_in[of ?diff] 
      by (metis "3" "4" Diff_empty double_diff form_not_empty_lits_exist subsetI)
    have 7: "\<nexists>l. l \<in> (all_literals ?res) \<and> l \<notin> ?all" by auto
    have 8: "\<exists>l. l \<in> ?all \<and> l \<notin> (all_literals ?res)" 
      using 6 1
      by blast
    have 9: "all_literals ?res \<subset> ?all"
      using 7 8
       by blast
    have 10: "card (all_literals ?res) < card ?all"
      by (metis (lifting) "9" all_literals.simps assms(1,2) card_seteq finite_Union linorder_not_le
          order_less_le)
    show ?thesis       
      by (metis "10" resolve.simps)
  qed
qed

(* DP *)
function dp :: "\<Phi> \<Rightarrow> result" where
  "dp f = 
    (if card f = 0 then Sat else 
    if has_empty_clause f then Unsat else 
    if has_non_normal f then dp (non_normal_elim f) else
    if has_unit_prop f then dp (unit_prop f) else
    if has_literal_elim f then dp (literal_elim f) else
    dp (resolve f)
)"
  by pat_completeness auto

termination
proof (relation "measures [ \<lambda>f. card (all_literals f),  \<lambda>f. card f]", 
       goal_cases WF TAUT UP PLE RES)
  case WF  
  then show ?case by auto
next  
  case (TAUT form)
  show ?case
  proof -
    have 1: "finite form \<or> card form = 0"
      by (metis card.infinite)
    have 2: "finite form"
      using "1" TAUT(1) by auto
    have alt1: "\<forall>c \<in> form. finite c \<or> card c = 0" by (metis card.infinite)
    have alt2: "\<forall>c \<in> form. card c \<noteq> 0" using TAUT alt1 unfolding has_empty_clause_def
      by auto
    have alt3: "\<forall> c \<in> form. finite c" using alt1 alt2 by auto
    have 3: "card (non_normal_elim form) < card form"
      using TAUT non_norm_shrink_apply[of form] 1 by simp
    have 4: "card (all_literals (non_normal_elim form)) \<le> card (all_literals form)" 
      using TAUT non_norm_elim_no_grow_lits[of form]  alt3 by fastforce
    then show ?thesis
      using 3 4 by auto
  qed   
next
  case (UP form)
  show ?case
    proof -
    have 1: "finite form \<or> card form = 0"
      by (metis card.infinite)
    have 2: "finite form"
      using "1" UP(1) by auto
    have alt1: "\<forall>c \<in> form. finite c \<or> card c = 0" by (metis card.infinite)
    have alt2: "\<forall>c \<in> form. card c \<noteq> 0" using UP alt1 unfolding has_empty_clause_def
      by auto
    have alt3: "\<forall> c \<in> form. finite c" using alt1 alt2 by auto
    have 3: "card (unit_prop form) < card form"
      using UP 2 unit_prop_shrink_apply[of form] by auto
    have 4: "card (all_literals (unit_prop form)) \<le> card (all_literals form)" 
      using UP alt3 unit_prop_no_grow_lits[of form] by fastforce
    then show ?thesis
      using 3 4 by auto
  qed
next
  case (PLE form) 
  then show ?case 
  proof -
    have 1: "finite form \<or> card form = 0"
      by (metis card.infinite)
    have 2: "finite form"
      using "1" PLE(1) by auto

    have alt1: "\<forall>c \<in> form. finite c \<or> card c = 0" by (metis card.infinite)
    have alt2: "\<forall>c \<in> form. card c \<noteq> 0" using PLE alt1 unfolding has_empty_clause_def
      by auto
    have alt3: "\<forall> c \<in> form. finite c" using alt1 alt2 by auto
    have 3: "card (literal_elim form) < card form" 
      using PLE 2 literal_elim_shrink_apply_clauses[of form] by blast
    have 4: "card (all_literals (literal_elim form)) \<le> card (all_literals form)" 
      using alt3 PLE literal_elim_no_grow_lits[of form] by fastforce
    then show ?thesis
      using 3 4 by auto
  qed
next
  case (RES form)
  then show ?case 
  proof -
    have 1: "finite form \<or> card form = 0"
      by (metis card.infinite)
    have 2: "finite form"
      using "1" RES(1) by auto
    have alt1: "\<forall>c \<in> form. finite c \<or> card c = 0" by (metis card.infinite)
    have alt2: "\<forall>c \<in> form. card c \<noteq> 0" using RES alt1 unfolding has_empty_clause_def
      by auto
    have alt3: "\<forall> c \<in> form. finite c" using alt1 alt2 by auto
    have 1: "card (all_literals (resolve form)) < card (all_literals form)"
      using RES resolve_shrink_apply_lits[of form] alt3 by fastforce
    then show ?thesis using measures_def by simp
  qed
qed

end
