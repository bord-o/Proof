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

fun first_literal :: "literal set \<Rightarrow> literal" where
  "first_literal s = (THE x. x \<in> s)"  (* since unit clauses have exactly one element *)

type_synonym clause = "literal set"

type_synonym \<Phi> = "clause set"

datatype result = Sat | Unsat

(* --- Helpers --- *)
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
  "unit_literals f = (\<lambda>c. (SOME lit. lit \<in> c) ) ` {c.  c \<in> f \<and> is_unit_clause c}"

definition unit_prop_step :: "\<Phi> \<Rightarrow> literal \<Rightarrow> \<Phi>" where
  "unit_prop_step f uc = (
    if card f = 0 then f else
      let pos_filt = {clause \<in> f. uc \<notin> clause} in 
      let neg_lit = opposite_lit uc in
      let neg_filt = {clause \<in> pos_filt. neg_lit \<in> clause} in 
      (pos_filt - neg_filt) \<union> {(\<lambda>c. c - {neg_lit}) clause | clause. clause \<in> neg_filt })"

definition unit_prop :: "\<Phi> \<Rightarrow> \<Phi>" where
  "unit_prop f = unit_prop_step f (SOME x. x \<in> (unit_literals f))"

definition  has_unit_prop :: "\<Phi> \<Rightarrow> bool" where
  "has_unit_prop f = (card (unit_literals f) \<noteq> 0 )"

lemma "is_unit_clause {Pos 0}" by (simp add: is_unit_clause_def)

lemma "unit_literals {{Pos 0, Pos 1}, {Pos 2}, {Pos 1}} = {Pos 2, Pos 1}" sorry


lemma "card (unit_literals f) \<le> card f" sorry

(* --- Pure Literal Elimination --- *)
definition has_literal_elim :: "\<Phi> \<Rightarrow> bool" where
  "has_literal_elim _ = True"

fun pure_literals :: "\<Phi> \<Rightarrow> literal set" where
  "pure_literals f = undefined"

fun literal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "literal_elim f = {}"

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
  "resolve f = {}"


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