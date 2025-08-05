theory Dp imports Main
begin

(* Types *)
datatype literal = 
  Pos nat
  | Neg nat

type_synonym clause = "literal set"

type_synonym \<Phi> = "clause set"

datatype result = Sat | Unsat

fun opposite_lit :: "literal \<Rightarrow> literal" where
  "opposite_lit (Pos n) = Neg n" |
  "opposite_lit (Neg n) = Pos n"

fun index_of_lit :: "literal \<Rightarrow> nat" where
  "index_of_lit (Pos n) = n" |
  "index_of_lit (Neg n) = n"

definition has_empty_clause :: "\<Phi> \<Rightarrow> bool" where 
  "has_empty_clause f = ({} \<in> f)"

value "has_empty_clause { {Pos 2}, {Pos 1}} = False"

definition is_unit_clause :: "clause \<Rightarrow> bool" where
  "is_unit_clause c = (card c = 1)"

definition unit_clauses :: "\<Phi> \<Rightarrow> \<Phi>" where
  "unit_clauses f = {c \<in> f. is_unit_clause c}"

value "the_elem {1::nat}"

definition unit_literals :: "\<Phi> \<Rightarrow> literal set" where
  "unit_literals f = {the_elem c |c.  c \<in> f \<and> is_unit_clause c}"

definition unit_prop_step :: "\<Phi> \<Rightarrow> literal \<Rightarrow> \<Phi>" where
  "unit_prop_step f uc = (
    if card f = 0 then f else
      let pos_filt = {clause \<in> f. uc \<notin> clause} in 
      let neg_lit = opposite_lit uc in
      let neg_filt = {clause \<in> pos_filt. neg_lit \<in> clause} in 
      (pos_filt - neg_filt) \<union> {(\<lambda>c. c - {neg_lit}) clause | clause. clause \<in> neg_filt })"

definition unit_prop :: "\<Phi> \<Rightarrow> \<Phi>" where
  "unit_prop f = unit_prop_step f (SOME x. x \<in> (unit_literals f))"


(* True if a clause contains a literal and its negation *)
definition clause_has_non_normal :: "clause \<Rightarrow> bool" where
  "clause_has_non_normal c = ( { lit \<in> c. opposite_lit lit \<in> c } \<noteq> {})"
value "clause_has_non_normal {Pos 1, Neg 1}"

definition has_non_normal :: "\<Phi> \<Rightarrow> bool" where
   "has_non_normal f = ( { clause \<in> f. clause_has_non_normal clause } \<noteq> {})"


(* Eliminate clauses that contain a literal and its negation *)
definition non_normal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "non_normal_elim f = {c \<in> f. \<not> (clause_has_non_normal c)} "

value "non_normal_elim {{Pos 0, Pos 1, Neg 0}, {Pos 4}, {Pos 2, Neg 2}, {Neg 3}}"

fun pure_literals :: "\<Phi> \<Rightarrow> literal set" where
  "pure_literals f = undefined"

fun literal_elim :: "\<Phi> \<Rightarrow> \<Phi>" where
  "literal_elim f = {}"

fun resolve :: "\<Phi> \<Rightarrow> \<Phi>" where
  "resolve f = {}"

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