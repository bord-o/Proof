theory Dp imports Main
begin

datatype literal = 
  Pos nat
  | Neg nat
type_synonym clause = "literal set"
type_synonym form = "clause set"
datatype result = Sat | Unsat

fun has_empty_clauses :: "form \<Rightarrow> bool" where 
  "has_empty_clauses f = ({} \<in> f)"

value "has_empty_clauses { {Pos 2}, {Pos 1}} = False"

fun pure_literals :: "form \<Rightarrow> literal set" where
  "pure_literals f = undefined"

fun literal_elim :: "form \<Rightarrow> form" where
  "literal_elim f = {}"

fun unit_prop :: "form \<Rightarrow> form" where
  "unit_prop f = {}"

fun resolve :: "form \<Rightarrow> form" where
  "resolve f = {}"

fun dp :: "form \<Rightarrow> result" where
  "dp f = 
    (if f = {} then Sat else 
    if has_empty_clauses f then Unsat else 
      let f1 = unit_prop f in
      if f1 \<noteq> f then dp f1 else
        let f2 = literal_elim f1 in
          if f2 \<noteq> f1 then dp f2 else
            let f3 = resolve f2 in
            dp f3
)"


end