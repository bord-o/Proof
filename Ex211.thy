theory Ex211 imports Main
begin

(*
Exercise 2.11. Define arithmetic expressions in one variable over integers
(type int ) as a data type:
datatype exp= Var | Const int | Add exp exp | Mult exp exp

Define a function 

eval :: exp \<Rightarrow>int \<Rightarrow>int 

such that eval e x evaluates e at
the value x.

A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2,− 1, 3] represents the polynomial 4+2x−x2 +3x3
.
Define a function 

evalp :: int list \<Rightarrow>int \<Rightarrow>int

that evaluates a polynomial at
the given value. Define a function 

coeffs :: exp \<Rightarrow>int list

that transforms an
expression into a polynomial. This may require auxiliary functions. Prove that
coeffs preserves the value of the expression: 

evalp (coeﬀs e) x = eval e x.
Hint: consider the hint in Exercise 2.10.
*)


datatype exp= Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var n = n" |
  "eval (Const n) _ = n" |
  "eval (Add a b) n = (eval a n) + (eval b n)" |
  "eval (Mult a b) n = (eval a n) * (eval b n)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0" |
  "evalp (x#xs) n = x + n * evalp xs n" 


fun add_poly :: "int list \<Rightarrow> int list \<Rightarrow> int list" where 
  "add_poly [] n = n" |
  "add_poly n [] = n" |
  "add_poly (x#xs) (y#ys) = (x+y) # (add_poly xs ys)"

value "add_poly [0, 1, 2] [0, 0, 3, 4, 5] = [0, 1, 5, 4, 5]"

value "map (\<lambda> (x::int). x+1) [1, 2]"

fun mult_poly :: "int list \<Rightarrow> int list \<Rightarrow> int list " where 
  "mult_poly [] n = []" |
  "mult_poly (x#xs) l = add_poly  (map (\<lambda>(i::int). i * x) l) (mult_poly xs (0#l))   "

value "mult_poly  [0, 3, 0, 4] [1, 0, 2] = [0, 3, 0, 10, 0, 8]"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const n) = [n]" |
  "coeffs (Add a b) = add_poly (coeffs a) (coeffs b)" |
  "coeffs (Mult a b) = mult_poly (coeffs a) (coeffs b)"

value "coeffs (Add (Mult Var Var) (Add Var (Const 2)))"

lemma padd_dist : "evalp (add_poly p1 p2) x = evalp p1 x + evalp p2 x"
  apply(induction p1 p2 rule: add_poly.induct)
    apply(auto)
  apply(simp add:algebra_simps)
  done

lemma pmult_map : "evalp (map ((*) xa) l) x = xa * evalp l x"
  apply(induction l)
   apply(auto simp add:algebra_simps)
  done
  

lemma pmult_dist : "evalp (mult_poly p1 p2) x = evalp p1 x * evalp p2 x"
  apply(induction p1 p2 rule: mult_poly.induct)
   apply(auto)
  apply(simp add:algebra_simps)
  apply(simp add:padd_dist pmult_map)
  done
  

theorem eq_eval : "evalp (coeffs e) x = eval e x"
  apply(induction e)
     apply(simp_all add:padd_dist pmult_dist)
  done
  
  


end