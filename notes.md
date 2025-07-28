# Notes

## Prooving double reverse 

fun snoc :: "'a list ⇒ 'a ⇒ 'a list" where
  "snoc [] a = [a]" |
  "snoc l a = l @ [a]"

fun mrev :: "'a list ⇒ 'a list" where
  "mrev [] = []" |
  "mrev (x#xs) = snoc (mrev xs) x"

### Example by hand

-  mrev (mrev [1, 2]))
- Matches "mrev (x#xs) = snoc (mrev xs) x"
- Simp snoc (mrev [2]) 1
- Matches "mrev (x#xs) = snoc (mrev xs) x"
- Simp snoc (snoc (mrev []) 2) 1
- Matches "mrev [] = []" 
- Simp snoc (snoc [] 2) 1
- Matches snoc [] a = [a]
- Simp snoc [2] 1
- Matches "snoc l a = l @ [a]"
- Simp [2] @ [1]
- Simp [2, 1]
- Done
