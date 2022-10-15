open Lambda

[@@@warning "-39"] 
[@@@warning "-27"]
[@@@warning "-32"]

(* Arithmetic *)

(* In this part, we are going to do natural number arithmetic in lambda calculus.
   The missions of this part is 
   - Represent natural numbers with Church numerals.
   - Define addition and multiplication of Church numerals.
   - Define a function [sum(n) = 0 + 1 + 2 + ... + n] using recursion.
   - Test that sum(n) * 2 = n * (n + 1).
*)

(* Church numerals are Church's way of representing natural numbers in lambda calculus.
   0 --> \ f . \ x . x
   1 --> \ f . \ x . f x
   2 --> \ f . \ x . f (f x)
   3 --> \ f . \ x . f (f (f x))
   ...
   That is, n is represented by a binary funcion, accepting a term [f] and a term [x],
   producing the result of applying [f] to [x] n times.
*)

(* Let's define some infix operators to make life easier. *)
(* Operator starting with `$` are left associative. For more information on operators, see 
   this blog: https://blog.shaynefletcher.org/2016/09/custom-operators-in-ocaml.html
   this page in manual: https://v2.ocaml.org/manual/expr.html
    *)
let ($$) x y = C.Ap (x , y)
let ($) x y = Ap (x , y)
let clam s t = C.Lam (s , t)
let lam t = Lam t

exception InvalidArgument of string

(* 
请先阅读 supplement 4 的 1.4 节 (布尔值 ~ 自然数),
了解这部份我们要干什么.
*)

(* 
一个约定: 凡是以 ' 结尾的值都是 C.term 相关的, 即
用字符串来指代绑定变量的; 不以 ' 结尾的是与 term 相关的,
即 locally nameless 表示.

church' 函数接收一个非负整数 n, 返回一个 C.term,
代表 n 的 church numeral 形式. 例如

church' 0 = λ f . λ x . x
church' 1 = λ f . λ x . f x
church' 2 = λ f . λ x . f (f x)
church' 3 = λ f . λ x . f (f (f x))
church' 4 = λ f . λ x . f (f (f (f x)))
*)

(* 下面的 C.Var "..." 只是用来占位的，你需要把它删掉，然后实现 church' 这个函数。
   下同。 *)
let church' (n : int) : C.term = 
   let rec aux n : C.term = 
      if (n == 0) 
         then C.Var "x" 
         else C.Ap ( C.Var "f" , (aux (n-1)) )
      in
      C.Lam ( "f" , C.Lam ( "x" , (aux n) ) )

(* locally nameless 的版本就是用原来的转过去. *)
let church n = church' n |> to_locally_nameless

let (cZero' , cOne' , cTwo' , cThree') = (church' 0 , church' 1 , church' 2 , church' 3)
let (cFour' , cFive' , cSeven' , cTwelf') = (church' 4 , church' 5 , church' 7 , church' 12)
let (cZero , cOne , cTwo , cThree) = (church 0 , church 1 , church 2 , church 3)
let (cFour , cFive , cSeven , cTwelf) = (church 4 , church 5 , church 7 , church 12)

(* 我们定义自然数上的 successor. Successor 就是
后继, 0 的 successor 是 1, 5 的 successor 是 6, 这样.
你也可以理解为 +1.

succ 是一个函数, 当得到一个 church numeral of n 时, 
求值后给出 church numeral of (n + 1).

succ = λ n . λ f . λ x . f (n f x)

如果你不能直观理解为什么 succ 是这样的话, 可以再
回顾一下 church numeral 的含义. 一个非负整数 n 的
church numeral 表示是一个函数 church-n 当给我一个 f 和一个 
x 时, 返回 f 在 x 上作用 n 次的表达式. 
比如 church-3 f x = f (f (f x)).

succ 拿到一个 n 的表示, 要返回 n + 1 的表示.
n + 1 的表示是把 f 在 x 上作用 n + 1 次, 
那不就是先把 f 在 x 上作用 n 次, 再作用一次吗?
而 (n f x) 就是 f 在 x 上作用 n 次.
所以 f (n f x) 就是 f 在 x 上作用 n + 1 次了.

下面我们用刚才定义的函数和运算符来写这个 C.term.
因为一直写 Lam ("n" , Lam ("f" , ...)) 太麻烦了.
下面你需要自己写若干个 lambda term, 你也可以用这种简便写法.
*)
let succ' = clam "n" @@ clam "f" @@ clam "x" @@ (Var "f" $$ (Var "n" $$ Var "f" $$ Var "x"))

(* 有时候觉得在代码里写中文注释, 输入法切换太麻烦了.
   下面就用英文写啦. *)
(* Next we define plus. *)
(* You can first write it in text form. 
   This is not compulsory.
   How to type "λ"? 
   - You can just copy a "λ" and paste it everywhere.
   - You can use VS Code extension "Insert Unicode". *)
(* plus n m = ? , or
   plus = λ n . λ m . ? *)
(* 在这里像上面的 succ' 一样写 plus 的 lambda term。
   注意，最后我们测试的是这个 lambda term 的功能（两数相加），而不是它本身的形式。
   有很多实现方法，任选一种即可。
   下同。 *)

   (* + m n f x = m f (n f x) *)
let plus' = clam "n" @@ clam "m" @@ clam "f" @@ clam "x" @@ (Var "m" $$ Var "f" $$ (Var "n" $$ Var "f" $$ Var "x"))

(* church' 2 = λ f . λ x . f (f (x))
   church' 3 = λ f . λ x . f (f (f (x)))
   2 3 f x = ( λ x . 3 (3 (x)) ) f x *)

(* try it *)
(* equiv (plus cThree cFour) cSeven *)
(* let plus n m = C.Ap( C.Ap(plus' , (from_locally_nameless n)) , (from_locally_nameless m)) |> to_locally_nameless
let plus_test = equiv (plus cThree cFour) cSeven *)

(* Define times (multiplication) *)
(* times n m = ? , or
   times = λ n . λ m . ? *)

(* church' 2 = λ f . λ x . f (f (x))
   church' 3 = λ f . λ x . f (f (f (x)))
   2 (3f) x = ( λ x . 3f (3f (x)) ) x *)
   (* * m n f x = m (n f) x *)
let times' = clam "n" @@ clam "m" @@ clam "f" @@ clam "x" @@ (Var "m" $$ (Var "n" $$ Var "f") $$ Var "x")

(* try it *)
(* equiv (times cThree cFour) cTwelf *)


(* Define sum(n) = 0 + 1 + 2 + ... + n *)

(* First we need a function is_zero, which test if a numeral is zero.
   But before that, we need boolean values!
*)

(* Define church booleans. *)

(* true = λ x . λ y . x *)
let cTrue' = clam "x" @@ clam "y" @@ Var "x" 

(* false = λ x . λ y . y *)
let cFalse' = clam "x" @@ clam "y" @@ Var "y" 

(* Define the "and" operation. 
   and false false === false
   and false true  === false
   and true false  === false
   and true true   === true  *)
(* and x y = ?
   and = λ x . λ y . ? *)
let bool_and' = clam "g" @@ clam "h" @@ (Var "g" $$ Var "h" $$ cFalse')

(* Define is_zero. 
   is_zero 0 === true
   is_zero 1 === false
   is_zero 2 === false 
   ...
   This is a little hard. You need to think. *)
(* is_zero n = ?
   is_zero = λ n . ?` *)

(* We want iszero applied to (the representation of) zero to evaluate to true, 
   and applied to anything other than zero to evaluate to false. 
   Note that ZERO is a function of two arguments; ISZERO needs to "get rid" of that function by applying it to the appropriate two values so that the result is TRUE; 
   i.e., we want ISZERO to be of the form:
      λf.f _ _
   What should the missing values be? 
   Well, ZERO is the function that returns its second argument, 
   and we want ISZERO applied to ZERO to evaluate to TRUE, so the second argument better be TRUE. 

   cZero' 是一个接收两个参数，并返回第二个参数的函数，
   所以对于 λf.f _ _ 形式的表达式，第二个空最好是 cTrue'

   The numbers other than ZERO are functions that apply their first argument to the second argument some number of times, 
   and for all of those numbers we want the final result to be FALSE. 
   So the first argument needs to be a lambda term g 
      such that 
         g applied to TRUE is FALSE; 
         g applied to (g applied to TRUE) is FALSE, 
         etc. 
   The answer is actually very simple: 
      make g be the function that ignores its argument and returns FALSE:
         g == λx.FALSE

   而对于church演算中的 f ，当 n > 0 时， 表达式里至少有一个 f x，为 n f x
   如果能够让 f 无论接收什么参数均返回 cFalse'，那么无论 f x , f ( f x ) 还是其他的均为flase了
   也就是说，第一个空中的 f = λx.cFalse'

   And now we know that ISZERO should be defined like this:
      λf.f(λx.FALSE)TRUE
*)
let is_zero' = clam "n" @@ (Var "n" $$ ( clam "x" @@ cFalse' ) $$ cTrue' )

(* Define predecessor.
   pred 0 === anything (not important)
   pred 1 === 0
   pred 2 === 1
   pred 3 === 2
   ...

   This definition is not trivial. You need to think. *)

(* pred = λ n . ? *)
(* PRED == λk.( k (λp.λu.u (SUCC(p TRUE)) (p TRUE) ) (λu.u ZERO ZERO) ) FALSE *)
let pred' = clam "n" @@ clam "f" @@ clam "x" @@ (Var "n" $$ (clam "g" @@ clam "h" @@ (Var "h" $$ (Var "g" $$ Var "f"))) $$ (clam "u" @@ Var "x") $$ (clam "u" @@ Var "u"))
(* clam "n" @@ (( Var "n" $$ (clam "p" @@ clam "u" @@ (Var "u" $$ (succ' $$ (Var "p" $$ cTrue'))) $$ (clam "u" @@ (Var "u" $$ cZero' $$ cZero'))) ) $$ cFalse') *)

(* Define the Y combinator.
   If you don't understand the idea behind the Y combinator, 
   make sure to read supplement 5!  *)
(* y = λ p . (λ f . p (f f)) (λ f . p (f f)) *)
let y' = clam "p" @@ ((clam "f" @@ (Var "p" $$ (Var "f" $$ Var "f"))) $$ (clam "f" @@ (Var "p" $$ (Var "f" $$ Var "f"))))

(* sum_u = ? *)
let sum_u' = clam "f" @@ clam "n" @@ (is_zero' $$ Var "n" $$ cZero' $$ 
   (plus' $$ Var "n" $$ (Var "f" $$ (pred' $$ Var "n"))) )

let sum' = y' $$ sum_u'

(* sum2 = λ n . 2 * (sum n) *)
let sum2' = clam "n" @@ (times' $$ cTwo' $$ (sum' $$ Var "n"))

(* calc = λ n . n * (n + 1) *)
let calc' = clam "n" @@ (times' $$ Var "n" $$ (succ' $$ Var "n"))

let sum = sum' |> to_locally_nameless
let sum2 = sum2' |> to_locally_nameless
let calc = calc' |> to_locally_nameless

(* try it!
    sum  $ cFive |> nf
    sum2 $ cFive |> nf
    calc $ cFive |> nf
*)