require "substitution.k"

module HOREF-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  syntax Prog  ::= "#" "set-bound" Int "#" Lib | Lib
  syntax Lib   ::= Block | "import" Method Lib
  syntax Block ::= "public"  Method KVar "=" "{" Term "}" ";" Block
                 | "private" Method KVar "=" "{" Term "}" ";" Block
		 | "fun" Ref ":=" Method ";" Block
                 | "int" Ref ":=" Int    ";" Block
                 | "main" KVar "=" Term
  syntax Term  ::= "assert" Term                         [strict(1)]
                 | EVal
                 | Val
		 | Lambda
 		 | "!" Ref
		 | "fst"  Term                           [strict(1)]
		 | "snd" Term                            [strict(1)]
		 //start: arithmetic operations
                 | "not" Term                            [seqstrict(1), right]
                 > Term "*" Term                         [seqstrict(1,2), left]
                 // | Term "/" Term                         [seqstrict(1,2), left]
                 > Term "+" Term                         [seqstrict(1,2), left]
		 | Term "-" Term                         [seqstrict(1,2), left]
                 > Term "<" Term                         [seqstrict(1,2), left]
		 | Term "==" Term                        [seqstrict(1,2), left]
		 // | Term "!=" Term                        [seqstrict(1,2), left]
		 > Term "&&" Term                        [seqstrict(1,2), left]
		 // > Term "||" Term                        [seqstrict(1,2), left]
		 //end: arithmetic operations
		 > Ref ":=" Term                         [strict(2), right]
		 > Term "," Term                         [strict(1,2), left]
		 > Term Term                             [strict(2,1)]
		 > "if" Term "then" Term "else" Term     [strict(1)]
		 | "let" KVar "=" Term "in" Term         [binder, strict(2)]
		 | Term ";" Term                         [strict(1), right]
		 | "letrec" KVar KVar "=" Term "in" Term [binder]
                 | "(" Term ")"                          [bracket]

  syntax Val    ::= KVar | Int | Method | "()"
  syntax EVal   ::= "fail" | "nil"
  syntax Method ::= KVar
  syntax Ref    ::= KVar

  syntax Lambda ::= "fun" KVar "->" Term  [binder]
endmodule

module HOREF
  imports HOREF-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  syntax KResult ::= Val
  syntax SMTLib ::= "(" "declare-const" KVar "Int" ")"
                  | "(" "declare-const" KVar "String" ")"
		  | "(" "check-sat" ")"
		  | "(" "get-model" ")"
		  | "(" "display" SMTProp ")"
		  | "(" "simplify" SMTProp ")"
                  | "(" "assert" SMTProp ")"
		  | SMTLib SMTLib	            [left]
  syntax SMTProp ::= Bool | Val
                   | "(" "<" Val Val ")"            [left]
		   | "(" "*" Val Val ")"            [left]
                   | "(" "+" Val Val ")"            [left]
                   | "(" "-" Val Val ")"            [left]
                   | "(" "="   SMTProp SMTProp ")"  [left]
                   | "(" "and" SMTProp SMTProp ")"  [left]
                   | "(" "or"  SMTProp SMTProp ")"  [left]
		   | "(" "not" SMTProp ")"          [right]
                   | "(" "ite"  SMTProp SMTProp SMTProp ")" [left]

  configuration <T>
                  <k> $PGM:Prog </k>
		  <repo> .Map </repo>
		  <state> .Map </state>
		  <sig> (assert true):SMTLib </sig>
		  <pc> (assert true):SMTLib </pc>
		  <bound> 4 </bound>
	        </T>

  //---------------
  // PROG semantics
  rule <k> # set-bound I # L => L </k>
       <bound> _ => I </bound>

  //--------------------------
  // LIB operational semantics
  rule <k> import M:Method L => L ... </k>
       //todo ABSTRACT names

  //----------------------------
  // BLOCK operational semantics
  rule <k> fun R:Ref := M:Method ; B => B ... </k>
       <state> ... .Map => (R |-> M) ... </state>
  rule <k> int R:Ref := I:Int ; B => B ... </k>
       <state> ... .Map => (R |-> I) ... </state>
  rule <k> public M:Method X:KVar = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun X -> T)) ... </repo>
       //todo PUBLIC names
  rule <k> private M:Method X:KVar = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun X -> T)) ... </repo>
  rule <k>main X:KVar = T:Term => T ... </k>
       <sig> SIG => SIG (declare-const X Int) </sig>

  //---------------------------
  // TERM operational semantics
  rule E:EVal ~> K:KItem => E
  rule assert I:Int => () requires I =/=Int 0
  rule assert 0 => fail
  rule <k> ! R:Ref => T ... </k>
       <state> ... R |-> T ... </state>
  rule <k> R:Ref := X => () ... </k>
       <state> S => S[R <- X] </state> //CHECK THIS. Suspect we don't update sigma since references never appear in PC.
  rule fst (T1,T2) => T1
  rule snd (T1,T2) => T2
  
  //begin: arithmetic operations
  rule not 0 => 1
  rule not I => 0                    requires I =/=Int 0
  rule I1:Int * I2:Int => I1 *Int I2
  // rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int < I2:Int => 1          requires I1 <Int I2
  rule I1:Int < I2:Int => 0          requires I1 >=Int I2
  rule I1:Int == I2:Int => 1         requires I1 ==Int I2
  rule I1:Int == I2:Int => 0         requires I1 =/=Int I2
  // rule I1:Int != I2:Int => 1         requires I1 =/=Int I2
  // rule I1:Int != I2:Int => 0         requires I1 ==Int I2
  rule I1:Int && I2:Int => 1         requires (I1 =/=Int 0) andBool (I2 =/=Int 0)
  rule I1:Int && I2:Int => 0         requires (I1 ==Int 0) orBool (I2 ==Int 0)
  // rule I1:Int || I2:Int => 1         requires (I1 =/=Int 0) orBool (I2 =/=Int 0)
  // rule 0 || 0 => 0
  //end: arithmetic operations
  
  rule <k> F:Lambda => !N:KVar ... </k>
       <repo> ... .Map => (!N |-> F) ... </repo>      
  rule if 0 then T1:Term else T0:Term => T0
  rule if I:Int then T1:Term else T0:Term => T1 requires I =/=Int 0
  rule let X:KVar = V:Val in T2:Term => T2[V/X]
  rule V:Val ; T2:Term => T2
  rule <k> letrec F:KVar X:KVar = T1:Term in T2:Term => T2[!N:KVar/F] ... </k>
       <repo> ... .Map => (!N |-> (fun X:KVar -> (T1[!N/F]))) ... </repo>

  //method application and evaluation boxes
  syntax Term ::= "{|" Term "|}" [strict(1)]
  rule <k> M:KVar V:Val => {| T[V/X] |} ... </k>
       <repo> ... M |-> (fun X -> T) ... </repo>
       <bound> I => I -Int 1 </bound> requires I =/=Int 0
  rule <k> M:KVar V:Val => nil ... </k>
       <repo> ... M |-> (fun X -> T) ... </repo>
       <bound> 0 </bound>
  rule <k> {| V:Val |} => V ... </k>
       <bound> I => I +Int 1 </bound>

  //symbolic non-deterministic transitions
  rule <k>assert X:KVar => fail ... </k>
       <pc>PC => PC (assert (= X 0))</pc>                      [transition]
  rule <k>assert X:KVar => () ... </k>
       <pc>PC => PC (assert (not (= X 0)))</pc>                [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T0 ...</k>
       <pc>PC => PC (assert (= X 0))</pc>                      [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T1 ...</k>
       <pc>PC => PC (assert (not (= X 0)))</pc>                [transition]
  //symbolic deterministic transitions
  rule <k> not X1:KVar => !X:KVar ... </k> //not
       <state> Sigma => Sigma[!X <- not X1] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 0) 1 0))) </sig>
  rule <k> X1:KVar + V2:Val => !X:KVar ... </k> //plus
       <state> Sigma => Sigma[!X <- X1 + V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ X1 V2))) </sig>
  rule <k> V1:Val + X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 + X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ V1 X2))) </sig>
  rule <k> X1:KVar - V2:Val => !X:KVar ... </k> //minus
       <state> Sigma => Sigma[!X <- X1 - V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- X1 V2))) </sig>
  rule <k> V1:Val - X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 - X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- V1 X2))) </sig>
  rule <k> X1:KVar * V2:Val => !X:KVar ... </k> //times
       <state> Sigma => Sigma[!X <- X1 * V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* X1 V2))) </sig>
  rule <k> V1:Val * X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 * X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* V1 X2))) </sig>
  rule <k> X1:KVar == V2:Val => !X:KVar ... </k> //equals
       <state> Sigma => Sigma[!X <- X1 == V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 V2) 1 0))) </sig>
  rule <k> V1:Val == X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 == X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= V1 X2) 1 0))) </sig>
  rule <k> X1:KVar < V2:Val => !X:KVar ... </k> //lessthan
       <state> Sigma => Sigma[!X <- X1 < V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< X1 V2) 1 0))) </sig>
  rule <k> V1:Val < X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 < X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< V1 X2) 1 0))) </sig>
  rule <k> X1:KVar && V2:Val => !X:KVar ... </k> //and
       <state> Sigma => Sigma[!X <- X1 && V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= X1 1) (= V2 1)) 1 0))) </sig>
  rule <k> V1:Val && X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 && X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= V1 1) (= X2 1)) 1 0))) </sig>
endmodule
