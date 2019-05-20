require "substitution.k"

module HOLIB-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  syntax Prog  ::= "#" "set-bounds" Int Int "#" Lib | Lib
  syntax Lib   ::= Block | "import" KVar TOut Lib
  syntax Block ::= "public"  KVar TVar TOut "=" "{" Term "}" ";"
                 | "private" KVar TVar TOut "=" "{" Term "}" ";"
		 | "fun" Ref ":=" KVar ";"
                 | "int" Ref ":=" Int    ";"
		 | Block Block                           [right]
		 | Term
  syntax Term  ::= "assert" Term                         [strict(1)]
                 | EVal
                 | Val
		 | Lambda
 		 | "!" Ref
		 | "fst" Term                            [strict(1)]
		 | "snd" Term                            [strict(1)]
		 //start: arithmetic operations
                 | "not" Term                            [seqstrict(1),  right]
                 > Term "*" Term                         [seqstrict(1,2), left]
                 > Term "+" Term                         [seqstrict(1,2), left]
		 | Term "-" Term                         [seqstrict(1,2), left]
                 > Term "<" Term                         [seqstrict(1,2), left]
		 | Term "==" Term                        [seqstrict(1,2), left]
		 > Term "&&" Term                        [seqstrict(1,2), left]
		 //end: arithmetic operations
		 > Ref ":=" Term                         [strict(2),  right]
		 > Term "," Term                         [strict(1,2), left]
		 > Term Term                             [strict(2,1)]
		 > "if" Term "then" Term "else" Term     [strict(1)]
		 | "let" KVar "=" Term "in" Term         [binder, strict(2)]
		 | Term ";" Term                         [strict(1),  right]
		 | "letrec" KVar TVar TOut "=" Term "in" Term [binder]
                 | "(" Term ")"                          [bracket]

  syntax Val    ::= KVar | Int | KVar | "()" | Val "," Val | "(" Val ")" [bracket]
  syntax EVal   ::= "fail" | "nil"
  syntax Ref    ::= KVar

  syntax Lambda ::= "fun" TVar TOut "->" Term  [binder]

  syntax Type ::= "int" | "unit"
                | Type "*"  Type [left]
		| Type "->" Type [right]
		| "(" Type ")"   [bracket]
  syntax TVar ::= "(" KVar ":" Type ")"
  syntax TOut ::= ":" "(" Type ")"
  syntax TKVar ::= KVar ":" Type
endmodule

module HOLIB
  imports HOLIB-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  imports SET
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
  syntax Prog ::= "!OPPONENT!"
  syntax Move ::= "call" KVar | "ret" KVar

  configuration <T>
                  <k> $PGM:Prog </k>
		  <eval> .K </eval>
		  <repo>  .Map </repo>
		  <state> .Map </state>
		  <abs> .Map </abs>
		  <pub> .Map </pub>
		  <sig> (assert true):SMTLib </sig>
		  <pc>  (assert true):SMTLib </pc>
		  <kbound> 4 </kbound>
		  <lbound> 4 </lbound>
		  <kzero>  4 </kzero>
		  <lzero>  4 </lzero>
		  <trace> .K </trace>
	        </T>

  //---------------
  // PROG semantics
  rule <k> # set-bounds I1 I2 # L => L </k>
       <kbound> _ => I1 </kbound>
       <lbound> _ => I2 </lbound>
       <kzero>  _ => I1 </kzero>
       <lzero>  _ => I2 </lzero>
       [structural]

  //--------------------------
  // LIB operational semantics
  rule <k> import M:KVar : ( TYPE ) L => L ... </k>
       <abs> ... .Map => (M |-> TYPE) ... </abs>
       <kbound> K </kbound>
       <lbound> I </lbound>
       requires (K =/=Int 0) andBool (I =/=Int 0)
       [structural]
       //todo ABSTRACT names

  //----------------------------
  // BLOCK operational semantics
  rule <k> fun R:Ref := M:KVar ; B => B ... </k>
       <state> ... .Map => (R |-> M) ... </state>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> int R:Ref := I:Int ; B => B ... </k>
       <state> ... .Map => (R |-> I) ... </state>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> public M:KVar (X : XTYPE) :(OTYPE) = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun (X : XTYPE) :(OTYPE) -> T)) ... </repo>
       <pub> ... .Map => (M |-> (XTYPE->OTYPE)) ...</pub>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
       //todo PUBLIC names
  rule <k> private M:KVar X:TVar OTYPE = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun X OTYPE -> T)) ... </repo>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
       //todo ABSTRACT names
  //terminal BLOCK
  rule <k> int R:Ref := I:Int ; => !OPPONENT! </k>
       <state> ... .Map => (R |-> I) ... </state>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> public M:KVar (X : XTYPE) :(OTYPE) = { T:Term } ; => !OPPONENT! </k>
       <repo> ... .Map => (M |-> (fun (X : XTYPE) :(OTYPE) -> T)) ... </repo>
       <pub> ... .Map => (M |-> (XTYPE->OTYPE)) ...</pub>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
       //todo PUBLIC names
  rule <k> private M:KVar X:TVar OTYPE = { T:Term } ; => !OPPONENT! </k>
       <repo> ... .Map => (M |-> (fun X OTYPE -> T)) ... </repo>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
       //todo ABSTRACT names  

  //---------------------------
  // TERM operational semantics
  rule E:EVal ~> K:KItem => E
  rule <k>assert I:Int => () ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I =/=Int 0)
       [structural]
  rule <k>assert 0 => fail ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> ! R:Ref => T ... </k>
       <state> ... R |-> T ... </state>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> R:Ref := X:Val => () ... </k>
       <state> S => S[R <- X] </state> //Suspect we don't update sigma since references never appear in PC.
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>fst (T1,T2) => T1 ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>snd (T1,T2) => T2 ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  
  //begin: arithmetic operations
  rule <k>not 0 => 1 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>not I => 0 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I =/=Int 0)
       [structural]
  rule <k>I1:Int * I2:Int => I1 *Int I2 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>I1:Int - I2:Int => I1 -Int I2 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>I1:Int + I2:Int => I1 +Int I2 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>I1:Int < I2:Int => 1  ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I1 <Int I2)
       [structural]
  rule <k>I1:Int < I2:Int => 0  ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I1 >=Int I2)
       [structural]
  rule <k>I1:Int == I2:Int => 1 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I1 ==Int I2)
       [structural]
  rule <k>I1:Int == I2:Int => 0 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I1 =/=Int I2)
       [structural]
  rule <k>I1:Int && I2:Int => 1 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I1 =/=Int 0) andBool (I2 =/=Int 0)
       [structural]
  rule <k>I1:Int && I2:Int => 0 ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool ((I1 ==Int 0) orBool (I2 ==Int 0))
       [structural]
  //end: arithmetic operations
  
  rule <k> F:Lambda => !N:KVar ... </k>
       <repo> ... .Map => (!N |-> F) ... </repo>      
  rule if 0 then T1:Term else T0:Term => T0
  rule <k>if I:Int then T1:Term else T0:Term => T1 ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0) andBool (I =/=Int 0)
       [structural]
  rule <k>let X:KVar = V:Val in T2:Term => T2[V/X] ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k>V:Val ; T2:Term => T2 ... </k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> letrec F:KVar X:TVar OTYPE = T1:Term in T2:Term => T2[!N:KVar/F] ... </k>
       <repo> ... .Map => (!N |-> (fun X OTYPE -> (T1[!N/F]))) ... </repo>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]

  //method application and evaluation boxes
  syntax Term ::= "{|" Term "|}" [strict(1)]
  rule <k> M:KVar V:Val => {| T[V/X] |} ... </k>
       <repo> ... M |-> (fun (X : ATYPE) OTYPE -> T) ... </repo>
       <kbound> K => K -Int 1 </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> {| V:Val |} => V ... </k>
       <kbound> K => K +Int 1 </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]

  //symbolic non-deterministic transitions
  rule <k>assert X:KVar => fail ... </k>
       <pc>PC => PC (assert (= X 0))</pc>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)               [transition]
  rule <k>assert X:KVar => () ... </k>
       <pc>PC => PC (assert (not (= X 0)))</pc>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)               [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T0 ...</k>
       <pc>PC => PC (assert (= X 0))</pc>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)               [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T1 ...</k>
       <pc>PC => PC (assert (not (= X 0)))</pc>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)               [transition]

  //symbolic deterministic transitions
  rule <k> not X1:KVar => !X:KVar ... </k> //not
       <state> Sigma => Sigma[!X <- not X1] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 0) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar + V2:Val => !X:KVar ... </k> //plus
       <state> Sigma => Sigma[!X <- X1 + V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ X1 V2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val + X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 + X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ V1 X2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar - V2:Val => !X:KVar ... </k> //minus
       <state> Sigma => Sigma[!X <- X1 - V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- X1 V2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val - X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 - X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- V1 X2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar * V2:Val => !X:KVar ... </k> //times
       <state> Sigma => Sigma[!X <- X1 * V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* X1 V2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val * X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 * X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* V1 X2))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar == V2:Val => !X:KVar ... </k> //equals
       <state> Sigma => Sigma[!X <- X1 == V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 V2) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val == X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 == X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= V1 X2) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar < V2:Val => !X:KVar ... </k> //lessthan
       <state> Sigma => Sigma[!X <- X1 < V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< X1 V2) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val < X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 < X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< V1 X2) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> X1:KVar && V2:Val => !X:KVar ... </k> //and
       <state> Sigma => Sigma[!X <- X1 && V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= X1 1) (= V2 1)) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]
  rule <k> V1:Val && X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 && X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= V1 1) (= X2 1)) 1 0))) </sig>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [structural]

  //////////////////////////////////////////////////////////////////////////////////
  // GAME SEMANTICS
  //---------------
  rule <k> M:Prog => nil ...</k>
       <kbound> K </kbound>
       <lbound> L </lbound>
       requires ((K ==Int 0) orBool (L ==Int 0)) andBool notBool isEVal(M)

  ////////////////////////////////////////////////////////
  // proponent question://////////////////////////////////
  // arg X is a method name
  rule <k> M:KVar X:KVar ~> E => !OPPONENT! </k>
       <eval> ES => M~>E~>ES </eval>
       <repo> ... X |-> (fun (A:ATYPE) :(OTYPE) -> T) ... </repo>
       <abs> ... (M |-> _) ... </abs>
       <pub> P => P[X <- ATYPE] </pub>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call M </trace>
       requires (K =/=Int 0)
       	        andBool (I =/=Int 0)
                andBool (ES =/=K .K)
       [transition]
  // arg X is a ground-type variable
  rule <k> M:KVar X:KVar ~> E => !OPPONENT! </k>
       <eval> ES => M~>E~>ES </eval>
       <repo> R </repo>
       <abs> ... (M |-> _) ... </abs>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call M </trace>
       requires notBool (X in_keys(R))
                andBool (I =/=Int 0)
                andBool (K =/=Int 0)
                andBool (ES =/=K .K)
       [transition]
  // arg V is a concrete value (TODO: traverse pairs and add methods to PUB)
  rule <k> M:KVar V:Val ~> E => !OPPONENT! </k>
       <eval> ES => M~>E~>ES </eval>
       <abs> ... (M |-> _ ) ... </abs>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call M </trace>
       requires notBool isKVar(V)
                andBool (I =/=Int 0)
                andBool (K =/=Int 0)
                andBool (ES =/=K .K)
       [transition]
  // proponent answer://////////////////////////////////
  // return value M is a method name
  rule <k> M:KVar => !OPPONENT! </k>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <repo> ... M |-> (fun (A:ATYPE) :(OTYPE) -> T ) ... </repo>
       <pub> P => P[M <- (ATYPE->OTYPE)] </pub>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M </trace>
       requires (I =/=Int 0) andBool (K =/=Int 0)
       [transition] //TODO? refresh names
  // return value X is a variable of ground type
  rule <k> X:KVar => !OPPONENT! </k>
       <repo> R </repo>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M </trace>
       requires (I =/=Int 0)
                andBool (K =/=Int 0)
                andBool notBool (X in_keys(R))
       [transition]
  // return value V is a value (TODO: traverse pairs to add names into PUB)
  rule <k> V:Val => !OPPONENT! </k>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <kbound> K </kbound>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M </trace>
       requires (I =/=Int 0)
       		andBool (K =/=Int 0)
                andBool notBool isKVar(V)
       [transition]

  ////////////////////////////////////////
  // rules to create fresh opponent values.
  syntax Term ::= "opp_val" Type
  rule opp_val (T1 * T2) => (opp_val T1 , opp_val T2)
  rule <k>opp_val (T1 -> T2) => !M:KVar ...</k>
       <abs> ... .Map => (!M |-> (T1 -> T2)) ... </abs>
  rule <k> opp_val int => !X:KVar ...</k>
       <sig> SIG => SIG (declare-const !X Int) </sig>
  rule <k> opp_val unit => () ...</k>
       <sig> SIG => SIG (declare-const !X Int) </sig>
  // opponent question://////////////////////////////////
  rule <k> !OPPONENT! => M (opp_val XTYPE) </k>
       <eval> ES => (L -Int 1)~>(M:KVar)~>ES </eval>
       <pub> ... M |-> (XTYPE->OTYPE) ... </pub>
       <kbound> K </kbound>
       <lbound> L:Int </lbound>
       <trace> TAU => TAU ~> call M </trace>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [transition]
  // opponent answer://////////////////////////////////
  rule <k> !OPPONENT! => (opp_val unit) ~> E </k>
       <eval> M:KVar ~> E ~> ES => ES </eval>
       <pub> ... M |-> (XTYPE->OTYPE) ... </pub>
       <kbound> K </kbound>
       <lbound> L </lbound>
       <trace> TAU => TAU ~> ret M </trace>
       requires (K =/=Int 0) andBool (L =/=Int 0)
       [transition]
       //TODO add declare-const for other types
  //TODO: check if you need to do k=/=0 for every rule.
  //TODO: check if adding all variables into ABS is fine.

endmodule
