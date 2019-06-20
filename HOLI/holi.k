require "substitution.k"
require "z3.k"

module HOLI-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  syntax Prog  ::= "#" "set-bounds" Int Int "#" Lib | Lib
  syntax Lib   ::= Block | "import" KVar TOut Lib
  syntax Block ::= "public"  KVar TVar TOut "=" "{" Term "}" ";"
                 | "private" KVar TVar TOut "=" "{" Term "}" ";"
		 | "fun" KVar ":=" KVar ";"
                 | "int" KVar ":=" Int    ";"
		 | Block Block                           [right]
		 | Term
  syntax Term  ::= "assert" Term                         [strict(1)]
                 | EVal
                 | Val
 		 | "!" KVar
		 | "fst" Term                            [strict(1)]
		 | "snd" Term                            [strict(1)]
		 > Term Term                             [strict(2,1)]
		 //start: arithmetic operations
                 > "not" Term                            [seqstrict(1)]
                 > Term "*" Term                         [seqstrict(1,2), left]
                 | Term "/" Term                         [seqstrict(1,2), left]
                 > Term "+" Term                         [seqstrict(1,2), left]
		 | Term "-" Term                         [seqstrict(1,2), left]
                 > Term "<" Term                         [seqstrict(1,2), left]
		 | Term "==" Term                        [seqstrict(1,2), left]
		 > Term "&&" Term                        [seqstrict(1,2), right]
		 > Term "||" Term                        [seqstrict(1,2), right]
		 //end: arithmetic operations
                 > Term "," Term                         [strict(1,2), left]
		 > KVar ":=" Term                        [strict(2),  right]
		 > "if" Term "then" Term "else" Term     [strict(1)]
                 > Term ";" Term                         [strict(1),  right]
		 > "let" KVar "=" Term "in" Term         [binder, strict(2)]
		 | "letrec" KVar TVar TOut "=" Term "in" Term [binder]
		 | "fun" TVar TOut "->" Term             [binder]
                 | "(" Term ")"                          [bracket]

  syntax Val    ::= KVar | Int | "()" | Val "," Val | "(" Val ")" [bracket]
  syntax EVal   ::= "fail" | "nil"

  syntax Type ::= "int" | "unit"
                | Type "*"  Type [left]
		| Type "->" Type [right]
		| "(" Type ")"   [bracket]
  syntax TVar ::= "(" KVar ":" Type ")"
  syntax TOut ::= ":" "(" Type ")"
  syntax TKVar ::= KVar ":" Type
endmodule

module HOLI
  imports HOLI-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  imports SET
  imports COLLECTIONS
  imports Z3
  
  syntax KResult ::= Val
  syntax Prog ::= "!OPPONENT!"
  syntax Move ::= "call" Term | "ret" Term
  syntax K ::= "Context" K

  syntax SMTVal ::= ValToSMT(Val)  [function]
  rule ValToSMT(X:KVar) => X
  rule ValToSMT(I:Int)  => I

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
		  <lzero>  4 </lzero>
		  <trace> .K </trace>
	        </T>

  ////////////////////
  // PROG semantics //
  ////////////////////
  rule <k> # set-bounds I1 I2 # L => L </k>
       <kbound> _ => I1 </kbound>
       <lbound> _ => I2 </lbound>
       <lzero>  _ => I2 </lzero>
       [structural]

  ///////////////////////////////
  // LIB operational semantics //
  ///////////////////////////////
  rule <k> import M:KVar : ( TYPE ) L => L ... </k>
       <abs> ... .Map => (M |-> TYPE) ... </abs>
       [structural]

  /////////////////////////////////
  // BLOCK operational semantics //
  /////////////////////////////////
  rule <k> fun R:KVar := M:KVar ; B => B ... </k>
       <state> ... .Map => (R |-> M) ... </state>
       [structural]
  rule <k> int R:KVar := I:Int ; B => B ... </k>
       <state> ... .Map => (R |-> I) ... </state>
       [structural]
  rule <k> public M:KVar (X : XTYPE) :(OTYPE) = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun (X : XTYPE) :(OTYPE) -> T)) ... </repo>
       <pub> ... .Map => (M |-> (XTYPE->OTYPE)) ...</pub>
       [structural]
  rule <k> private M:KVar X:TVar OTYPE = { T:Term } ; B => B ... </k>
       <repo> ... .Map => (M |-> (fun X OTYPE -> T)) ... </repo>
       [structural]
  rule <k> int R:KVar := I:Int ; => !OPPONENT! </k>
       <state> ... .Map => (R |-> I) ... </state>
       [structural]
  rule <k> public M:KVar (X : XTYPE) :(OTYPE) = { T:Term } ; => !OPPONENT! </k>
       <repo> ... .Map => (M |-> (fun (X : XTYPE) :(OTYPE) -> T)) ... </repo>
       <pub> ... .Map => (M |-> (XTYPE->OTYPE)) ...</pub>
       [structural]
  rule <k> private M:KVar X:TVar OTYPE = { T:Term } ; => !OPPONENT! </k>
       <repo> ... .Map => (M |-> (fun X OTYPE -> T)) ... </repo>
       [structural]

  ////////////////////////////////
  // TERM operational semantics //
  ////////////////////////////////
  rule E:EVal ~> K:KItem => E
  rule <k>assert I:Int => () ... </k>
       requires (I =/=Int 0)
       [structural]
  rule <k>assert 0 => fail ... </k>
       [structural]
  rule <k> ! R:KVar => T ... </k>
       <state> ... R |-> T ... </state>
       [structural]
  rule <k> R:KVar := X:Val => () ... </k>
       <state> S => S[R <- X] </state>
       [structural]
  rule <k>fst (T1,T2) => T1 ... </k>
       [structural]
  rule <k>snd (T1,T2) => T2 ... </k>
       [structural]
  
  //begin: arithmetic operations
  rule <k>not 0 => 1 ...</k>
       [structural]
  rule <k>not I => 0 ...</k>
       requires (I =/=Int 0)
       [structural]
  rule <k>I1:Int * I2:Int => I1 *Int I2 ...</k>
       [structural]
  rule <k>I1:Int - I2:Int => I1 -Int I2 ...</k>
       [structural]
  rule <k>I1:Int + I2:Int => I1 +Int I2 ...</k>
       [structural]
  rule <k>I1:Int < I2:Int => 1  ...</k>
       requires (I1 <Int I2)
       [structural]
  rule <k>I1:Int < I2:Int => 0  ...</k>
       requires (I1 >=Int I2)
       [structural]
  rule <k>I1:Int == I2:Int => 1 ...</k>
       requires (I1 ==Int I2)
       [structural]
  rule <k>I1:Int == I2:Int => 0 ...</k>
       requires (I1 =/=Int I2)
       [structural]
  rule <k>I1:Int && I2:Int => 1 ...</k>
       requires (I1 =/=Int 0) andBool (I2 =/=Int 0)
       [structural]
  rule <k>I1:Int && I2:Int => 0 ...</k>
       requires ((I1 ==Int 0) orBool (I2 ==Int 0))
       [structural]
  rule <k>I1:Int || I2:Int => 1 ...</k>
       requires (I1 =/=Int 0) orBool (I2 =/=Int 0)
       [structural]
  rule <k>I1:Int || I2:Int => 0 ...</k>
       requires ((I1 ==Int 0) andBool (I2 ==Int 0))
       [structural]
  //end: arithmetic operations
  
  rule <k> fun X:TVar OTYPE -> Term => !N:KVar ... </k>
       <repo> ... .Map => (!N |-> fun X OTYPE -> Term) ... </repo>
  rule if 0 then T1:Term else T0:Term => T0
  rule <k>if I:Int then T1:Term else T0:Term => T1 ... </k>
       requires (I =/=Int 0)
       [structural]
  rule <k>let X:KVar = V:Val in T2:Term => T2[V/X] ... </k>
       [structural]
  rule <k>V:Val ; T2:Term => T2 ... </k>
       [structural]
  rule <k> letrec F:KVar X:TVar OTYPE = T1:Term in T2:Term => T2[!N:KVar/F] ... </k>
       <repo> ... .Map => (!N |-> (fun X OTYPE -> (T1[!N/F]))) ... </repo>
       [structural]

  //method application and evaluation boxes
  syntax Term ::= "{|" Term "|}" [strict(1)]
  rule <k> M:KVar V:Val => {| T[V/X] |} ... </k>
       <repo> ... M |-> (fun (X : ATYPE) OTYPE -> T) ... </repo>
       <kbound> K => K -Int 1 </kbound>
       requires (K =/=Int 0)
       [structural]
  rule <k> M:KVar V:Val => nil ... </k>
       <repo> ... M |-> (fun (X : ATYPE) OTYPE -> T) ... </repo>
       <kbound> 0 </kbound>
       [structural]
  rule <k> {| V:Val |} => V ... </k>
       <kbound> K => K +Int 1 </kbound>
       [structural]

  //symbolic non-deterministic transitions
  rule <k>assert X:KVar => fail ... </k>
       <sig> SIG </sig>
       <pc>PC => PC (assert (= X 0))</pc>
       requires CheckSAT(SIG PC (assert (= X 0)))
       [transition]
  rule <k>assert X:KVar => () ... </k>
       <sig> SIG </sig>
       <pc>PC => PC (assert (not (= X 0)))</pc>
       requires CheckSAT(SIG PC (assert (not (= X 0))))
       [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T0 ...</k>
       <sig> SIG </sig>
       <pc>PC => PC (assert (= X 0))</pc>
       requires CheckSAT(SIG PC (assert (= X 0)))
       [transition]
  rule <k>if X:KVar then T1:Term else T0:Term => T1 ...</k>
       <sig> SIG </sig>
       <pc>PC => PC (assert (not (= X 0)))</pc>
       requires CheckSAT(SIG PC (assert (not (= X 0))))
       [transition]

  //symbolic deterministic transitions
  rule <k> not X1:KVar => !X:KVar ... </k> //not
       <state> Sigma => Sigma[!X <- not X1] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 0) 1 0))) </sig>
       [structural]
  rule <k> X1:KVar + V2:Val => !X:KVar ... </k> //plus
       <state> Sigma => Sigma[!X <- X1 + V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ X1 ValToSMT(V2)))) </sig>
       [structural]
  rule <k> V1:Val + X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 + X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (+ ValToSMT(V1) X2))) </sig>
       [structural]
  rule <k> X1:KVar - V2:Val => !X:KVar ... </k> //minus
       <state> Sigma => Sigma[!X <- X1 - V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- X1 ValToSMT(V2)))) </sig>
       [structural]
  rule <k> V1:Val - X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 - X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (- ValToSMT(V1) X2))) </sig>
       [structural]
  rule <k> X1:KVar * V2:Val => !X:KVar ... </k> //times
       <state> Sigma => Sigma[!X <- X1 * V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* X1 ValToSMT(V2)))) </sig>
       [structural]
  rule <k> V1:Val * X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 * X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (* ValToSMT(V1) X2))) </sig>
       [structural]
  rule <k> X1:KVar / V2:Val => !X:KVar ... </k> //times
       <state> Sigma => Sigma[!X <- X1 * V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (/ X1 ValToSMT(V2)))) (assert (not (= ValToSMT(V2) 0)))</sig>
       [structural]
  rule <k> V1:Val / X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 * X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (/ ValToSMT(V1) X2))) (assert (not (= X2 0)))</sig>
       [structural]
  rule <k> X1:KVar == V2:Val => !X:KVar ... </k> //equals
       <state> Sigma => Sigma[!X <- X1 == V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= X1 ValToSMT(V2)) 1 0))) </sig>
       [structural]
  rule <k> V1:Val == X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 == X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (= ValToSMT(V1) X2) 1 0))) </sig>
       [structural]
  rule <k> X1:KVar < V2:Val => !X:KVar ... </k> //lessthan
       <state> Sigma => Sigma[!X <- X1 < V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< X1 ValToSMT(V2)) 1 0))) </sig>
       [structural]
  rule <k> V1:Val < X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 < X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (< ValToSMT(V1) X2) 1 0))) </sig>
       [structural]
  rule <k> X1:KVar && V2:Val => !X:KVar ... </k> //and
       <state> Sigma => Sigma[!X <- X1 && V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (or (= X1 0) (= ValToSMT(V2) 0)) 0 1))) </sig>
       [structural]
  rule <k> V1:Val && X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 && X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (or (= ValToSMT(V1) 0) (= X2 0)) 0 1))) </sig>
       [structural]
  rule <k> X1:KVar || V2:Val => !X:KVar ... </k> //or
       <state> Sigma => Sigma[!X <- X1 || V2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= X1 0) (= ValToSMT(V2) 0)) 0 1))) </sig>
       [structural]
  rule <k> V1:Val || X2:KVar => !X:KVar ... </k>
       <state> Sigma => Sigma[!X <- V1 || X2] </state>
       <sig> SIG => SIG (declare-const !X Int) (assert (= !X (ite (and (= ValToSMT(V1) 0) (= X2 0)) 0 1))) </sig>
       [structural]

  ////////////////////
  // GAME SEMANTICS //
  ////////////////////
  // rules to traverse pairs and add names:
  //----------------------------------------
  syntax Term ::= "prop_val" Term
  syntax Prog ::= "in_pair"  Term  [strict(1)]
  rule prop_val (T1 , T2) => ((prop_val T1) , (prop_val T2))
       [structural]
  rule <k> prop_val X:KVar => X ... </k>
       <repo> ... X |-> (fun (A:ATYPE) :(OTYPE) -> T) ... </repo>
       <pub> P => P[X <- ATYPE] </pub>
       [structural]
  rule <k> prop_val X:KVar => X ... </k>
       <repo> R </repo>
       requires notBool (X in_keys(R))
       [structural]
  rule <k> prop_val V:Val => V ... </k>
       <repo> R </repo>
       requires notBool isKVar(V)
       [structural]
  rule <k> in_pair V:Val => !OPPONENT! </k>
       [structural]
  // proponent question:
  //---------------------
  // arg X is a method name
  rule <k> M:KVar X:KVar ~> E => !OPPONENT! </k>
       <eval> ES => M~>(Context E)~>ES </eval>
       <repo> ... X |-> (fun (A:ATYPE) :(OTYPE) -> T) ... </repo>
       <abs> ... (M |-> _) ... </abs>
       <pub> P => P[X <- (ATYPE->OTYPE)] </pub>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call (M X) </trace>
       [transition]
  // arg X is a ground-type variable
  rule <k> M:KVar X:KVar ~> E => !OPPONENT! </k>
       <eval> ES => M~>(Context E)~>ES </eval>
       <repo> R </repo>
       <abs> ... (M |-> _) ... </abs>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call (M X) </trace>
       requires notBool (X in_keys(R))
       [transition] 
  // arg V is a concrete value
  rule <k> M:KVar V:Val ~> E => in_pair (prop_val V) </k>
       <eval> ES => M~>(Context E)~>ES </eval>
       <abs> ... (M |-> _ ) ... </abs>
       <lbound> I => L </lbound>
       <lzero>  L </lzero>
       <trace> TAU => TAU ~> call (M V) </trace>
       requires notBool isKVar(V)
       [transition]
  // proponent answer:
  //-------------------
  // return value M is a method name
  rule <k> X:KVar => !OPPONENT! </k>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <repo> ... X |-> (fun (A:ATYPE) :(OTYPE) -> T ) ... </repo>
       <pub> P => P[X <- (ATYPE->OTYPE)] </pub>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M X </trace>
       [transition] //TODO? refresh names
  // return value X is a variable of ground type
  rule <k> X:KVar => !OPPONENT! </k>
       <repo> R </repo>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M X </trace>
       requires notBool (X in_keys(R))
       [transition]
  // return value V is a value
  rule <k> V:Val => in_pair (prop_val V) </k>
       <eval> (L:Int)~>(M:KVar)~>ES => ES </eval>
       <lbound> I => L </lbound>
       <trace> TAU => TAU ~> ret M V </trace>
       requires notBool isKVar(V)
       [transition]

  // rules to create fresh opponent values:
  //----------------------------------------
  syntax Term ::= "opp_val" Type
  rule opp_val (T1 * T2) => (opp_val T1 , opp_val T2)
  rule <k>opp_val (T1 -> T2) => !M:KVar ...</k>
       <abs> ... .Map => (!M |-> (T1 -> T2)) ... </abs>
  rule <k> opp_val int => !X:KVar ...</k>
       <sig> SIG => SIG (declare-const !X Int) </sig>
  rule <k> opp_val unit => () ...</k>
       <sig> SIG => SIG (declare-const !X Int) </sig>
  // opponent question:
  //--------------------
  syntax Prog ::= "opp_question" Map
  rule <k> !OPPONENT! => opp_question P </k>
       <pub> P </pub>
       <lbound> L:Int </lbound>
       requires (L =/=Int 0)
       [transition,structural]
  rule <k> !OPPONENT! => nil </k>
       <lbound> 0 </lbound>
       [transition,structural]
  syntax Prog ::= "in_question" KVar Term  [strict(2)]
  rule <k> opp_question ((M |-> (XTYPE->OTYPE)) P:Map) => in_question M (opp_val XTYPE) </k>
       <eval> ES => (L -Int 1)~>(M:KVar)~>ES </eval>
       <lbound> L </lbound>
       [transition,structural]
  rule <k> in_question M V:Val => M V </k>
       <trace> TAU => TAU ~> call M V </trace>
       [structural]
  rule <k> opp_question ((M |-> T) P:Map) => opp_question P </k>
       requires (P =/=K .Map)
       [transition,structural]
  // opponent answer:
  //------------------
  syntax Prog ::= "in_answer" KVar Term  [strict(2)]
  rule <k> !OPPONENT! => in_answer M (opp_val OTYPE) ~> E </k>
       <eval> M ~> (Context E) ~> ES => ES </eval>
       <abs> ... M |-> (XTYPE->OTYPE) ... </abs>
       [transition,structural]
  rule <k> in_answer M V:Val ~> E => V ~> E </k>
       <trace> TAU => TAU ~> ret M V </trace>
       [structural]
endmodule
