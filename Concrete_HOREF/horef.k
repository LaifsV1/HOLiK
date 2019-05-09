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
                 | Term
  syntax Term  ::= "assert" Term                         [strict(1)]
                 | Val
		 | Lambda
 		 | "!" Ref
		 | "fst"  Term                           [strict(1)]
		 | "snd" Term                            [strict(1)]
		 //start: arithmetic operations
                 | "not" Term                            [seqstrict(1), right]
                 > Term "*" Term                         [seqstrict(1,2), left]
                 | Term "/" Term                         [seqstrict(1,2), left]
                 > Term "+" Term                         [seqstrict(1,2), left]
		 | Term "-" Term                         [seqstrict(1,2), left]
                 > Term "<" Term                         [seqstrict(1,2), left]
		 | Term "==" Term                        [seqstrict(1,2), left]
		 | Term "!=" Term                        [seqstrict(1,2), left]
		 > Term "&&" Term                        [seqstrict(1,2), left]
		 > Term "||" Term                        [seqstrict(1,2), left]
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
  syntax Method ::= KVar
  syntax Ref    ::= KVar

  syntax Lambda ::= "fun" KVar "->" Term    [binder]
endmodule

module HOREF
  imports HOREF-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  syntax KResult ::= Val

  configuration <T>
                  <k> $PGM:Lib </k>
		  <repo> .Map </repo>
		  <state> .Map </state>
		  <bound> 4 </bound>
	        </T>

  // PROG semantics
  rule <k> # set-bound I # L => L </k>
       <bound> _ => I </bound>

  // LIB operational semantics
  rule <k> import M:Method L => L </k>
       //todo ABSTRACT names

  // BLOCK operational semantics
  rule <k> fun R:Ref := M:Method ; B => B </k>
       <state> ... .Map => (R |-> M) ... </state>
  rule <k> int R:Ref := I:Int ; B => B </k>
       <state> ... .Map => (R |-> I) ... </state>
  rule <k> public M:Method X:KVar = { T:Term } ; B => B </k>
       <repo> ... .Map => (M |-> (fun X -> T)) ... </repo>
       //todo PUBLIC names
  rule <k> private M:Method X:KVar = { T:Term } ; B => B </k>
       <repo> ... .Map => (M |-> (fun X -> T)) ... </repo>

  // TERM operational semantics
  rule assert I:Int => () requires I =/=Int 0
  rule <k> ! R:Ref => V ... </k>
       <state> ... R |-> V ... </state>
  rule <k> R:Ref := V:Val => () ... </k>
       <state> ... R |-> (_ => V) ... </state>
  rule fst (T1,T2) => T1
  rule snd (T1,T2) => T2
  
  //begin: arithmetic operations
  rule not 0 => 1
  rule not I => 0                    requires I =/=Int 0
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=Int 0
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int < I2:Int => 1          requires I1 <Int I2
  rule I1:Int < I2:Int => 0          requires I1 >=Int I2
  rule I1:Int == I2:Int => 1         requires I1 ==Int I2
  rule I1:Int == I2:Int => 0         requires I1 =/=Int I2
  rule I1:Int != I2:Int => 1         requires I1 =/=Int I2
  rule I1:Int != I2:Int => 0         requires I1 ==Int I2
  rule I1:Int && I2:Int => 1         requires (I1 =/=Int 0) andBool (I2 =/=Int 0)
  rule I1:Int && I2:Int => 0         requires (I1 ==Int 0) orBool (I2 ==Int 0)
  rule I1:Int || I2:Int => 1         requires (I1 =/=Int 0) orBool (I2 =/=Int 0)
  rule 0 || 0 => 0
  //end: arithmetic operations
  
  rule <k> F:Lambda => !N:KVar ... </k>
       <repo> ... .Map => (!N |-> F) ... </repo>
  rule if 0 then T1:Term else T0:Term => T0
  rule if I:Int then T1:Term else T0:Term => T1 requires I =/=Int 0
  rule let X:KVar = V:Val in T2:Term => T2[V/X]
  rule T1:Term ; T2:Term => T2
  rule <k> letrec F:KVar X:KVar = T1:Term in T2:Term => T2[!N:KVar/F] ... </k>
       <repo> ... .Map => (!N |-> (fun X:KVar -> (T1[!N/F]))) ... </repo>

  //method application and evaluation boxes
  syntax Term ::= "{|" Term "|}" [strict(1)]
  rule <k> M:KVar V:Val => {| T[V/X] |} ... </k>
       <repo> ... M |-> (fun X -> T) ... </repo>
       <bound> I => I -Int 1 </bound> requires I =/=Int 0
  rule <k> {| V:Val |} => V ... </k>
       <bound> I => I +Int 1 </bound>
endmodule
