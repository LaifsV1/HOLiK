require "substitution.k"

module Z3-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS-SYNTAX
  imports INT-SYNTAX
  imports STRING

  syntax SMTLib ::= "(" "declare-const" KVar "Int" ")"
                  | "(" "declare-const" KVar "String" ")"
		  | "(" "check-sat" ")"
		  | "(" "get-model" ")"
                  | "(" "assert" SMTProp ")"
		  | SMTLib SMTLib	                    [left]
  syntax SMTProp ::= Bool | SMTVal
                   | "(" "<" SMTVal SMTVal ")"
                   | "(" ">" SMTVal SMTVal ")"
                   | "(" "<=" SMTVal SMTVal ")"
                   | "(" ">=" SMTVal SMTVal ")"
                   | "(" "/" SMTVal SMTVal ")"
		   | "(" "*" SMTVal SMTVal ")"
                   | "(" "+" SMTVal SMTVal ")"
                   | "(" "-" SMTVal SMTVal ")"
                   | "(" "="   SMTProp SMTProp ")"
                   | "(" "and" SMTProp SMTProp ")"
                   | "(" "or"  SMTProp SMTProp ")"
		   | "(" "not" SMTProp ")"
                   | "(" "ite"  SMTProp SMTProp SMTProp ")"
  syntax SMTVal  ::= KVar | Int

  syntax String ::= PropToString(SMTProp) [function]
  syntax String ::= BoolToString(Bool) [function, functional]
  syntax String ::= XToString(SMTVal)  [function, functional]
  syntax String ::= XToString(Int) [function]
  syntax String ::= KVar2String(KVar) [function, functional, hook(STRING.token2string)]

  rule BoolToString( true )  => "true"
  rule BoolToString( false ) => "false"
  rule PropToString( V:SMTVal ) => XToString(V)
  rule PropToString( B:Bool ) => BoolToString(B)
  rule XToString( I:Int ) => Int2String(I)
  rule XToString( K:KVar ) => KVar2String(K)

  rule PropToString( ( < V1 V2 ) ) => "( < " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( > V1 V2 ) ) => "( > " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( <= V1 V2 ) ) => "( <= " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( >= V1 V2 ) ) => "( >= " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( * V1 V2 ) ) => "( * " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( / V1 V2 ) ) => "( / " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( + V1 V2 ) ) => "( + " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( - V1 V2 ) ) => "( - " +String XToString(V1) +String " " +String XToString(V2) +String " )"
  rule PropToString( ( = P1 P2 ) ) => "( = " +String PropToString(P1) +String " " +String PropToString(P2) +String " )"
  rule PropToString( ( and P1 P2 ) ) => "( and " +String PropToString(P1) +String " " +String PropToString(P2) +String " )"
  rule PropToString( ( or P1 P2 ) ) => "( or " +String PropToString(P1) +String " " +String PropToString(P2) +String " )"
  rule PropToString( ( not P1 ) ) => "( not " +String PropToString(P1) +String " )"
  rule PropToString( ( ite P1 P2 P3 ) ) => "( ite " +String PropToString(P1) +String " " +String PropToString(P2) +String " " +String PropToString(P3) +String " )"
  
  syntax String ::= LibToString(SMTLib)  [function]
  rule LibToString( ( declare-const X Int) ) => "( declare-const " +String XToString(X) +String " Int )"
  rule LibToString( ( check-sat ) ) => "( check-sat )"
  rule LibToString( ( get-model ) ) => "( get-model )"
  rule LibToString( ( assert P ) ) => "( assert " +String PropToString(P) +String " )"
  rule LibToString( P1 P2 ) => LibToString(P1) +String LibToString(P2)
endmodule

module Z3
  imports SUBSTITUTION
  imports Z3-SYNTAX
  imports DOMAINS
  imports STRING
  
  syntax KResult ::= Bool  
  syntax Bool ::= CheckSAT(SMTLib)  [function]
  syntax Bool ::= SystemSAT(KItem)  [function]

  rule CheckSAT(P) => SystemSAT(#system("echo \"" +String LibToString(P) +String "(check-sat)\" | z3 -in"))
  rule SystemSAT(#systemResult ( 0, "sat\n" ,   "" )) => true
  rule SystemSAT(#systemResult ( 0, "unsat\n" , "" )) => false
endmodule
