/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

/***
 * The ANTLR grammar described here is based on the FOOL language specification provided by
 * Prof. Cosimo Laneve, with minimal modifications.
 ***/

/*
 * Modified by Chun Tian with the following changes:
 * - Simplified LINECOMENTS and BLOCKCOMENTS using non-greedy matching
 * - Added a "block" rule to be used in "prog" and "fun" rules
 * - Extended "type" to support class types
 * - Multiple top-level blocks (at no charge)
 * - Added OO extension (a.k.a. FOOL+)
 */

grammar FOOL;

prog   : (block SEMIC)+ ;

block  : body		#codeBody
       | varasm		#globalVar
       | defcls		#classDef // for OO support (part 1 of 5)
       ;

body   : exp		#singleExp
       | let exp	#letInExp
       ;

// BEGIN: additions for OO support (part 2 of 5)
defcls : CLASS ID (LPAR ( vardec (COMMA vardec)* )? RPAR)?
	 ASM OBJECT supers? slots ;

supers : INHER ID (LPAR (exp (COMMA exp)*)? RPAR)? SEMIC;

slots  : (slotd SEMIC)* END ;

slotd  : vardec		#slotNoInit
       | varasm		#slotInit
       ;
// END

let    : LET (dec SEMIC)+ IN ;

dec    : varasm         #varAssignment
       | fun            #funDeclaration
       ;

fun    : type ID LPAR ( vardec ( COMMA vardec)* )? RPAR body ;

varasm : vardec ASM exp ;
vardec : type ID ;

type   : INT
       | BOOL
       | ID // class types for OO support (part 3 of 5)
       ;

exp    : left=term (PLUS right=exp)? ;
term   : left=factor (TIMES right=term)? ;
factor : left=value (EQ right=value)? ;

value  : INTEGER					#intVal
       | ( TRUE | FALSE )				#boolVal
       | LPAR exp RPAR					#baseExp
       | IF cond=exp THEN CLPAR thenBranch=exp CRPAR ELSE CLPAR elseBranch=exp CRPAR #ifExp
       | ID						#varExp
       | ID LPAR (exp (COMMA exp)* )? RPAR		#funExp
       | PRINT exp					#printExp
       // BEGIN: additions for OO support (part 4 of 5)
       | 'new' ID (LPAR (exp (COMMA exp)*)? RPAR)?	#classExp
       | value '.' ID LPAR (exp (COMMA exp)*)? RPAR	#methodExp
       | value '.' ID					#slotExp
       // END
       ;

SEMIC  : ';' ;
COLON  : ':' ;
COMMA  : ',' ;
EQ     : '==' ;
ASM    : '=' ;
PLUS   : '+' ;
TIMES  : '*' ;
TRUE   : 'true' ;
FALSE  : 'false' ;
LPAR   : '(' ;
RPAR   : ')' ;
CLPAR  : '{' ;
CRPAR  : '}' ;
IF     : 'if' ;
THEN   : 'then' ;
ELSE   : 'else' ;
PRINT  : 'print' ; 
LET    : 'let' ;
IN     : 'in' ;
VAR    : 'var' ;
FUN    : 'fun' ;
INT    : 'int' ;
BOOL   : 'bool' ;

// BEGIN: additions for OO support (part 5 of 5)
CLASS  : 'class' ;
OBJECT : 'object' ;
INHER  : 'inherit' ;
END    : 'end' ;
// END

// Numbers
fragment DIGIT : '0'..'9';    
INTEGER        : ('-')?DIGIT+;

// IDs
fragment CHAR  : 'a'..'z' | 'A'..'Z' ;
ID             : CHAR (CHAR | DIGIT)* ;

// ESCAPED SEQUENCES
WS             : [ \t\r\n]+ -> skip;
LINECOMENTS    : '//' .*? [\r\n]+ -> skip;
BLOCKCOMENTS   : '/*' .*? '*/' -> skip;

// ERR
ERR            : . -> channel(HIDDEN); 
