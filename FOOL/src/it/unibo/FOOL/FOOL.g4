/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

/***
 * The ANTLR grammar described here is based on the FOOL language specification provided by
 * Prof. Cosimo Laneve, with minimal modifications.
 * 
 * Changes by Chun Tian:
 * - Simplified LINECOMENTS and BLOCKCOMENTS using non-greedy matching
 * - Added a "block" rule to be used in "prog" and "fun" rules
 * - Extended "type" to support class types
 * - Multiple top-level blocks (at no charge)
 ***/

grammar FOOL;

prog   : (block SEMIC)+ ;

block  : exp		#singleExp
       | let exp	#letInExp
       ;

let    : LET (dec SEMIC)+ IN ;

dec    : varasm         #varAssignment
       | fun            #funDeclaration
       ;

fun    : type ID LPAR ( vardec ( COMMA vardec)* )? RPAR block ;

varasm : vardec ASM exp ;
vardec : type ID ;

type   : INT
       | BOOL
       | ID
       ;

exp    : left=term (PLUS right=exp)? ;
term   : left=factor (TIMES right=term)? ;
factor : left=value (EQ right=value)? ;

value  : INTEGER					#intVal
       | ( TRUE | FALSE )				#boolVal
       | LPAR exp RPAR					#baseExp
       | IF cond=exp THEN CLPAR thenBranch=exp CRPAR ELSE CLPAR elseBranch=exp CRPAR #ifExp
       | ID						#varExp
       | ID ( LPAR (exp (COMMA exp)* )? RPAR )?		#funExp
       | PRINT exp					#printExp
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
