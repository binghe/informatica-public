/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #10: Local functions without local vars (code/5.fool)
 */

public final class Code5Test extends ProgTest {
	public static void main(String[] args) {
		prog = "let int foo(int n) \nlet int gee(int n) n+1 ; in \nif (n==0) then { 1 } else { n*gee(n + -1) } ; \nin print(foo(3)) ;\n";
		run();
	}
}

/*
5. Emit Bytecode:
defining function foo [nargs: 1(0 + 1), nlocals: 0]
defining function gee [nargs: 2(1 + 1), nlocals: 0]
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         78
0005:	br         22
0010:	load       1
0015:	iconst     1
0020:	iadd         
0021:	ret          
0022:	load       0
0027:	iconst     0
0032:	ieq          
0033:	null         
0034:	ieq          
0035:	brt        50
0040:	iconst     1
0045:	br         77
0050:	load       0
0055:	load       0
0060:	load       0
0065:	iconst     -1
0070:	iadd         
0071:	call       #1:gee()@10
0076:	imul         
0077:	ret          
0078:	iconst     3
0083:	call       #0:foo()@5
0088:	print        
0089:	halt         

7. Run Bytecode:
9
 */