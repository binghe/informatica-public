/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */


package it.unibo.FOOL.test;

/*
 * Test #11: Global functions with local vars
 */

public final class LocalVarProgTest extends ProgTest {
	public static void main(String[] args) {
		prog = "let int x = 1; int foo(int n) let int m = 2; in x + m + n; in print foo(3);\n";
		run();
	}
}

/*
5. Emit Bytecode:
defining function foo [nargs: 2(1 + 1), nlocals: 1]
nlocals for top-level LET: 1
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	store      0
0010:	br         43
0015:	iconst     2
0020:	store      2
0025:	load       0
0030:	load       2
0035:	load       1
0040:	iadd         
0041:	iadd         
0042:	ret          
0043:	load       0
0048:	iconst     3
0053:	call       #0:foo()@15
0058:	print        
0059:	halt         

7. Run Bytecode:
6
 */
