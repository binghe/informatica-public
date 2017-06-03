/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #9: global functions with literal parameters
 */

public final class FunParProgTest extends ProgTest {
	public static void main(String[] args) {
		prog = "let int y = 2; int f(int x) (x+y); in print f(1);\n";
		run();
	}
}

/*
Disassembly:
.global 0
0000:	iconst     2
0005:	store      0
0010:	br         27
0015:	load       1
0020:	load       0
0025:	iadd         
0026:	ret          
0027:	load       0
0032:	iconst     1
0037:	call       #0:f()@15
0042:	print        
0043:	halt         

7. Run Bytecode:
3
 */