/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #8: global functions without parameters
 */

public final class FunProgTest extends ProgTest {
	public static void main(String[] args) {
		prog = "let int f() 1; int g() 2; in print f();\n";
		run();
	}
}

/*
Disassembly:
.global 0
0000:	br         11
0005:	iconst     1
0010:	ret          
0011:	br         22
0016:	iconst     2
0021:	ret          
0022:	call       #0:f()@5
0027:	print        
0028:	halt         

7. Run Bytecode:
1
 */
