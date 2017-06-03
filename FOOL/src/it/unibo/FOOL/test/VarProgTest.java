/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #7: global variables only
 */

public final class VarProgTest extends ProgTest {
	public static void main(String[] args) {
		prog = "let int x = 1; int y = 2; in print x;\n";
		run();
	}
}

/*
5. Emit Bytecode:
nlocals for top-level LET: 2
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	store      0
0010:	iconst     2
0015:	store      1
0020:	load       0
0025:	print        
0026:	halt         

7. Run Bytecode:
1
 */
