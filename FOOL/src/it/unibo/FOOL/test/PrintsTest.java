/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #16: multiple print blocks in one prog
 */

public final class PrintsTest extends ProgTest {
	public static void main(String[] args) {
		prog = "print 1; print 2; print 3;\n";
		run();
	}
}

/*
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	print        
0006:	iconst     2
0011:	print        
0012:	iconst     3
0017:	print        
0018:	halt         

7. Run Bytecode:
1
2
3
*/
