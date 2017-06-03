/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #2: simple program with arithmetic operations only
 */

public class SimpleProgTest extends ProgTest {	
	public static void main(String[] args) {
		prog = "print ((2*3+5)==13) == false;\n";
		run();
	}
}

/*
Disassembly:
.global 0
0000:	iconst     2
0005:	iconst     3
0010:	imul         
0011:	iconst     5
0016:	iadd         
0017:	iconst     13
0022:	ieq          
0023:	null         
0024:	ieq          
0025:	print        
0026:	halt         

7. Run Bytecode:
1
 */
