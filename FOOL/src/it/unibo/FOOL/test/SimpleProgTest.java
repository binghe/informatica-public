/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

/*
 * Test #2: simple program with arithmetic operations only
 */

public class SimpleProgTest extends UnitTest {
    @Test
    public void testSimpleProg() {
	prog = "((2*3+5)==13) == false;\n";
	result = 1;
	assertEquals(run(), result);
    }
}

/** @formatter:off
6. Disassemble Bytecode:
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
0025:	halt         

7. Run Bytecode:
1
 */
