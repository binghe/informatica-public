/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.*;
import org.junit.*;

/*
 * Test #16: multiple print blocks in one prog
 */

public final class PrintsTest extends UnitTest {
    @Test
    public void testPrints() {
	prog = "print 1; print 2; print 3;\n";
	result = 3;
	assertEquals(run(), result);
    }
}

/** @formatter:off
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	print        
0006:	iconst     2
0011:	print        
0012:	iconst     3
0017:	halt         

7. Run Bytecode:
1
2
3
 */
