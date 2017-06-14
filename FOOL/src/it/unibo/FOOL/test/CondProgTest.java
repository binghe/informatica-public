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
 * Test #4: condition (if..then..else) expressions (assembly)
 */

public final class CondProgTest extends UnitTest {
    @Test
    public void testCondProg() {
	prog = "(if (if true then { false } else { true }) then {1} else {2});\n";
	result = 2;
	assertEquals(run(), result);
    }
}

/** @formatter:off
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	null         
0006:	ieq          
0007:	brt        18
0012:	null         
0013:	br         23
0018:	iconst     1
0023:	null         
0024:	ieq          
0025:	brt        40
0030:	iconst     1
0035:	br         45
0040:	iconst     2
0045:	print        
0046:	halt         

7. Run Bytecode:
2
 */
