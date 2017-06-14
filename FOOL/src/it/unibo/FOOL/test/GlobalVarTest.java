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
 * Test #17: global variables
 */

public final class GlobalVarTest extends UnitTest {
    @Test
    public void testGlobalVar() {
	prog = "int i = 1; int j = 2; print i; j;\n";
	result = 2;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
defined variable i in [bool, int, standard_object, i]
defined variable j in [bool, int, standard_object, i, j]
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
 done.
6. Disassemble Bytecode:
Disassembly:
.global 2
0000:	iconst     1
0005:	gstore     0
0010:	iconst     2
0015:	gstore     1
0020:	gload      0
0025:	print        
0026:	gload      1
0031:	halt         

7. Run Bytecode:
1
2
 */
