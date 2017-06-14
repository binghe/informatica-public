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
 * Test #7: global variables only
 */

public final class VarProgTest extends UnitTest {
    @Test
    public void testVarProg() {
	prog = "let int x = 1; int y = 2; in x;\n";
	result = 1;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
defined variable x in [x]
defined variable y in [x, y]
locals: [x, y]
 done.
4. Type Analysis:
type of prog is: int
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
0025:	halt         

7. Run Bytecode:
1
 */
