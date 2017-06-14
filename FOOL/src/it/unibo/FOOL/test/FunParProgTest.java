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
 * Test #9: global functions with literal parameters
 */

public final class FunParProgTest extends UnitTest {
    @Test
    public void testFunParProg() {
	prog = "let int y = 2; int f(int x) (x+y); in f(1);\n";
	result = 3;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
defined variable y in [y]
base ID of <f():int> is 1
defined variable x in <f(int):int>
defined function: <f(int):int>
locals: [y]
created new generic function: f
added new method f(int) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function f(int) [nargs: 2(1 + 1), nlocals: 0]
nlocals for top-level LET: 1
 done.
6. Disassemble Bytecode:
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
0037:	call       #0:f(int)@15
0042:	halt         

7. Run Bytecode:
3
 */
