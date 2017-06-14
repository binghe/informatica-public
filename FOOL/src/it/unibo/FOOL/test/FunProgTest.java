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
 * Test #8: global functions without parameters
 */

public final class FunProgTest extends UnitTest {
    @Test
    public void testFunProg() {
	prog = "let int f() 1; int g() 2; in f();\n";
	result = 1;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <f():int> is 0
defined function: <f():int>
base ID of <g():int> is 0
defined function: <g():int>
locals: []
created new generic function: f
added new method f() into gf
created new generic function: g
added new method g() into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function f() [nargs: 0(0 + 0), nlocals: 0]
defining function g() [nargs: 0(0 + 0), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         11
0005:	iconst     1
0010:	ret          
0011:	br         22
0016:	iconst     2
0021:	ret          
0022:	call       #0:f()@5
0027:	halt         

7. Run Bytecode:
1
 */
