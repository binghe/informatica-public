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
 * Test #11: Global functions with local vars
 */

public final class LocalVarProgTest extends UnitTest {
    @Test
    public void testLocalVarProg() {
	prog = "let int x = 1; int foo(int n) let int m = 2; in x + m + n; in foo(3);\n";
	result = 6;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
defined variable x in [x]
base ID of <foo():int> is 1
defined variable n in <foo(int):int>
base ID of [] is 2
defined variable m in [m]
locals: [m]
defined function: <foo(int):int>
locals: [x]
created new generic function: foo
added new method foo(int) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function foo(int) [nargs: 2(1 + 1), nlocals: 1]
nlocals for top-level LET: 1
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	iconst     1
0005:	store      0
0010:	br         43
0015:	iconst     2
0020:	store      2
0025:	load       0
0030:	load       2
0035:	load       1
0040:	iadd         
0041:	iadd         
0042:	ret          
0043:	load       0
0048:	iconst     3
0053:	call       #0:foo(int)@15
0058:	halt         

7. Run Bytecode:
6
 */
