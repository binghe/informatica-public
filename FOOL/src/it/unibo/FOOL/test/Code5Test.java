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
 * Test #10: Local functions without local vars (code/5.fool)
 */

public final class Code5Test extends UnitTest {
    @Test
    public void testCode5() {
	prog = "let int foo(int n) \n" + "let int gee(int n) n+1 ; in \n"
		+ "if (n==0) then { 1 } else { n*gee(n + -1) } ; \n" + "in foo(3);\n";
	result = 9;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <foo():int> is 0
defined variable n in <foo(int):int>
base ID of [] is 1
base ID of <gee():int> is 1
defined variable n in <gee(int):int>
defined function: <gee(int):int>
locals: []
defined function: <foo(int):int>
locals: []
created new generic function: foo
added new method foo(int) into gf
created new generic function: gee
added new method gee(int) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function foo(int) [nargs: 1(0 + 1), nlocals: 0]
defining function gee(int) [nargs: 2(1 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         78
0005:	br         22
0010:	load       1
0015:	iconst     1
0020:	iadd         
0021:	ret          
0022:	load       0
0027:	iconst     0
0032:	ieq          
0033:	null         
0034:	ieq          
0035:	brt        50
0040:	iconst     1
0045:	br         77
0050:	load       0
0055:	load       0
0060:	load       0
0065:	iconst     -1
0070:	iadd         
0071:	call       #1:gee(int)@10
0076:	imul         
0077:	ret          
0078:	iconst     3
0083:	call       #0:foo(int)@5
0088:	halt         

7. Run Bytecode:
9
 */
