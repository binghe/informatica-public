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
 * Test #13: code/6.fool (multiple local functions with parameters)
 */

public final class Code6Test extends UnitTest {
    @Test
    public void testCode6() {
	prog = "let int gee(int n) n+1 ; \n" + "int foo(int n)\n if (n==0) then { 1 } else { n*gee(n + -1) } ;\n"
		+ "in foo(3) ;\n";
	result = 9;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <gee():int> is 0
defined variable n in <gee(int):int>
defined function: <gee(int):int>
base ID of <foo():int> is 0
defined variable n in <foo(int):int>
defined function: <foo(int):int>
locals: []
created new generic function: gee
added new method gee(int) into gf
created new generic function: foo
added new method foo(int) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function gee(int) [nargs: 1(0 + 1), nlocals: 0]
defining function foo(int) [nargs: 1(0 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         17
0005:	load       0
0010:	iconst     1
0015:	iadd         
0016:	ret          
0017:	br         73
0022:	load       0
0027:	iconst     0
0032:	ieq          
0033:	null         
0034:	ieq          
0035:	brt        50
0040:	iconst     1
0045:	br         72
0050:	load       0
0055:	load       0
0060:	iconst     -1
0065:	iadd         
0066:	call       #0:gee(int)@5
0071:	imul         
0072:	ret          
0073:	iconst     3
0078:	call       #1:foo(int)@22
0083:	halt         

7. Run Bytecode:
9
 */
