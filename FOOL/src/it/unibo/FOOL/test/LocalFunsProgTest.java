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
 * Test #12: Local function chains with pars
 */

public final class LocalFunsProgTest extends UnitTest {
    @Test
    public void testLocalFunsProg() {
	prog = "let int foo(int x) let int bar(int y) x+y; in bar(1); in foo(2);\n";
	result = 3;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <foo():int> is 0
defined variable x in <foo(int):int>
base ID of [] is 1
base ID of <bar():int> is 1
defined variable y in <bar(int):int>
defined function: <bar(int):int>
locals: []
defined function: <foo(int):int>
locals: []
created new generic function: foo
added new method foo(int) into gf
created new generic function: bar
added new method bar(int) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function foo(int) [nargs: 1(0 + 1), nlocals: 0]
defining function bar(int) [nargs: 2(1 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         38
0005:	br         22
0010:	load       0
0015:	load       1
0020:	iadd         
0021:	ret          
0022:	load       0
0027:	iconst     1
0032:	call       #1:bar(int)@10
0037:	ret          
0038:	iconst     2
0043:	call       #0:foo(int)@5
0048:	halt         

7. Run Bytecode:
3
 */
