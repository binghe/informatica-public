/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

import static org.junit.Assert.assertEquals;
import org.junit.Test;

/*
 * Test #15: code/3.fool
 */

public final class Code3Test extends UnitTest {
    @Test
    public void testCode3() {
	prog = "let bool foo(int x)\n if (x==0) then { true }\n else { false };\n in foo(3);\n";
	result = 0;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <foo():bool> is 0
defined variable x in <foo(int):bool>
defined function: <foo(int):bool>
locals: []
created new generic function: foo
added new method foo(int) into gf
 done.
4. Type Analysis:
type of prog is: bool
5. Emit Bytecode:
defining function foo(int) [nargs: 1(0 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         35
0005:	load       0
0010:	iconst     0
0015:	ieq          
0016:	null         
0017:	ieq          
0018:	brt        33
0023:	iconst     1
0028:	br         34
0033:	null         
0034:	ret          
0035:	iconst     3
0040:	call       #0:foo(int)@5
0045:	halt         

7. Run Bytecode:
0
 */
