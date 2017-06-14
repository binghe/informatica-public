/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.test.*;

/*
 * Method Test #4: chain of methods
 */

public final class MethodTest5 extends UnitTest {
    @Test
    public void testMethod5() {
	prog = "   class C = object end;					\n"
		+ "let C f(C o) o; 						\n"
		+ "    int g(C o) 1;						\n"
		+ "in (new C).f().g();						\n";
	result = 1;
	trace = true;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of class C is 1
defined class: class C(standard_object):{}
defined init function: <global.C_init():class C(standard_object):{}>
base ID of <f():class C(standard_object):{}> is 0
defined variable o in <f(C):class C(standard_object):{}>
defined function: <f(C):class C(standard_object):{}>
base ID of <g():int> is 0
defined variable o in <g(C):int>
defined function: <g(C):int>
locals: []
created new generic function: f
added new method f(C) into generic function f
created new generic function: g
added new method g(C) into generic function g
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function f(C) [nargs: 1(0 + 1), nlocals: 0]
defining function g(C) [nargs: 1(0 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         26
0005:	iconst     3
0010:	load       0
0015:	fstore     0
0020:	load       0
0025:	ret          
0026:	br         37
0031:	load       0
0036:	ret          
0037:	br         48
0042:	iconst     1
0047:	ret          
0048:	struct     1
0053:	call       #0:C_init()@5
0058:	call       #1:f(C)@31
0063:	call       #2:g(C)@42
0068:	halt         

7. Run Bytecode:
1
 */
