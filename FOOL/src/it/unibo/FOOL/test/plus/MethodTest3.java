/**
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.plus;

/*
 * Method Test #3: two methods for irrelevant classes
 */

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.test.*;

public final class MethodTest3 extends UnitTest {
    @Test
    public void testMethod3() {
	prog = "   class C1 = object int x = 1; end;					\n"
		+ "class C2 = object int y = 2; end;					\n"
		+ "let int f(C1 a) a.x;							\n"
		+ "    int f(C2 b) b.y;							\n"
		+ "in f(new C1) + f(new C2);";
	result = 3;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of class C1 is 1
defined variable x in class C1(standard_object):{x}
defined class: class C1(standard_object):{x}
defined init function: <global.C1_init():class C1(standard_object):{x}>
base ID of class C2 is 1
defined variable y in class C2(standard_object):{y}
defined class: class C2(standard_object):{y}
defined init function: <global.C2_init():class C2(standard_object):{y}>
base ID of <f():int> is 0
defined variable a in <f(C1):int>
defined function: <f(C1):int>
base ID of <f():int> is 0
defined variable b in <f(C2):int>
defined function: <f(C2):int>
locals: []
created new generic function: f
added new method f(C1) into generic function f
added new method f(C2) into generic function f
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function f(C1) [nargs: 1(0 + 1), nlocals: 0]
defining function f(C2) [nargs: 1(0 + 1), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         41
0005:	iconst     1
0010:	load       0
0015:	fstore     1
0020:	iconst     1001
0025:	load       0
0030:	fstore     0
0035:	load       0
0040:	ret          
0041:	br         82
0046:	iconst     2
0051:	load       0
0056:	fstore     1
0061:	iconst     1002
0066:	load       0
0071:	fstore     0
0076:	load       0
0081:	ret          
0082:	br         98
0087:	load       0
0092:	fload      1
0097:	ret          
0098:	br         114
0103:	load       0
0108:	fload      1
0113:	ret          
0114:	struct     2
0119:	call       #0:C1_init()@5
0124:	call       #2:f(C1)@87
0129:	struct     2
0134:	call       #1:C2_init()@46
0139:	call       #3:f(C2)@103
0144:	iadd         
0145:	halt         

7. Run Bytecode:
3
 */
