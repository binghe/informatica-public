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
 * Test #14: code/7.fool (local functions with 2 parameters)
 */

public class Code7Test extends UnitTest {
    @Test
    public void testCode7() {
	prog = "let int foo (int n, bool f) 0 ;\n in foo(3, false);\n";
	trace = true;
	result = 0;
	assertEquals(run(), result);
    }
}

/** @formatter:off
3. Symbol Analysis:
base ID of <foo():int> is 0
defined variable n in <foo(int):int>
defined variable f in <foo(int,bool):int>
defined function: <foo(int,bool):int>
locals: []
created new generic function: foo
added new method foo(int,bool) into gf
 done.
4. Type Analysis:
type of prog is: int
5. Emit Bytecode:
defining function foo(int,bool) [nargs: 2(0 + 2), nlocals: 0]
nlocals for top-level LET: 0
 done.
6. Disassemble Bytecode:
Disassembly:
.global 0
0000:	br         11
0005:	iconst     0
0010:	ret          
0011:	iconst     3
0016:	null         
0017:	call       #0:foo(int,bool)@5
0022:	halt         

7. Run Bytecode:
Trace:
0000:	br         11		stack=[ ], calls=[ _main ]
0011:	iconst     3		stack=[ ], calls=[ _main ]
0016:	null         		stack=[ 3 ], calls=[ _main ]
0017:	call       #0:foo(int,bool)@5		stack=[ 3 0 ], calls=[ _main ]
0005:	iconst     0		stack=[ ], calls=[ _main foo(int,bool) ]
0010:	ret          		stack=[ 0 ], calls=[ _main foo(int,bool) ]
0
 */
