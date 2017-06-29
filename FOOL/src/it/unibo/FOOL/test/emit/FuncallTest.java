/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.emit;

import static org.junit.Assert.*;
import org.junit.*;
import it.unibo.FOOL.svm.*;

public final class FuncallTest {
    @Test
    public void testFuncall() {
	Assembler assem = new Assembler();

	assem.defineFunction("add", 2, 0);
	assem.gen("load", 0); // load 1st argument into stack
	assem.gen("load", 1); // load 2nd argument into stack
	assem.gen("iadd");
	assem.gen("ret");

	assem.defineFunction("_main", 0, 0);
	assem.gen("iconst", 1);
	assem.gen("iconst", 2);
	assem.gen("call", new Function("add"));
	assem.gen("halt");
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	vm.setTrace(true);
	Object retVal = 3;
	try {
	    retVal = vm.exec();
	} catch (Exception e) {
	    e.printStackTrace();
	}
	System.out.println(retVal);
	assertEquals(retVal, 3);
    }
}

/** @formatter:off
Disassembly:
.global 0
0000:	load       0
0005:	load       1
0010:	iadd         
0011:	ret          
0012:	iconst     1
0017:	iconst     2
0022:	call       #0:add@0
0027:	halt         

Trace:
0012:	iconst     1		stack=[ ], calls=[ main ]
0017:	iconst     2		stack=[ 1 ], calls=[ main ]
0022:	call       #0:add@0		stack=[ 1 2 ], calls=[ main ]
0000:	load       0		stack=[ ], calls=[ main add ]
0005:	load       1		stack=[ 1 ], calls=[ main add ]
0010:	iadd         		stack=[ 1 2 ], calls=[ main add ]
0011:	ret          		stack=[ 3 ], calls=[ main add ]
3
 */
