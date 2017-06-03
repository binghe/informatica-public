/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #6: function calls with parameters (assembly)
 */

import it.unibo.FOOL.vm.*;

public final class FuncallTest {
	public static void main(String[] args) {
		Assembler assem = new Assembler();

		assem.defineFunction("add", 2, 0);
		assem.gen("load", 0); // load 1st argument into stack
		assem.gen("load", 1); // load 2nd argument into stack
		assem.gen("iadd");
		assem.gen("ret");

		assem.defineFunction("main", 0, 0);
		assem.gen("iconst", 1);
		assem.gen("iconst", 2);
		assem.gen("call", new Function("add"));
		assem.gen("print");
		assem.gen("halt");
		assem.check();

	    Disassembler disasm = new Disassembler(assem);
	    disasm.disassemble();
		Interpreter vm = new Interpreter(assem);
		vm.setTrace(true);
		try {
			vm.exec();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}

/*
Disassembly:
0000:	load       0
0005:	load       1
0010:	iadd         
0011:	ret          
0012:	iconst     1
0017:	iconst     2
0022:	call       #0:add()@0
0027:	print        
0028:	halt         

Trace:
0012:	iconst     1		stack=[ ], calls=[ main ]
0017:	iconst     2		stack=[ 1 ], calls=[ main ]
0022:	call       #0:add()@0		stack=[ 1 2 ], calls=[ main ]
0000:	load       0		stack=[ ], calls=[ main add ]
0005:	load       1		stack=[ 1 ], calls=[ main add ]
0010:	iadd         		stack=[ 1 2 ], calls=[ main add ]
0011:	ret          		stack=[ 3 ], calls=[ main add ]
0027:	print        		stack=[ 3 ], calls=[ main ]
3
 */