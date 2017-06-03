/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #5: function calls without parameters (assembly)
 */

import it.unibo.FOOL.vm.*;

public final class FunctionTest {
	public static void main(String[] args) {
		Assembler assem = new Assembler();

		assem.defineFunction("g", 0, 0);
		assem.gen("iconst", 1);
		assem.gen("ret");
		
		assem.defineFunction("f", 0, 0);
		assem.gen("call", new Function("g"));
		assem.gen("ret");
		
		assem.defineFunction("main", 0, 0);
		assem.gen("call", new Function("g"));
		assem.gen("pop");
		assem.gen("call", new Function("f"));
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
0000:	iconst     1
0005:	ret          
0006:	call       #0:g()@0
0011:	ret          
0012:	call       #0:g()@0
0017:	pop          
0018:	call       #1:f()@6
0023:	print        
0024:	halt         

0012:	call       #0:g()@0		stack=[ ], calls=[ main ]
0000:	iconst     1		stack=[ ], calls=[ main g ]
0005:	ret          		stack=[ 1 ], calls=[ main g ]
0017:	pop          		stack=[ 1 ], calls=[ main ]
0018:	call       #1:f()@6		stack=[ ], calls=[ main ]
0006:	call       #0:g()@0		stack=[ ], calls=[ main f ]
0000:	iconst     1		stack=[ ], calls=[ main f g ]
0005:	ret          		stack=[ 1 ], calls=[ main f g ]
0011:	ret          		stack=[ 1 ], calls=[ main f ]
0023:	print        		stack=[ 1 ], calls=[ main ]
1
 */
