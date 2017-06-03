/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #1: simple assembly code
 */

import it.unibo.FOOL.vm.*;

public final class InterpreterTest {
	public static void main(String[] args) {
		Assembler assem = new Assembler();
		assem.gen("iconst", 1);
		assem.gen("iconst", 1);
		assem.gen("iadd");
		assem.gen("print");
		assem.gen("halt");

		Disassembler disasm = new Disassembler(assem);
		disasm.disassemble();
		Interpreter vm = new Interpreter(assem);
		try {
			vm.exec();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}

/* Test output:
Disassembly:
0000:	iconst     1
0005:	iconst     1
0010:	iadd         
0011:	print        
0012:	halt         

2
 */
