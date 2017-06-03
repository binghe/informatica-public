/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test;

/*
 * Test #3: labels in assembly
 */

import it.unibo.FOOL.vm.*;

public final class LabelTest {
	public static void main(String[] args) {
		Assembler assem = new Assembler();
		Label end = assem.newLabel("end");
		Label end1 = assem.newLabel("end");
		assert (end != end1);

		assem.gen("br", end);
		assem.gen("br", end1);
		assem.setLabel(end);
		assem.gen("halt");
		assem.setLabel(end1);
		assem.check();

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

/*
Disassembly:
0000:	br         10
0005:	br         11
0010:	halt         

 */
