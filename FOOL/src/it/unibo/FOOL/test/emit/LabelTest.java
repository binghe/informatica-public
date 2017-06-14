/*
 * An bytecode compiler and interpreter for FOOL+ language in Java/ANTLR
 * 
 * Course project for COMPILATORI E INTERPRETI (ANALISI STATICA DI PROGRAMMI)
 * Copyright(R) 2017  Chun Tian, University of Bologna
 */

package it.unibo.FOOL.test.emit;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import it.unibo.FOOL.svm.*;

/*
 * Test #3: labels in assembly
 */

public final class LabelTest {
    @Test
    public void testLabel() {
	Assembler assem = new Assembler();
	Label end = assem.newLabel("end");
	Label end1 = assem.newLabel("end");
	assert (end != end1);

	assem.br(end);
	assem.br(end1);
	assem.setLabel(end);
	assem.halt();
	assem.setLabel(end1);
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	Object retVal = true;
	retVal = vm.exec();
	assertEquals(retVal, null);
    }
}

/** @formatter:off
Disassembly:
.global 0
0000:	br         10
0005:	br         11
0010:	halt         

 */
