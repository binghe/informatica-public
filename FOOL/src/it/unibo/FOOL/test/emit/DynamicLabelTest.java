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
import it.unibo.FOOL.test.*;

/*
 * Test: dynamic labels stored on stack
 */

public final class DynamicLabelTest extends UnitTest {
    @Test
    public void testLabel() {
	Assembler assem = new Assembler();
	Label end = assem.newLabel("end");

	assem.gen("br", end);
	assem.setLabel(end);
	assem.gen("halt");
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	Object retVal = true;
	retVal = vm.exec();
	assertEquals(retVal, null);
    }
}
