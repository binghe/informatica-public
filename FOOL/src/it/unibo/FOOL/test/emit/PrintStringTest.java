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

public final class PrintStringTest extends UnitTest {
    @Test
    public void testPrintString() {
	Assembler assem = new Assembler();

	assem.gen("sconst", "hello world!");
	assem.gen("print");
	assem.gen("iconst", 1);
	assem.gen("halt");
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	Object retVal = vm.exec();
	assertEquals(retVal, 1);
    }
}
