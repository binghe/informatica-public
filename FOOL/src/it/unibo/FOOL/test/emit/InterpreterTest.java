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

public final class InterpreterTest {
    @Test
    public void testInterpreter() {
	Assembler assem = new Assembler();
	assem.gen("iconst", 1);
	assem.gen("iconst", 1);
	assem.gen("iadd");
	assem.gen("halt");

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	Object retVal = null;
	try {
	    retVal = vm.exec();
	} catch (Exception e) {
	    e.printStackTrace();
	}
	System.out.println(retVal);
	assertEquals(retVal, 2);
    }
}

/** @formatter:off
Disassembly:
.global 0
0000:	iconst     1
0005:	iconst     1
0010:	iadd         
0011:	halt         

2
 */
