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
 * Test: Writing loops in assembly code 
 */

public final class LoopTest extends UnitTest {
    @Test
    public void testLoop() {
	Assembler assem = new Assembler();
	Label restart = assem.newLabel("restart");
	Label end = assem.newLabel("end");

	/* @formatter:off
	 * global: 0(i) for counter, 1(j) for end condition, 2(k) for the result
	 * 
	 * for (i = 0; i < j; i++)
	 *     k = k + i;
	 * 
	 * int i = 0;
	 * int k = 0;
	 * begin:
	 * k = k + i;
	 * if (i < j) {
	 *   i = i + 1;
	 *   goto restart;
	 * }
	 * end:
	 * print k
	 * @formatter:on
	 */
	// 1. initialization
	assem.defineDataSize(3);
	int i = 0, i_val = 0;
	assem.gen("iconst", i_val);
	assem.gen("gstore", i); // i = 0;
	int j = 1, j_val = 101;
	assem.gen("iconst", j_val);
	assem.gen("gstore", j); // j = 101;
	int k = 2, k_val = 0;
	assem.gen("iconst", k_val);
	assem.gen("gstore", k); // k = 0;

	// 2. end condition
	assem.setLabel(restart);
	assem.gen("gload", i);
	assem.gen("gload", j);
	assem.gen("ieq");       // i == j ?
	assem.gen("brt", end);  // goto end

	// 3. loop body
	assem.gen("gload", k);  // load k
	assem.gen("gload", i);  // load i
	assem.gen("iadd");      // k + i
	assem.gen("gstore", k);

	// 4. increase counter
	assem.gen("gload", i);
	assem.gen("iconst", 1); // 1
	assem.gen("iadd");      // i + 1
	assem.gen("gstore", i); // save i

	// 5. restart the loop
	assem.gen("br", restart);
	assem.setLabel(end);
	assem.gen("gload", k);
	// assem.gen("print");
	assem.gen("halt");
	assem.check();

	Disassembler disasm = new Disassembler(assem);
	disasm.disassemble();
	Interpreter vm = new Interpreter(assem);
	// vm.setTrace(true);
	Object retVal = vm.exec();
	assertEquals(retVal, 5050);
    }
}
